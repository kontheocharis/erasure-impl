module Unification (unify) where

import Common
import Control.Exception
import Data.IORef
import qualified Data.IntMap as IM
import Errors
import Evaluation
import Metacontext
import Syntax
import Value

-- Unification
--------------------------------------------------------------------------------

-- | partial renaming from Γ to Δ
data PartialRenaming = PRen
  { -- | size of Γ
    dom :: Lvl,
    -- | size of Δ
    cod :: Lvl,
    -- | mapping from Δ vars to Γ vars
    ren :: IM.IntMap (Lvl, VarMode)
  }

-- | Lifting a partial renaming over an extra bound variable.
--   Given (σ : PRen Γ Δ), (lift σ : PRen (Γ, x : A[σ]) (Δ, x : A))
lift :: VarMode -> PartialRenaming -> PartialRenaming
lift q (PRen dom cod ren) =
  PRen (dom + 1) (cod + 1) (IM.insert (unLvl cod) (dom, q) ren)

-- | @invert : (Γ : Cxt) → (spine : Sub Δ Γ) → PRen Γ Δ@
invert :: Lvl -> Mode -> Spine -> IO PartialRenaming
invert gamma q sp = do
  let go :: Spine -> IO (Lvl, IM.IntMap (Lvl, VarMode))
      go [] = pure (0, mempty)
      go (sp :> (t, _, _)) = do
        (dom, ren) <- go sp
        case force t of
          VVar (Lvl x) q' | IM.notMember x ren -> case invertVarMode q' q of
            Just q'inv -> pure (dom + 1, IM.insert x (dom, q'inv) ren)
            Nothing -> throwIO UnifyError
          _ -> throwIO UnifyError

  (dom, ren) <- go sp
  pure $ PRen dom gamma ren

-- | Perform the partial renaming on rhs, while also checking for "m" occurrences.
rename :: MetaVar -> PartialRenaming -> Val -> IO Tm
rename m pren v = go pren v
  where
    goSp :: PartialRenaming -> Tm -> Spine -> IO Tm
    goSp pren t [] = pure t
    goSp pren t (sp :> (u, q, i)) = App <$> goSp pren t sp <*> go pren u <*> pure q <*> pure i

    go :: PartialRenaming -> Val -> IO Tm
    go pren t = case force t of
      VFlex m' q sp
        | m == m' -> throwIO UnifyError -- occurs check
        | otherwise -> goSp pren (wrapMode q (Meta m')) sp
      VRigid (Lvl x) q sp -> case IM.lookup x (ren pren) of
        Nothing -> throwIO UnifyError -- scope error ("escaping variable" error)
        Just (x', q') -> goSp pren (wrapMode (substVarMode q q') (Var (lvl2Ix (dom pren) x'))) sp
      VLam x q i t -> Lam x q i <$> go (lift (AtMode q) pren) (t $$ VVar (cod pren) (AtMode q))
      VPi iu x q i a b -> wrapIsUpped iu <$> (Pi x q i <$> go pren a <*> go (lift (AtMode Zero) pren) (b $$ VVar (cod pren) (AtMode Zero)))
      VU iu -> pure $ wrapIsUpped iu U

-- | Wrap a term in lambdas. We need an extra list of Icit-s to
--   match the type of the to-be-solved meta.
lams :: [(Mode, Icit)] -> Tm -> Tm
lams = go (0 :: Int)
  where
    go x [] t = t
    go x ((q, i) : is) t = Lam ("x" ++ show (x + 1)) q i $ go (x + 1) is t

--       Γ      i        ?α         sp   =? rhs
solve :: Mode -> Lvl -> VarMode -> MetaVar -> Spine -> Val -> IO ()
solve lq gamma Upped m sp rhs = solve lq gamma (AtMode Zero) m sp (coe Downward rhs)
solve lq gamma Downed m sp rhs = solve lq gamma (AtMode Omega) m sp (coe Upward rhs) -- this will lead to the case below
solve Zero gamma (AtMode Omega) m sp rhs = do
  throwIO MetaSolutionTooWeak -- @@TODO: can try check/prune RHS? Or otherwise promote metas
solve lq gamma (AtMode q) m sp rhs = do
  pren <- invert gamma q sp
  rhs <- rename m pren rhs
  let solution = eval [] $ lams (reverse $ map (\(_, q, i) -> (q, i)) sp) rhs
  modifyIORef' mcxt $ IM.insert (unMetaVar m) (Solved q solution)

unifySp :: Mode -> Lvl -> Spine -> Spine -> IO ()
unifySp lq l sp sp' = case (sp, sp') of
  ([], []) -> pure ()
  -- Note: we don't have to compare Icit-s, since we know from the recursive
  -- call that sp and sp' have the same type.
  (sp :> (t, q, _), sp' :> (t', q', _))
    | q == q' ->
        unifySp lq l sp sp' >> unify (mult lq q) l t t'
  _ -> throwIO UnifyError -- rigid mismatch error

unify :: Mode -> Lvl -> Val -> Val -> IO ()
unify lq l t u = case (force t, force u) of
  (VLam _ q _ t, VLam _ q' _ t') -> unify lq (l + 1) (t $$ VVar l (AtMode q)) (t' $$ VVar l (AtMode q'))
  (t, VLam _ q i t') -> unify lq (l + 1) (vApp t (VVar l (AtMode q)) q i) (t' $$ VVar l (AtMode q))
  (VLam _ q i t, t') -> unify lq (l + 1) (t $$ VVar l (AtMode q)) (vApp t' (VVar l (AtMode q)) q i)
  (VU _, VU _) -> pure ()
  (VPi _ x q i a b, VPi _ x' q' i' a' b') | q == q' && i == i' -> unify Zero l a a' >> unify Zero (l + 1) (b $$ VVar l (AtMode Zero)) (b' $$ VVar l (AtMode Zero))
  (VRigid x _ sp, VRigid x' _ sp') | x == x' -> unifySp lq l sp sp'
  (VFlex m _ sp, VFlex m' _ sp') | m == m' -> unifySp lq l sp sp'
  (VFlex m q sp, t') -> solve lq l q m sp t'
  (t, VFlex m' q sp') -> solve lq l q m' sp' t
  _ -> throwIO UnifyError -- rigid mismatch error
