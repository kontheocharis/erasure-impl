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
    ren :: IM.IntMap (Lvl, Mode)
  }

-- | Lifting a partial renaming over an extra bound variable.
--   Given (σ : PRen Γ Δ), (lift σ : PRen (Γ, x {i}: A[σ]) (Δ, x {i}: A))
lift :: Mode -> PartialRenaming -> PartialRenaming
lift q (PRen dom cod ren) =
  PRen (dom + 1) (cod + 1) (IM.insert (unLvl cod) (dom, q) ren)

-- | @invert : # ∈ Δ → (Γ : Cxt) → (spine : Sub Δ Γ) → PRen Γ Δ@
invert :: Mode -> Lvl -> Mode -> [Mode] -> Spine -> IO PartialRenaming
invert lq gamma q modes sp = do
  let go :: Spine -> [Mode] -> IO (Lvl, IM.IntMap (Lvl, Mode))
      go [] [] = pure (0, mempty)
      go (sp :> (t, _, _)) (modes :> mq) = do
        (dom, ren) <- go sp modes
        case force t of
          VVar (Lvl x) q'
            | IM.notMember x ren ->
                let ok = (dom + 1, IM.insert x (dom, q') ren)
                 in if q == Omega && lq == Zero
                      then
                        -- Here we basically check if:
                        -- The meta was created in mode Omega, we are in mode Zero, and we
                        -- use a relevant variable where an irrelevant one is expected.
                        -- In this case the invert is invalid
                        if q' == Omega && mq == Zero
                          then throwIO MetaSolutionTooWeak
                          else pure ok
                      else pure ok
          _ -> throwIO UnifyError
      go _ _ = pure (0, mempty) -- we might have more applications than what the meta expects
  (dom, ren) <- go sp modes
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
        | otherwise -> goSp pren (Meta m' q) sp
      VRigid (Lvl x) q sp -> case IM.lookup x (ren pren) of
        Nothing -> throwIO UnifyError -- scope error ("escaping variable" error)
        Just (x', q') -> goSp pren (Var (lvl2Ix (dom pren) x') q') sp
      VLam x q i t -> Lam x q i <$> go (lift q pren) (t $$ VVar (cod pren) q)
      VPi x q i a b -> Pi x q i <$> go pren a <*> go (lift Zero pren) (b $$ VVar (cod pren) Zero)
      VU -> pure U

-- | Wrap a term in lambdas. We need an extra list of Icit-s to
--   match the type of the to-be-solved meta.
lams :: [(Mode, Icit)] -> Tm -> Tm
lams = go (0 :: Int)
  where
    go x [] t = t
    go x ((q, i) : is) t = Lam ("x" ++ show (x + 1)) q i $ go (x + 1) is t

--       #∈Γ     Γ      mode(?a) ?α         sp   =? rhs
solve :: Mode -> Lvl -> Mode -> MetaVar -> Spine -> Val -> IO ()
solve Zero gamma Omega m sp rhs = do
  throwIO MetaSolutionTooWeak -- @@TODO: can try check/prune RHS? Or otherwise promote metas
solve lq gamma q m sp rhs = do
  let modes = getMetaModes m
  pren <- invert lq gamma q modes sp
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
  (VLam _ q _ t, VLam _ q' _ t') -> unify lq (l + 1) (t $$ VVar l q) (t' $$ VVar l q')
  (t, VLam _ q i t') -> unify lq (l + 1) (vApp t (VVar l q) q i) (t' $$ VVar l q)
  (VLam _ q i t, t') -> unify lq (l + 1) (t $$ VVar l q) (vApp t' (VVar l q) q i)
  (VU, VU) -> pure ()
  (VPi x q i a b, VPi x' q' i' a' b') | q == q' && i == i' -> unify Zero l a a' >> unify Zero (l + 1) (b $$ VVar l Zero) (b' $$ VVar l Zero)
  (VRigid x _ sp, VRigid x' _ sp') | x == x' -> unifySp lq l sp sp'
  (VFlex m _ sp, VFlex m' _ sp') | m == m' -> unifySp lq l sp sp'
  (VFlex m q sp, t') -> solve lq l q m sp t'
  (t, VFlex m' q sp') -> solve lq l q m' sp' t
  _ -> throwIO UnifyError -- rigid mismatch error
