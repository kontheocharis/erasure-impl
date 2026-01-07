module Elaboration (check, infer, inferIn) where

import Common
import Control.Exception
import Control.Monad
import Cxt
import Data.IORef
import qualified Data.IntMap as IM
import Errors
import Evaluation
import Metacontext
import qualified Presyntax as P
import Syntax
import Unification
import Value

-- Elaboration
--------------------------------------------------------------------------------

freshMeta :: Cxt -> Mode -> IO Tm
freshMeta cxt q = do
  m <- readIORef nextMeta
  writeIORef nextMeta (m + 1)
  let metaMd = case (md cxt, q) of
        (Zero, Omega) -> Zero
        (Omega, Zero) -> Zero
        (Zero, Zero) -> Zero
        (Omega, Omega) -> Omega
  modifyIORef' mcxt $ IM.insert m (Unsolved metaMd)
  pure $ InsertedMeta (MetaVar m) metaMd (bds cxt)

unifyCatch :: Cxt -> Val -> Val -> IO ()
unifyCatch cxt t t' =
  unify (md cxt) (lvl cxt) t t'
    `catch` \e -> throwIO $ Error cxt $ CantUnify (quote (lvl cxt) t) (quote (lvl cxt) t') e

-- | Insert fresh implicit applications.
insert' :: Cxt -> IO (Tm, VTy) -> IO (Tm, VTy)
insert' cxt act = go =<< act
  where
    go (t, va) = case force va of
      VPi x q Impl a b -> do
        m <- freshMeta cxt q
        let mv = eval (env cxt) m
        go (App t m q Impl, b $$ mv)
      va -> pure (t, va)

-- | Insert fresh implicit applications to a term which is not
--   an implicit lambda (i.e. neutral).
insert :: Cxt -> IO (Tm, VTy) -> IO (Tm, VTy)
insert cxt act =
  act >>= \case
    (t@(Lam _ q Impl _), va) -> pure (t, va)
    (t, va) -> insert' cxt (pure (t, va))

-- | Insert fresh implicit applications until we hit a Pi with
--   a particular binder name.
insertUntilName :: Cxt -> Name -> IO (Tm, VTy) -> IO (Tm, VTy)
insertUntilName cxt name act = go =<< act
  where
    go (t, va) = case force va of
      va@(VPi x q Impl a b) -> do
        if x == name
          then
            pure (t, va)
          else do
            m <- freshMeta cxt q
            let mv = eval (env cxt) m
            go (App t m q Impl, b $$ mv)
      _ ->
        throwIO $ Error cxt $ NoNamedImplicitArg name

-- Mode given as argument
--
-- types always in mode 0
checkIn :: Cxt -> Mode -> P.Tm -> VTy -> IO Tm
checkIn cxt Zero t a = check (enter cxt Zero) t a
checkIn cxt Omega t a = check cxt t a

-- Mode ω
--
-- types always in mode 0
check :: Cxt -> P.Tm -> VTy -> IO Tm
check cxt t a = case (t, force a) of
  (P.SrcPos pos t, a) ->
    check (cxt {pos = pos}) t a
  -- If the icitness of the lambda matches the Pi type, check as usual
  (P.Lam x i t, VPi x' q' i' a b) | either (\x -> x == x' && i' == Impl) (== i') i -> do
    Lam x q' i' <$> check (bind cxt x q' a) t (b $$ VVar (lvl cxt) Zero)

  -- Otherwise if Pi is implicit, insert a new implicit lambda
  (t, VPi x q Impl a b) -> do
    Lam x q Impl <$> check (newBinder cxt x q a) t (b $$ VVar (lvl cxt) Zero)
  (P.Let x q a t u, a') -> do
    a <- checkIn cxt Zero a VU
    let ~va = eval (env cxt) a
    t <- checkIn cxt q t va
    let ~vt = eval (env cxt) t
    u <- check (define cxt x q vt va) u a'
    pure (Let x q a t u)
  (P.Hole, a) ->
    freshMeta cxt Omega
  (t, expected) -> do
    (t, inferred) <- insert cxt $ infer cxt t
    unifyCatch cxt expected inferred
    pure t

inferIn :: Cxt -> Mode -> P.Tm -> IO (Tm, VTy)
inferIn cxt Zero t = infer (enter cxt Zero) t
inferIn cxt Omega t = infer cxt t

-- Mode ω
--
-- types always in mode 0
infer :: Cxt -> P.Tm -> IO (Tm, VTy)
infer cxt = \case
  P.SrcPos pos t ->
    infer (cxt {pos = pos}) t
  P.Var x -> do
    let go ix (types :> (x', origin, q, a))
          | x == x' && origin == Source = case (md cxt, q) of
              (Omega, Omega) -> pure (Var ix q, a)
              (Omega, Zero) -> throwIO $ Error cxt $ InsufficientMode
              (Zero, Omega) -> pure (Var ix q, a)
              (Zero, Zero) -> pure (Var ix q, a)
          | otherwise = go (ix + 1) types
        go ix [] =
          throwIO $ Error cxt $ NameNotInScope x

    go 0 (types cxt)
  P.Lam x (Right i) t -> do
    let q = Omega
    a <- eval (env cxt) <$> freshMeta cxt Zero
    let cxt' = bind cxt x q a
    (t, b) <- insert cxt' $ infer cxt' t
    pure (Lam x q i t, VPi x q i a $ closeVal cxt b)
  P.Lam x Left {} t ->
    throwIO $ Error cxt $ InferNamedLam
  P.App t u i -> do
    -- choose implicit insertion
    (i, t, tty) <- case i of
      Left name -> do
        (t, tty) <- insertUntilName cxt name $ infer cxt t
        pure (Impl, t, tty)
      Right Impl -> do
        (t, tty) <- infer cxt t
        pure (Impl, t, tty)
      Right Expl -> do
        (t, tty) <- insert' cxt $ infer cxt t
        pure (Expl, t, tty)

    -- ensure that tty is Pi
    (q, a, b) <- case force tty of
      VPi x q i' a b -> do
        unless (i == i') $
          throwIO $
            Error cxt $
              IcitMismatch i i'
        pure (q, a, b)
      tty -> do
        let q = Omega
        a <- eval (env cxt) <$> freshMeta cxt Zero
        b <- Closure (env cxt) <$> freshMeta (bind cxt "x" q a) Zero
        unifyCatch cxt tty (VPi "x" q i a b)
        pure (q, a, b)

    u <- checkIn cxt q u a
    pure (App t u q i, b $$ eval (env cxt) u)
  P.U -> do
    when (md cxt /= Zero) (throwIO $ Error cxt $ InsufficientMode)
    pure (U, VU)
  P.Pi x q i a b -> do
    when (md cxt /= Zero) (throwIO $ Error cxt $ InsufficientMode)
    a <- checkIn cxt Zero a (VU)
    b <- checkIn (bind cxt x Zero (eval (env cxt) a)) Zero b (VU)
    pure (Pi x q i a b, VU)
  P.Let x q a t u -> do
    a <- checkIn cxt Zero a VU
    let ~va = eval (env cxt) a
    t <- checkIn cxt q t va
    let ~vt = eval (env cxt) t
    (u, b) <- infer (define cxt x q vt va) u
    pure (Let x q a t u, b)
  P.Hole -> do
    a <- eval (env cxt) <$> freshMeta cxt Zero
    t <- freshMeta cxt Omega
    pure (t, a)
