module Elaboration (check, infer) where

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

freshMeta :: Cxt -> IO Tm
freshMeta cxt = do
  m <- readIORef nextMeta
  writeIORef nextMeta (m + 1)
  modifyIORef' mcxt $ IM.insert m Unsolved
  pure $ InsertedMeta (MetaVar m) (bds cxt)

unifyCatch :: Cxt -> Val -> Val -> IO ()
unifyCatch cxt t t' =
  unify (lvl cxt) t t'
    `catch` \UnifyError ->
      throwIO $ Error cxt $ CantUnify (quote (lvl cxt) t) (quote (lvl cxt) t')

-- | Insert fresh implicit applications.
insert' :: Cxt -> IO (Tm, VTy) -> IO (Tm, VTy)
insert' cxt act = go =<< act
  where
    go (t, va) = case force va of
      VPi x q Impl a b -> do
        m <- freshMeta cxt
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
            m <- freshMeta cxt
            let mv = eval (env cxt) m
            go (App t m q Impl, b $$ mv)
      _ ->
        throwIO $ Error cxt $ NoNamedImplicitArg name

-- Mode given as argument
checkIn :: Cxt -> Mode -> P.Tm -> VTy -> IO Tm
checkIn cxt Zero t a = Down <$> check (enter cxt Zero) t a
checkIn cxt Omega t a = check cxt t a

-- Mode ω
check :: Cxt -> P.Tm -> VTy -> IO Tm
check cxt t a = case (t, force a) of
  (P.SrcPos pos t, a) ->
    check (cxt {pos = pos}) t a
  -- If the icitness of the lambda matches the Pi type, check as usual
  (P.Lam x i t, VPi x' q' i' a b) | either (\x -> x == x' && i' == Impl) (== i') i -> do
    Lam x q' i' <$> check (bind cxt x q' a) t (b $$ VVar (lvl cxt) (diffVarMode q' Zero))

  -- Otherwise if Pi is implicit, insert a new implicit lambda
  (t, VPi x q Impl a b) -> do
    Lam x q Impl <$> check (newBinder cxt x q a) t (b $$ VVar (lvl cxt) (diffVarMode q Zero))
  (P.Let x q a t u, a') -> do
    a <- checkIn cxt Zero a VU
    let ~va = eval (env cxt) a
    t <- check cxt t va
    let ~vt = eval (env cxt) t
    u <- check (define cxt x q vt va) u a'
    pure (Let x q a t u)
  (P.Hole, a) ->
    freshMeta cxt
  (t, expected) -> do
    (t, inferred) <- insert cxt $ infer cxt t
    unifyCatch cxt expected inferred
    pure t

-- Mode ω
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
              (Zero, Zero) -> pure (Up (Var ix q), a)
          | otherwise = go (ix + 1) types
        go ix [] =
          throwIO $ Error cxt $ NameNotInScope x

    go 0 (types cxt)
  P.Lam x (Right i) t -> do
    let q = Omega
    a <- eval (env cxt) <$> freshMeta cxt
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
        a <- eval (env cxt) <$> freshMeta cxt
        b <- Closure (env cxt) <$> freshMeta (bind cxt "x" q a)
        unifyCatch cxt tty (VPi "x" q i a b)
        pure (q, a, b)

    u <- checkIn cxt q u a
    pure (App t u q i, b $$ eval (env cxt) u)
  P.U ->
    pure (U, VU)
  P.Pi x q i a b -> do
    a <- check cxt a VU
    b <- check (bind cxt x Zero (eval (env cxt) a)) b VU
    pure (Pi x q i a b, VU)
  P.Let x q a t u -> do
    a <- checkIn cxt Zero a VU
    let ~va = eval (env cxt) a
    t <- check cxt t va
    let ~vt = eval (env cxt) t
    (u, b) <- infer (define cxt x q vt va) u
    pure (Let x q a t u, b)
  P.Hole -> do
    a <- eval (env cxt) <$> freshMeta cxt
    t <- freshMeta cxt
    pure (t, a)
