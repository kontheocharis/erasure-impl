module Pretty (prettyTm, showTm0, displayMetas) where

import Common
import Control.Monad
import Data.IORef
import qualified Data.IntMap.Strict as IM
import {-# SOURCE #-} Evaluation
import Metacontext
import Syntax
import Text.Printf

--------------------------------------------------------------------------------

fresh :: [Name] -> Name -> Name
fresh ns "_" = "_"
fresh ns x
  | elem x ns = fresh ns (x ++ "'")
  | otherwise = x

-- printing precedences
atomp = 3 :: Int -- U, var

appp = 2 :: Int -- application

pip = 1 :: Int -- pi

letp = 0 :: Int -- let, lambda

-- Wrap in parens if expression precedence is lower than
-- enclosing expression precedence.
par :: Int -> Int -> ShowS -> ShowS
par p p' = showParen (p' < p)

prettyTm :: Int -> [Name] -> Tm -> ShowS
prettyTm prec = go prec
  where
    bracket :: ShowS -> ShowS
    bracket ss = ('{' :) . ss . ('}' :)

    mode :: Mode -> String
    mode q = (show q ++ " ")

    piBind ns x q Expl a = showParen True ((mode q ++) . (x ++) . (" : " ++) . go letp ns a)
    piBind ns x q Impl a = bracket ((mode q ++) . (x ++) . (" : " ++) . go letp ns a)

    lamBind x Impl = bracket (x ++)
    lamBind x Expl = (x ++)

    goBDS :: Int -> [Name] -> MetaVar -> [BD] -> ShowS
    goBDS p ns m bds = case (ns, bds) of
      ([], []) -> (("?" ++ show m) ++)
      (ns :> n, bds :> Bound _) -> par p appp $ goBDS appp ns m bds . (' ' :) . (n ++)
      (ns :> n, bds :> Defined) -> goBDS appp ns m bds
      _ -> error "impossible"

    go :: Int -> [Name] -> Tm -> ShowS
    go p ns = \case
      Var (Ix x) _ -> ((ns !! x) ++)
      App t u _ Expl -> par p appp $ go appp ns t . (' ' :) . go atomp ns u
      App t u _ Impl -> par p appp $ go appp ns t . (' ' :) . bracket (go letp ns u)
      Lam (fresh ns -> x) q i t -> par p letp $ ("λ " ++) . lamBind x i . goLam (ns :> x) t
        where
          goLam ns (Lam (fresh ns -> x) q i t) =
            (' ' :) . lamBind x i . goLam (ns :> x) t
          goLam ns t =
            (". " ++) . go letp ns t
      U -> ("U" ++)
      Pi "_" Omega Expl a b -> par p pip $ go appp ns a . (" → " ++) . go pip (ns :> "_") b
      Pi (fresh ns -> x) q i a b -> par p pip $ piBind ns x q i a . goPi (ns :> x) b
        where
          goPi ns (Pi (fresh ns -> x) q i a b)
            | x /= "_" = piBind ns x q i a . goPi (ns :> x) b
          goPi ns b = (" → " ++) . go pip ns b
      Let (fresh ns -> x) q a t u ->
        par p letp $
          ("let " ++)
            . (mode q ++)
            . (x ++)
            . (" : " ++)
            . go letp ns a
            . ("\n  = " ++)
            . go letp ns t
            . (";\n\n" ++)
            . go letp (ns :> x) u
      Meta m _ -> (("?" ++ show m) ++)
      InsertedMeta m bds -> goBDS p ns m bds
      Up t -> ("↑ " ++) . go atomp ns t
      Down t -> ("↓ " ++) . go atomp ns t

showTm0 :: Tm -> String
showTm0 t = prettyTm 0 [] t []

displayMetas :: IO ()
displayMetas = do
  ms <- readIORef mcxt
  forM_ (IM.toList ms) $ \(m, e) -> case e of
    Unsolved q -> printf "let %s ?%s = ?;\n" (show q) (show m)
    Solved q v -> printf "let %s ?%s = %s;\n" (show q) (show m) (showTm0 $ quote 0 v)
  putStrLn ""
