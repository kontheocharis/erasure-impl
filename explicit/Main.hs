module Main where

import Common
import Control.Exception
import Cxt
import Elaboration
import Errors
import Evaluation
import Extraction (extract)
import Metacontext
import Parser
import qualified Presyntax as P
import Pretty
import System.Environment
import System.Exit

--------------------------------------------------------------------------------

helpMsg =
  unlines
    [ "usage: erasure-impl [--help|elab|nf|type]",
      "  --help : display this message",
      "  elab   : read & elaborate expression from stdin",
      "  nf     : read & typecheck expression from stdin, print its normal form and type",
      "  type   : read & typecheck expression from stdin, print its type"
    ]

showHelp = putStrLn helpMsg >> exitFailure

mainWith :: IO [String] -> IO (P.Tm, String) -> IO ()
mainWith getOpt getRaw = do
  let elab m = do
        (t, file) <- getRaw
        inferIn (emptyCxt (initialPos file)) m t
          `catch` \e -> (displayError file e >> exitFailure)

  let parseMode "0" = pure Zero
      parseMode "" = pure Omega
      parseMode _ = showHelp

  reset
  getOpt >>= \case
    ["--help"] -> putStrLn helpMsg
    ['n' : 'f' : optMode] -> do
      q <- parseMode optMode
      (t, a) <- elab q
      putStrLn $ showTm0 $ nf (getMarker q) [] t
      putStrLn "  :"
      putStrLn $ showTm0 $ quote 0 a
    ['t' : 'y' : 'p' : 'e' : optMode] -> do
      q <- parseMode optMode
      (t, a) <- elab q
      putStrLn $ showTm0 $ quote 0 a
    ['e' : 'l' : 'a' : 'b' : optMode] -> do
      q <- parseMode optMode
      (t, a) <- elab q
      displayMetas
      putStrLn $ showTm0 t
    ['e' : 'x' : optMode] -> do
      q <- parseMode optMode
      (t, a) <- elab q
      let e = extract t
      putStrLn $ showCode0 e
    _ -> showHelp

main :: IO ()
main = mainWith getArgs parseStdin

-- | Run main with inputs as function arguments.
main' :: String -> String -> IO ()
main' mode src = mainWith (pure [mode]) ((,src) <$> parseString src)
