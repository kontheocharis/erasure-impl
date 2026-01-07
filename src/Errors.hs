module Errors where

import Common
import Control.Exception
import Cxt
import Syntax
import Text.Printf

--------------------------------------------------------------------------------

data UnifyError = UnifyError
  deriving (Show, Exception)

data ElabError
  = NameNotInScope Name
  | CantUnify Tm Tm
  | InferNamedLam
  | NoNamedImplicitArg Name
  | IcitMismatch Icit Icit
  | InsufficientMode
  deriving (Show, Exception)

data Error = Error Cxt ElabError
  deriving (Show, Exception)

displayError :: String -> Error -> IO ()
displayError file (Error cxt e) = do
  let SourcePos path (unPos -> linum) (unPos -> colnum) = pos cxt
      lnum = show linum
      lpad = map (const ' ') lnum
      msg = case e of
        NameNotInScope x ->
          "Name not in scope: " ++ x
        CantUnify t t' ->
          ( "Cannot unify expected type\n\n"
              ++ "  "
              ++ showTm cxt t
              ++ "\n\n"
              ++ "with inferred type\n\n"
              ++ "  "
              ++ showTm cxt t'
          )
        InferNamedLam ->
          "Cannot infer type for lambda with named argument"
        NoNamedImplicitArg name ->
          "No named implicit argument with name " ++ name
        IcitMismatch i i' ->
          printf
            ("Function icitness mismatch: expected %s, got %s.")
            (show i)
            (show i')
        InsufficientMode ->
          "Term is valid in mode 0 but need mode ω"

  printf "%s:%d:%d:\n" path linum colnum
  printf "%s |\n" lpad
  printf "%s | %s\n" lnum (lines file !! (linum - 1))
  printf "%s | %s\n" lpad (replicate (colnum - 1) ' ' ++ "^")
  printf "%s\n" msg
