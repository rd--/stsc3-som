import System.Environment {- base -}

import qualified Music.Theory.Directory {- hmt-base -}

import qualified Interpreter.Som.Eval {- stsc3-som -}
import qualified Interpreter.Som.Primitives.Som as Primitives.Som {- stsc3-som -}
import qualified Interpreter.Som.Primitives.Smalltalk as Primitives.Smalltalk {- stsc3-som -}
import qualified Interpreter.Som.Repl {- stsc3-som -}

help :: [String]
help =
    ["stsc3-som -cp <classpath> command [arguments]"
    ," {som | st } repl"
    ," run class arguments..."
    ]

replOpt :: String -> Interpreter.Som.Eval.EvalOpt
replOpt typ =
  case typ  of
    "som" -> Primitives.Som.somEvalOpt
    "st" -> Primitives.Smalltalk.stEvalOpt
    _ -> error "replOpt?"

main :: IO ()
main = do
  a <- getArgs
  case a of
    ["-cp", cp, typ, "repl"] -> Interpreter.Som.Repl.replInitAndContinue (replOpt typ) (Music.Theory.Directory.path_split cp)
    "-cp":cp:"run":cl:arg -> Interpreter.Som.Repl.loadAndRunClass (replOpt "som") (Music.Theory.Directory.path_split cp) cl arg
    _ -> putStrLn (unlines help)
