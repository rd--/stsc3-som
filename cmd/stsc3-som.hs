import System.Environment {- base -}

import qualified Language.Smalltalk.Som as Som {- stsc3 -}

import qualified Interpreter.Som.Core {- stsc3-som -}
import qualified Interpreter.Som.Primitives.Som as Primitives.Som {- stsc3-som -}
import qualified Interpreter.Som.Primitives.Smalltalk as Primitives.Smalltalk {- stsc3-som -}
import qualified Interpreter.Som.Repl {- stsc3-som -}

help :: [String]
help =
    ["stsc3-som command [arguments]"
    ," {som | st } repl"
    ," run class arguments..."
    ]

replOpt :: String -> Interpreter.Som.Core.CoreOpt
replOpt typ =
  case typ  of
    "som" -> Primitives.Som.somCoreOpt
    "st" -> Primitives.Smalltalk.stCoreOpt
    _ -> error "replOpt?"

main :: IO ()
main = do
  somDirectory <- Som.somSystemClassPath
  a <- getArgs
  case a of
    [typ, "repl"] -> Interpreter.Som.Repl.replMain (replOpt typ) somDirectory
    "run":cl:arg -> Interpreter.Som.Repl.loadAndRunClass (replOpt "som") somDirectory cl arg
    _ -> putStrLn (unlines help)
