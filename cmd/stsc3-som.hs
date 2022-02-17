import System.Environment {- base -}

import qualified Language.Smalltalk.Som as Som {- stsc3 -}

import qualified Interpreter.Som.Repl {- stsc3-som -}

help :: [String]
help =
    ["stsc3-som command [arguments]"
    ," repl"
    ," run class arguments..."
    ]

main :: IO ()
main = do
  somDirectory <- Som.somSystemClassPath
  a <- getArgs
  case a of
    ["repl"] -> Interpreter.Som.Repl.replMain somDirectory
    "run":cl:arg -> Interpreter.Som.Repl.loadAndRunClass somDirectory cl arg
    _ -> putStrLn (unlines help)
