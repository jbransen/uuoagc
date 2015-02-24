module Main where

import Data
import Parser (parseAG)
import qualified Compile as Comp
import qualified IncrCompile as CompI
import PrintCode (printCode)
import Text.PrettyPrint (render)
import System.Environment (getArgs)

main :: IO ()
main = do
  args <- getArgs
  case args of
    (file:opts) -> do
      ag <- parseAG file
      generate opts ag
    _      -> do putStrLn "Usage: uuoagc <filename> [options]"
                 putStrLn "   --nodata: don't generate data types"
                 putStrLn "   --incremental: generate incremental evaluation machinery"
                 putStrLn "   --ticks: put tickAG, tickSem and tickEQ functions in source code for analysis (only with incremental)"
                 putStrLn "   --hosupport: build up change representations for ho attributes (only with incremental)"

generate :: [String] -> AG -> IO ()
generate opts ag@(AG _ litCode) = putStrLn code where
  compile = if "--incremental" `elem` opts
            then CompI.compile
            else Comp.compile
  (prog,prag) = compile opts ag
  doc  = printCode prog
  code = prag ++ "\n" ++ litCode ++ "\n" ++ render doc
