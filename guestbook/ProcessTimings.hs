module Main where

import System.Environment
import Text.CSV

main :: IO ()
main = do
  args <- getArgs
  case args of
   [ifile,ofile] -> processFile ifile ofile
   _      -> putStrLn "Usage: ./ProcessTimings <csvfile> <result>"

processFile :: FilePath -> FilePath -> IO ()
processFile ifile ofile = do
  Right csv <- parseCSVFromFile ifile
  let newCSV = processNums csv
  writeFile ofile (printCSV newCSV)
  putStrLn $ "Result written to " ++ ofile
     
processNums :: CSV -> CSV
processNums (h@["Name","Mean","MeanLB","MeanUB","Stddev","StddevLB","StddevUB"]
            :i@["initial",mean,_,_,_,_,_]:xs) = h : i : map f xs where
  f [name,a,b,c,d,e,f] = [name,show (read a - read mean :: Double), b, c, d, e, f]
  f row = row
