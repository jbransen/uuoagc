import System.Environment
import System.FilePath
import ParseLib.Abstract

import Lexer
import Parser
import Compile
import SSM

start :: Parser s a -> [s] -> a
start p = fst . head . filter (null . snd) . parse p

main :: IO ()
main = do
         -- get command line arguments
         args  <- getArgs
         -- compute a list of input an output files
         files <- case args of
                    []  ->  do
                              putStrLn "no argument given; assuming example.cs"
                              return [("example.cs", "example.ssm")]
                    xs  ->  return (map (\ f -> (f, addExtension (dropExtension f) "ssm")) xs)
         -- translate each of the files
         mapM_ processFile files

-- processFile compiles one file; it take the name of the input
-- file and the name of the output file as arguments
processFile :: (FilePath, FilePath) -> IO ()
processFile (infile, outfile) =
  do
    xs <- readFile infile
    let ret = process xs
    writeFile outfile ret
    putStrLn (outfile ++ " written")
    putStrLn ret
  where process = formatCode 
                . generateCode
                . start (pClass <* eof)
                . start lexicalScanner
