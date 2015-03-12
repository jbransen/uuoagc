module Main where

import ParseLib.Abstract
import Criterion.Main

import CompileI hiding (generateCode, generateCode2)
import CompileI_nonHO
import Lexer
import Parser
import SSM
import Transformations

tests :: (FilePath, [(String, FilePath)])
tests = ("../bigprogram.cs",
         [ ("insert", "../bigprogram2.cs")
         , ("delete", "../bigprogram4.cs")
         , ("while->for", "../bigprogram3.cs") ])

start :: Parser s a -> [s] -> a
start p = fst . head . filter (null . snd) . parse p

parseClass :: String -> Class
parseClass = start (pClass <* eof) . start lexicalScanner

parseMember :: String -> Member
parseMember = start (pMember <* eof) . start lexicalScanner

parseFile :: FilePath -> IO Class
parseFile infile = readFile infile >>= return . parseClass

main :: IO ()
main = do
  pinit <- parseFile $ fst tests
  prest <- mapM (parseFile . snd) $ snd tests
  diffs <- mapM (return . mydiff pinit) prest
  -- force some evaluation
  mapM_ (print . length) diffs
  let bi = bench "initial"  $ nf (fst . generateCode) pinit
  defaultMain $
    bi : [ bench name $ nf (\(p,ch) -> let (res,st) = generateCode p
                                       in  (res,fst $ generateCode2 st df)) (pinit, df)
         | ((name, _), df) <- zip (snd tests) diffs ]
