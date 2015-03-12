module Main where

import ParseLib.Abstract
import Criterion.Main

import CompileI hiding (generateCode)
import CompileI_Lazy
import Lexer
import Parser
import SSM

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
  -- force some evaluation
  mapM_ (print . length . generateCode) (pinit : prest)
  let bi = bench "initial" $ nf generateCode pinit
  defaultMain $
    bi : [ bench name $ nf (\(p1,p2) -> (generateCode p1, generateCode p2)) (pinit, pother)
         | ((name, _), pother) <- zip (snd tests) prest  ]
