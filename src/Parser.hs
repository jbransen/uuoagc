{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
module Parser (parseAG, parseHOExpr) where

import Data
import IncrData
import Data.Char (isSpace, isAlphaNum, isUpper)
import Data.List (isInfixOf)
import Text.ParserCombinators.UU hiding (Alternative, Const)
import Text.ParserCombinators.UU.BasicInstances
import Text.ParserCombinators.UU.Utils
import Debug.Trace
import qualified Control.Exception as Exc
import System.IO.Unsafe (unsafePerformIO)

-- OAG parsing
parseAG :: FilePath -> IO AG
parseAG path = do
  contents <- readFile path
  return $ runParser path pAG contents

pAG :: Parser AG
pAG = AG <$  pSpace
         <*> pListSep_ng pSpace pNonterminal
         <*  pSpace
         <*> pCodeblock

pCodeblock :: Parser String
pCodeblock =    pToken "-- Haskell code"
             *> pMunch (const True)
             <|> pReturn ""

pNonterminal :: Parser Nonterminal
pNonterminal = Nonterminal <$  pToken "nonterminal"
                           <*  pSpace
                           <*> pName
                           <*> return Nothing
                           <*  pSpace
                           <*> pListSep_ng pSpace pVisit
                           <*  pSpace
                           <*> pListSep_ng pSpace pAlternative
               <|> (\t n v a -> Nonterminal n (Just t) v a)
                           <$  pToken "list"
                           <*  pSpace
                           <*> pType
                           <*  pSpace
                           <*> pName
                           <*  pSpace
                           <*> pListSep_ng pSpace pVisit
                           <*  pSpace
                           <*> pListSep_ng pSpace pAlternative

pVisit :: Parser Visit
pVisit = Visit <$  pToken "visit"
               <*  pSpace
               <*> pIntegerRaw
               <*  pSpace
               <*> pListSep_ng pSpace pAttribute

pAttribute :: Parser Attribute
pAttribute = ((Inherited <$ pToken "inh") <|> 
              (Synthesized <$ pToken "syn"))
                    <*  pSpace
                    <*> pName
                    <*  pSpace
                    <*  pToken "::"
                    <*> pType             

pAlternative :: Parser Alternative
pAlternative = Alternative <$  pToken "alternative"
                           <*  pSpace
                           <*> pName
                           <*  pSpace
                           <*> pListSep_ng pSpace pChild
                           <*  pSpace
                           <*> pListSep_ng pSpace pSchedule

pChild :: Parser Child
pChild = Child <$  pToken "child"
               <*  pSpace
               <*> pName
               <*  pSpace
               <*  pToken "::"
               <*> pType

pSchedule :: Parser Schedule
pSchedule = Schedule <$  pToken "visit"
                     <*  pSpace
                     <*> pIntegerRaw
                     <*  pSpace
                     <*> pListSep_ng pSpace pStep

pStep :: Parser Step
pStep = (ChildVisit    <$  pToken "childvisit"
                       <*  pSpace
                       <*> pName)
        <|>  (HoChild  <$> pChild
                       <*  pSpace
                       <*  pSym '='
                       <*> pExpression)
        <|>  ((SynDecl <$  pToken "lhs")
        <|>   (LocDecl <$  pToken "loc")
        <<|>  (InhDecl <$> pName))
                       <*  pSpace
                       <*  pSym '.'
                       <*  pSpace
                       <*> pName
                       <*  pSpace
                       <*  pSym '='
                       <*> pExpression

pExpression :: Parser Expression
pExpression = Expression <$ pSpace <*> pMunch (/='\n')

pType :: Parser Type
pType = Primitive  <$  pSpace
                   <*  pSym '{'
                   <*> pMunch (/='}')
                   <*  pSym '}'
        <|> NTType <$  pSpace
                   <*> pName

pName :: Parser String
pName = pMunch (\x -> isAlphaNum x || x == '_')

pSpace :: Parser String
pSpace = pMunch isSpace <|> pToken "--" *> pMunch (/='\n') <* pSym '\n'

-- HOExpr parsing
pCons :: Parser String
pCons = (:) <$> pLetter <*> pMunch (\x -> isAlphaNum x || x `elem` "_.")
        <<|> "Nil" <$ pToken "[]"
        <<|> "Cons" <$ pToken "(:)"

pMunch1 :: Char -> (Char -> Bool) -> Parser String
pMunch1 a f = (:) <$> pSatisfy f (Insertion "" a 5) <*> pMunch f

pHOExprBase :: Parser HOExpr
pHOExprBase =      Attr    <$ pSym '@' <*> pName <* pSym '.' <*> pName
              <|>  Attr "" <$ pSym '@' <*> pName <* noPeriod
              <<|> Constr  <$> pCons {- <* noPeriod -} <*> pList_ng pHOExpr
              <<|> pSym '(' *> (
                  -- Prefix operator
                  (\o -> Constr ("(" ++ o ++ ")"))
                     <$> pMunch1 '*' (\x -> not $ isAlphaNum x || isSpace x || x == ')') <* pSym ')'
                     <*>  pList_ng pHOExpr
                <<|> -- Expression between parentheses
                     pHOExpr <* pMunch isSpace <* pSym ')')
              <<|> Const   <$> pMunch1 '0' (\x -> not (isSpace x) && x `notElem` "[,]:")
              <<|> pSym '[' *> pHOList1
              where
                noPeriod = pSatisfy (/= '.') (Insertion "" ' ' 5)
                pHOList1 :: Parser HOExpr
                pHOList1 = (\h t -> Constr "Cons" [h, t]) <$> pHOExpr <*> pHOList 
                pHOList :: Parser HOExpr
                pHOList = pMunch isSpace *>
                          (     Constr "Nil" [] <$  pSym ']'
                           <<|> (\h t -> Constr "Cons" [h, t])
                                <$ pSym ',' <*> pHOExpr <*> pHOList )

pHOExpr :: Parser HOExpr
pHOExpr = pMunch isSpace *>
          (    IfThenElse <$ pToken "if" <*> pHOExpr
                          <* pMunch isSpace <* pToken "then" <*> pHOExpr
                          <* pMunch isSpace <* pToken "else" <*> pHOExpr
          <<|> ((\a1 f a2 -> Constr ("(" ++ f ++ ")") [a1,a2])
               <$> pHOExprBase
               <*  pMunch isSpace
               <*> pMunch1 '+' (`elem` "+-*/^!")
               <*> pHOExpr
           <|> pHOExprBase)
          )

parseHOExpr :: String -> HOExpr
parseHOExpr s = case unsafeCleanup $ f s of
  Just a  -> a
  Nothing -> trace ("Warning, could not parse " ++ show s) (Const "noparse")
  where
    f s | "case" `isInfixOf` s = error "Case is not supported"
        | otherwise = runParser s (pHOExpr <* pMunch isSpace) (s ++ " ")

-- Super ugly, but quick hack because I don't want to write a parser
-- that can handle arbitrary Haskell expressions mixed with attributes
{-# NOINLINE unsafeCleanup #-}
unsafeCleanup :: a -> Maybe a
unsafeCleanup x = unsafePerformIO $ Exc.catch (x `seq` return (Just x)) handler
    where
    handler exc = return Nothing  `const`  (exc :: Exc.ErrorCall)
