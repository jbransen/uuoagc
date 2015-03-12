module Lexer where

import Data.Char
import Control.Monad
import ParseLib.Abstract

data Token = POpen    | PClose        -- parentheses     ()
           | SOpen    | SClose        -- square brackets []
           | COpen    | CClose        -- curly braces    {}
           | Comma    | Semicolon
           | KeyIf    | KeyElse  
           | KeyWhile | KeyReturn
           | KeyFor
           | KeyTry   | KeyCatch
           | KeyClass | KeyVoid
           | StdType   String         -- the 8 standard types
           | Operator  String         -- the 15 operators
           | UpperId   String         -- uppercase identifiers
           | LowerId   String         -- lowercase identifiers
           | TConstInt  Int
           | TConstBool Bool
           | TConstChar Char
           deriving (Eq, Show)

keyword :: String -> Parser Char String
keyword []                    = succeed ""
keyword xs@(x:_) | isLetter x = do
                                  ys <- greedy (satisfy isAlphaNum)
                                  guard (xs == ys)
                                  return ys
                 | otherwise  = token xs

greedyChoice :: [Parser s a] -> Parser s a
greedyChoice = foldr (<<|>) empty

terminals :: [(Token, String)]
terminals =
    [( POpen     , "("      )
    ,( PClose    , ")"      )
    ,( SOpen     , "["      )
    ,( SClose    , "]"      )
    ,( COpen     , "{"      )
    ,( CClose    , "}"      )
    ,( Comma     , ","      )
    ,( Semicolon , ";"      )
    ,( KeyIf     , "if"     )
    ,( KeyElse   , "else"   )
    ,( KeyWhile  , "while"  )
    ,( KeyFor    , "for"  )
    ,( KeyReturn , "return" )
    ,( KeyTry    , "try"    )
    ,( KeyCatch  , "catch"  )
    ,( KeyClass  , "class"  )
    ,( KeyVoid   , "void"   )
    ]


lexWhiteSpace :: Parser Char String
lexWhiteSpace = greedy (satisfy isSpace)

lexLowerId :: Parser Char Token
lexLowerId =  (\x xs -> LowerId (x:xs))
          <$> satisfy isLower
          <*> greedy (satisfy isAlphaNum)

lexUpperId :: Parser Char Token
lexUpperId =  (\x xs -> UpperId (x:xs))
          <$> satisfy isUpper
          <*> greedy (satisfy isAlphaNum)

lexConstInt :: Parser Char Token
lexConstInt = (TConstInt . read) <$> greedy1 (satisfy isDigit)

lexConstBool :: Parser Char Token
lexConstBool =     (TConstBool True) <$ token "true"
               <|> (TConstBool False) <$ token "false"

lexConstChar :: Parser Char Token
lexConstChar = TConstChar <$ symbol '\'' <*> anySymbol <* symbol '\''


lexEnum :: (String -> Token) -> [String] -> Parser Char Token
lexEnum f xs = f <$> choice (map keyword xs)

lexTerminal :: Parser Char Token
lexTerminal = choice (map (\ (t,s) -> t <$ keyword s) terminals)

stdTypes :: [String]
stdTypes = ["int", "long", "double", "float",
            "byte", "short", "bool", "char"]

operators :: [String]
operators = ["+", "-", "*", "/", "%", "&&", "||",
             "^", "<=", "<", ">=", ">", "==",
             "!=", "="]


lexToken :: Parser Char Token
lexToken = greedyChoice
             [ lexTerminal
             , lexEnum StdType stdTypes
             , lexEnum Operator operators
             , lexConstInt
             , lexConstBool
             , lexConstChar
             , lexLowerId
             , lexUpperId
             ]

lexicalScanner :: Parser Char [Token]
lexicalScanner = lexWhiteSpace *> greedy (lexToken <* lexWhiteSpace) <* eof


sStdType :: Parser Token String
sStdType = (\(StdType r) -> r) <$> satisfy isStdType
       where isStdType (StdType _) = True
             isStdType _           = False

sName :: Parser Token String
sName =     (\(UpperId r) -> r) <$> sUpperId
        <|> (\(LowerId r) -> r) <$> sLowerId

sUpperId :: Parser Token Token
sUpperId = satisfy isUpperId
       where isUpperId (UpperId _) = True
             isUpperId _           = False

sLowerId :: Parser Token Token
sLowerId = satisfy isLowerId
       where isLowerId (LowerId _) = True
             isLowerId _           = False

sConst :: Parser Token Token
sConst  = satisfy isConst
       where isConst (TConstInt  _) = True
             isConst (TConstBool _) = True
             isConst (TConstChar _) = True            
             isConst _             = False
             
sOperator :: Parser Token Token
sOperator = satisfy isOperator
       where isOperator (Operator _) = True
             isOperator _            = False
             

sSemi :: Parser Token Token
sSemi =  symbol Semicolon

