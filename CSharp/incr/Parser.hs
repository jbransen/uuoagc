module Parser where

import ParseLib.Abstract hiding (braced, bracketed, parenthesised)
import Lexer
import CompileI

parenthesised p = pack (symbol POpen) p (symbol PClose)
bracketed     p = pack (symbol SOpen) p (symbol SClose)
braced        p = pack (symbol COpen) p (symbol CClose)

pExprSimple :: Parser Token Expr
pExprSimple =  ExprConst <$> pConst
           <|> ExprVar   <$> sName
           <|> ExprFun   <$> sName
                         <*> parenthesised (option (listOf pExpr (symbol Comma)) [])
           <|> parenthesised pExpr

pConst :: Parser Token Const
pConst = f <$> sConst where
  f (TConstInt i)  = ConstInt i
  f (TConstBool b) = ConstBool b
  f (TConstChar c) = ConstChar c

-- Operator precedence, see http://msdn.microsoft.com/en-us/library/aa691323.aspx
pExpr :: Parser Token Expr
pExpr = foldr gen pExprSimple [
  ["="],
  ["||"],
  ["&&"],
  ["^"],
  ["==", "!="],
  ["<=", "<", ">=", ">"],
  ["+", "-"],                           
  ["*", "/", "%"]]

gen :: [String] -> Parser Token Expr -> Parser Token Expr
gen ops p = chainl p (choice (map f ops))
  where f :: String -> Parser Token (Expr -> Expr -> Expr)
        f o = ExprOper o <$ symbol (Operator o)

pMember :: Parser Token Member
pMember =   MemberD <$> pDeclSemi
        <|> pMeth

pStatDecl :: Parser Token Stat
pStatDecl =   pStat
          <|> StatDecl <$> pDeclSemi

pStat :: Parser Token Stat
pStat =  StatExpr
         <$> pExpr 
         <*  sSemi
     <|> StatIf
         <$  symbol KeyIf
         <*> parenthesised pExpr
         <*> pStat
         <*> option ((\_ x -> x) <$> symbol KeyElse <*> pStat) (StatBlock [])
     <|> StatWhile
         <$  symbol KeyWhile
         <*> parenthesised pExpr
         <*> pStat
     <|> StatFor
         <$  symbol KeyFor
         <*  symbol POpen
         <*> pDecl
         <*  symbol Semicolon
         <*> pExpr
         <*  symbol Semicolon
         <*> pExpr
         <*  symbol PClose
         <*> pStat
     <|> StatReturn
         <$  symbol KeyReturn
         <*> pExpr
         <*  sSemi
     <|> pBlock
     
     
pBlock :: Parser Token Stat
pBlock  =  StatBlock
           <$> braced ( many pStatDecl )



pMeth :: Parser Token Member
pMeth =  MemberM
         <$> (   pType 
             <|> const TypeVoid <$> symbol KeyVoid
             )
         <*> sName
         <*> parenthesised (option (listOf pDecl
                                           (symbol Comma)
                                   )
                                   []
                           )
         <*> pBlock
         
pType0 :: Parser Token Type
pType0 =  TypePrim <$> sStdType
      <|> TypeObj  <$> sName

pType :: Parser Token Type
pType = foldr (const TypeArray) 
        <$> pType0 
        <*> many (bracketed (succeed ()))


pDecl :: Parser Token Decl 
pDecl =     DeclC <$> pType
                  <*> sName
        <|> DeclInit <$> pType
                     <*> sName
                     <*  symbol (Operator "=")
                     <*> pExpr
        
pDeclSemi :: Parser Token Decl 
pDeclSemi = const <$> pDecl <*> sSemi

pClass :: Parser Token Class
pClass = ClassC
        <$  symbol KeyClass
        <*> sName
        <*> braced ( many pMember )
