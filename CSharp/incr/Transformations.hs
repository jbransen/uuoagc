{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
module Transformations where

import Generics.MultiRec.Base
import Generics.MultiRec.Transformations.Path as TR
import Generics.MultiRec.Transformations.Explicit3

import CompileI as CI

data AST :: * -> * where
  Class :: AST Class
  Const :: AST Const
  Decl :: AST Decl
  Expr :: AST Expr
  Member :: AST Member
  Stat :: AST Stat
  Type :: AST Type

type instance Ixs AST = '[ Class, Const, Decl, Expr, Member, Stat, Type ]

mydiff :: Class -> Class -> [MyInsert AST]
mydiff c1 c2 = map f $ toNiceTransformation $ diff Class c1 c2 where
  f :: NiceInsert AST Class Class -> MyInsert AST
  f (NiceInsert w p r) = MyInsert w (toPath p) r
  
-- This should all be automatically generated
toPath :: TR.Path AST t f -> CI.Path t f
toPath TR.End = CI.End
toPath (PlusL (TagP (ConsP (ProdR (TrvI i (RecP _ m)))))) = ClassClassCP_members $ applyI i PathL_tl $ PathL_hd $ toPath m
toPath (PlusR (PlusR (PlusL (TagP (PlusL (ConsP (ProdL (RecP _ p)))))))) = DeclDeclCP_vtype $ toPath p
toPath (PlusR (PlusR (PlusR (PlusL (TagP r))))) = case r of
  PlusL (ConsP (RecP _ p)) -> ExprExprConstP_const $ toPath p
  PlusR (PlusR (PlusL (ConsP r))) -> case r of
    ProdR (ProdL (RecP _ p)) -> ExprExprOperP_left $ toPath p
    ProdR (ProdR (RecP _ p)) -> ExprExprOperP_right $ toPath p
  PlusR (PlusR (PlusR (ConsP (ProdR (TrvI i (RecP _ p)))))) -> ExprExprFunP_params $ applyI i PathL_tl $ PathL_hd $ toPath p
toPath (PlusR (PlusR (PlusR (PlusR (PlusL (TagP (PlusL (ConsP (RecP _ p))))))))) =
  MemberMemberDP_decl $ toPath p
toPath (PlusR (PlusR (PlusR (PlusR (PlusL (TagP (PlusR (ConsP r)))))))) = case r of
  ProdL (RecP _ p)                          -> MemberMemberMP_rtype $ toPath p
  ProdR (ProdR (ProdL (TrvI i (RecP _ p)))) -> MemberMemberMP_params $ applyI i PathL_tl $ PathL_hd $ toPath p
  ProdR (ProdR (ProdR (RecP _ p)))          -> MemberMemberMP_body $ toPath p
toPath (PlusR (PlusR (PlusR (PlusR (PlusR (PlusL (TagP r))))))) = case r of
  PlusL (ConsP (RecP _ p)) -> StatStatDeclP_decl $ toPath p
  PlusR (PlusL (ConsP (RecP _ p))) -> StatStatExprP_expr $ toPath p
  PlusR (PlusR (PlusL (ConsP r))) -> case r of
    ProdL (RecP _ p) -> StatStatIfP_cond $ toPath p
    ProdR (ProdL (RecP _ p)) -> StatStatIfP_true $ toPath p
    ProdR (ProdR (RecP _ p)) -> StatStatIfP_false $ toPath p
  PlusR (PlusR (PlusR (PlusL (ConsP r)))) -> case r of
    ProdL (RecP _ p) -> StatStatWhileP_cond $ toPath p
    ProdR (RecP _ p) -> StatStatWhileP_body $ toPath p
  PlusR (PlusR (PlusR (PlusR (PlusL (ConsP (RecP _ p)))))) -> StatStatReturnP_expr $ toPath p
  PlusR (PlusR (PlusR (PlusR (PlusR (PlusL (ConsP (TrvI i (RecP _ p)))))))) -> StatStatBlockP_stats $ applyI i PathL_tl $ PathL_hd $ toPath p
  PlusR (PlusR (PlusR (PlusR (PlusR (PlusR (ConsP r)))))) -> case r of
    ProdL               (RecP _ p)   -> StatStatForP_init $ toPath p
    ProdR (ProdL        (RecP _ p))  -> StatStatForP_cond $ toPath p
    ProdR (ProdR (ProdL (RecP _ p))) -> StatStatForP_incr $ toPath p
    ProdR (ProdR (ProdR (RecP _ p))) -> StatStatForP_body $ toPath p

fromPath :: CI.Path t f -> TR.Path AST t f
fromPath CI.End = TR.End

applyI :: Int -> (a -> a) -> a -> a
applyI 0 f = id
applyI n f = f . applyI (n - 1) f

instance HasRef AST top where
  type RefRep AST top r = ReplType r top

  toRef Class (Ref p) = Class_Ref (toPath p)
  toRef Class (InR (L (Tag (C ((:*:) (K f0) (D f1)))))) = ClassClassCR f0 (foldr ListConsR ListNilR $ map (toRef Member . unI) f1)
  
  toRef Const (Ref p) = Const_Ref (toPath p)
  toRef Const (InR (R (L (Tag (L (C (K f0))))))) = ConstConstIntR f0
  toRef Const (InR (R (L (Tag (R (L (C (K f0)))))))) = ConstConstBoolR f0
  toRef Const (InR (R (L (Tag (R (R (C (K f0)))))))) = ConstConstCharR f0
  
  toRef Decl (Ref p) = Decl_Ref (toPath p)
  toRef Decl (InR (R (R (L (Tag (L (C ((:*:) f0 f1))))))))
    = DeclDeclCR undefined (unK f1) -- (error "(toRef Type . unI)" f0)
  toRef Decl (InR (R (R (L (Tag (R (C ((:*:) f0 ((:*:) (K f1) f2)))))))))
    = DeclDeclInitR ((toRef Type . unI) f0) f1 ((toRef Expr . unI) f2)

  toRef Expr (Ref p) = Expr_Ref (toPath p)
  toRef Expr (InR (R (R (R (L (Tag (L (C f0))))))))
    = ExprExprConstR ((toRef Const . unI) f0)
  toRef Expr (InR (R (R (R (L (Tag (R (L (C f0))))))))) = ExprExprVarR (unK f0)
  toRef Expr (InR (R (R (R (L (Tag (R (R (L (C ((:*:) f0 ((:*:) f1 f2))))))))))))
    = ExprExprOperR (unK f0) ((toRef Expr . unI) f1) ((toRef Expr . unI) f2)
  toRef Expr (InR (R (R (R (L (Tag (R (R (R (C ((:*:) f0 (D f1))))))))))))
    = ExprExprFunR (unK f0) (foldr ListConsR ListNilR $ fmap (toRef Expr . unI) f1)

  toRef Member (Ref p) = Member_Ref (toPath p)
  toRef Member (InR (R (R (R (R (L (Tag (L (C (I f0)))))))))) = MemberMemberDR (toRef Decl f0)
  toRef Member (InR (R (R (R (R (L (Tag (R (C ((:*:) (I f0) ((:*:) (K f1) ((:*:) (D f2) (I f3))))))))))))) = MemberMemberMR (toRef Type f0) f1 (foldr ListConsR ListNilR $ map (toRef Decl . unI) f2) (toRef Stat f3)

  toRef Stat (Ref p) = Stat_Ref (toPath p)
  toRef Stat (InR (R (R (R (R (R (L (Tag (L (C f0))))))))))
    = StatStatDeclR ((toRef Decl . unI) f0)
  toRef Stat (InR (R (R (R (R (R (L (Tag (R (L (C f0)))))))))))
    = StatStatExprR ((toRef Expr . unI) f0)
  toRef Stat (InR (R (R (R (R (R (L (Tag (R (R (L (C ((:*:) f0 ((:*:) f1 f2))))))))))))))
    = StatStatIfR ((toRef Expr . unI) f0) ((toRef Stat . unI) f1) ((toRef Stat . unI) f2)
  toRef Stat (InR (R (R (R (R (R (L (Tag (R (R (R (L (C ((:*:) f0 f1))))))))))))))
    = StatStatWhileR ((toRef Expr . unI) f0) ((toRef Stat . unI) f1)
  toRef Stat (InR (R (R (R (R (R (L (Tag (R (R (R (R (L (C f0))))))))))))))
    = StatStatReturnR ((toRef Expr . unI) f0)
  toRef Stat (InR (R (R (R (R (R (L (Tag (R (R (R (R (R (L (C (D f0))))))))))))))))
    = StatStatBlockR (foldr ListConsR ListNilR $ fmap (toRef Stat . unI) f0)
  toRef Stat (InR (R (R (R (R (R (L (Tag (R (R (R (R (R (R (C ((:*:) f0 ((:*:) f1 ((:*:) f2 f3)) ))))))))))))))))
    = StatStatForR ((toRef Decl . unI) f0) ((toRef Expr . unI) f1) ((toRef Expr . unI) f2) ((toRef Stat . unI) f3)

  toRef Type (Ref p) = error "Type_Ref (toPath p)"
  toRef Type (InR (R (R (R (R (R (R (Tag (L (C U)))))))))) = TypeTypeVoidR
  toRef Type (InR (R (R (R (R (R (R (Tag (R (L (C f0)))))))))))
    = TypeTypePrimR (unK f0)
  toRef Type (InR (R (R (R (R (R (R (Tag (R (R (L (C f0))))))))))))
    = TypeTypeObjR (unK f0)
  toRef Type (InR (R (R (R (R (R (R (Tag (R (R (R (C f0))))))))))))
    = TypeTypeArrayR $ error "((toRef Type . unI) f0)"

  -- TODO
  fromRef Class (Class_Ref p) = Ref (fromPath p)


-- Generated with TH, manually edited

data ClassClass
instance Constructor ClassClass where
  conName _ = "ClassClass"
data ConstInt
data ConstBool
data ConstChar
instance Constructor ConstInt where
  conName _ = "ConstInt"
instance Constructor ConstBool where
  conName _ = "ConstBool"
instance Constructor ConstChar where
  conName _ = "ConstChar"
data DeclDecl
data DeclInit
instance Constructor DeclDecl where
  conName _ = "DeclDecl"
instance Constructor DeclInit where
  conName _ = "DeclInit"
data ExprConst
data ExprVar
data ExprOper
data ExprFun
instance Constructor ExprConst where
  conName _ = "ExprConst"
instance Constructor ExprVar where
  conName _ = "ExprVar"
instance Constructor ExprOper where
  conName _ = "ExprOper"
instance Constructor ExprFun where
  conName _ = "ExprFun"
data MemberD
data MemberM
instance Constructor MemberD where
  conName _ = "MemberD"
instance Constructor MemberM where
  conName _ = "MemberM"
data StatDecl
data StatExpr
data StatIf
data StatWhile
data StatReturn
data StatBlock
data StatFor
instance Constructor StatDecl where
  conName _ = "StatDecl"
instance Constructor StatExpr where
  conName _ = "StatExpr"
instance Constructor StatIf where
  conName _ = "StatIf"
instance Constructor StatWhile where
  conName _ = "StatWhile"
instance Constructor StatReturn where
  conName _ = "StatReturn"
instance Constructor StatBlock where
  conName _ = "StatBlock"
instance Constructor StatFor where
  conName _ = "StatFor"
data TypeVoid
data TypePrim
data TypeObj
data TypeArray
instance Constructor TypeVoid where
  conName _ = "TypeVoid"
instance Constructor TypePrim where
  conName _ = "TypePrim"
instance Constructor TypeObj where
  conName _ = "TypeObj"
instance Constructor TypeArray where
  conName _ = "TypeArray"

type instance PF AST = (:+:) ((:>:) (C ClassClass ((:*:) (K String) ((:.:) [] (I Member)))) Class) ((:+:) ((:>:) ((:+:) (C ConstInt (K Int)) ((:+:) (C ConstBool (K Bool)) (C ConstChar (K Char)))) Const) ((:+:) ((:>:) ((:+:) (C DeclDecl ((:*:) (I Type) (K String))) (C DeclInit ((:*:) (I Type) ((:*:) (K String) (I Expr))))) Decl) ((:+:) ((:>:) ((:+:) (C ExprConst (I Const)) ((:+:) (C ExprVar (K String)) ((:+:) (C ExprOper ((:*:) (K String) ((:*:) (I Expr) (I Expr)))) (C ExprFun ((:*:) (K String) ((:.:) [] (I Expr))))))) Expr) ((:+:) ((:>:) ((:+:) (C MemberD (I Decl)) (C MemberM ((:*:) (I Type) ((:*:) (K String) ((:*:) ((:.:) [] (I Decl)) (I Stat)))))) Member) ((:+:) ((:>:) ((:+:) (C StatDecl (I Decl)) ((:+:) (C StatExpr (I Expr)) ((:+:) (C StatIf ((:*:) (I Expr) ((:*:) (I Stat) (I Stat)))) ((:+:) (C StatWhile ((:*:) (I Expr) (I Stat))) ((:+:) (C StatReturn (I Expr)) ((:+:) (C StatBlock ((:.:) [] (I Stat))) (C StatFor (I Decl :*: I Expr :*: I Expr :*: I Stat)))))))) Stat) ((:>:) ((:+:) (C TypeVoid U) ((:+:) (C TypePrim (K String)) ((:+:) (C TypeObj (K String)) (C TypeArray (I Type))))) Type))))))

instance El AST Class where
  proof = Class
instance El AST Const where
  proof = Const
instance El AST Decl where
  proof = Decl
instance El AST Expr where
  proof = Expr
instance El AST Member where
  proof = Member
instance El AST Stat where
  proof = Stat
instance El AST Type where
  proof = Type

instance Fam AST where
  from Class (ClassC f0 f1) = L (Tag (C ((:*:) (K f0) (D (fmap (I . I0) f1)))))
  from Const (ConstInt f0) = R (L (Tag (L (C (K f0)))))
  from Const (ConstBool f0) = R (L (Tag (R (L (C (K f0))))))
  from Const (ConstChar f0) = R (L (Tag (R (R (C (K f0))))))
  from Decl (DeclC f0 f1)
    = R (R (L (Tag (L (C ((:*:) ((I . I0) f0) (K f1)))))))
  from Decl (DeclInit f0 f1 f2)
    = R (R (L (Tag (R (C ((I $ I0 f0) :*: K f1 :*: (I $ I0 f2)))))))
  from Expr (ExprConst f0)
    = R (R (R (L (Tag (L (C ((I . I0) f0)))))))
  from Expr (ExprVar f0) = R (R (R (L (Tag (R (L (C (K f0))))))))
  from Expr (ExprOper f0 f1 f2)
    = R (R (R (L (Tag (R (R (L (C ((:*:) (K f0) ((:*:) ((I . I0) f1) ((I . I0) f2)))))))))))
  from Expr (ExprFun f0 f1)
    = R (R (R (L (Tag (R (R (R (C ((:*:) (K f0) (D (fmap (I . I0) f1)))))))))))
  from Member (MemberD f0)
    = R (R (R (R (L (Tag (L (C ((I . I0) f0))))))))
  from Member (MemberM f0 f1 f2 f3)
    = R (R (R (R (L (Tag (R (C ((:*:) ((I . I0) f0) ((:*:) (K f1) ((:*:) (D (fmap (I . I0) f2)) ((I . I0) f3)))))))))))
  from Stat (StatDecl f0)
    = R (R (R (R (R (L (Tag (L (C ((I . I0) f0)))))))))
  from Stat (StatExpr f0)
    = R (R (R (R (R (L (Tag (R (L (C ((I . I0) f0))))))))))
  from Stat (StatIf f0 f1 f2)
    = R (R (R (R (R (L (Tag (R (R (L (C ((:*:) ((I . I0) f0) ((:*:) ((I . I0) f1) ((I . I0) f2)))))))))))))
  from Stat (StatWhile f0 f1)
    = R (R (R (R (R (L (Tag (R (R (R (L (C ((:*:) ((I . I0) f0) ((I . I0) f1)))))))))))))
  from Stat (StatReturn f0)
    = R (R (R (R (R (L (Tag (R (R (R (R (L (C ((I . I0) f0)))))))))))))
  from Stat (StatBlock f0)
    = R (R (R (R (R (L (Tag (R (R (R (R (R (L (C (D (fmap (I . I0) f0)))))))))))))))
  from Stat (StatFor f0 f1 f2 f3)
    = R (R (R (R (R (L (Tag (R (R (R (R (R (R (C ((I $ I0 f0) :*: (I $ I0 f1) :*: (I $ I0 f2) :*: (I $ I0 f3)))))))))))))))
  from Stat (StatCat f0 f1)
    = error "StatCat"
  from Type TypeVoid = R (R (R (R (R (R (Tag (L (C U))))))))
  from Type (TypePrim f0)
    = R (R (R (R (R (R (Tag (R (L (C (K f0))))))))))
  from Type (TypeObj f0)
    = R (R (R (R (R (R (Tag (R (R (L (C (K f0)))))))))))
  from Type (TypeArray f0)
    = R (R (R (R (R (R (Tag (R (R (R (C ((I . I0) f0)))))))))))
  to Class (L (Tag (C ((:*:) f0 f1)))) = ClassC (unK f0) (fmap (unI0 . unI) (unD f1))
  to Const (R (L (Tag (L (C f0))))) = ConstInt (unK f0)
  to Const (R (L (Tag (R (L (C f0)))))) = ConstBool (unK f0)
  to Const (R (L (Tag (R (R (C f0)))))) = ConstChar (unK f0)
  to Decl (R (R (L (Tag (L (C ((:*:) f0 f1)))))))
    = DeclC ((unI0 . unI) f0) (unK f1)
  to Expr (R (R (R (L (Tag (L (C f0)))))))
    = ExprConst ((unI0 . unI) f0)
  to Expr (R (R (R (L (Tag (R (L (C f0)))))))) = ExprVar (unK f0)
  to
    Expr
    (R (R (R (L (Tag (R (R (L (C ((:*:) f0 ((:*:) f1 f2)))))))))))
    = ExprOper (unK f0) ((unI0 . unI) f1) ((unI0 . unI) f2)
  to Expr (R (R (R (L (Tag (R (R (R (C ((:*:) f0 (D f1)))))))))))
    = ExprFun (unK f0) (fmap (unI0 . unI) f1)
  to Member (R (R (R (R (L (Tag (L (C f0))))))))
    = MemberD ((unI0 . unI) f0)
  to
    Member
    (R (R (R (R (L (Tag (R (C ((:*:) f0 ((:*:) f1 ((:*:) (D f2) f3)))))))))))
    = MemberM ((unI0 . unI) f0) (unK f1) (fmap (unI0 . unI) f2) ((unI0 . unI) f3)
  to Stat (R (R (R (R (R (L (Tag (L (C f0)))))))))
    = StatDecl ((unI0 . unI) f0)
  to Stat (R (R (R (R (R (L (Tag (R (L (C f0))))))))))
    = StatExpr ((unI0 . unI) f0)
  to
    Stat
    (R (R (R (R (R (L (Tag (R (R (L (C ((:*:) f0 ((:*:) f1 f2)))))))))))))
    = StatIf ((unI0 . unI) f0) ((unI0 . unI) f1) ((unI0 . unI) f2)
  to
    Stat
    (R (R (R (R (R (L (Tag (R (R (R (L (C ((:*:) f0 f1)))))))))))))
    = StatWhile ((unI0 . unI) f0) ((unI0 . unI) f1)
  to Stat (R (R (R (R (R (L (Tag (R (R (R (R (L (C f0)))))))))))))
    = StatReturn ((unI0 . unI) f0)
  to Stat (R (R (R (R (R (L (Tag (R (R (R (R (R (L (C (D f0)))))))))))))))
    = StatBlock (fmap (unI0 . unI) f0)
  to Type (R (R (R (R (R (R (Tag (L (C U))))))))) = TypeVoid
  to Type (R (R (R (R (R (R (Tag (R (L (C f0))))))))))
    = TypePrim (unK f0)
  to Type (R (R (R (R (R (R (Tag (R (R (L (C f0)))))))))))
    = TypeObj (unK f0)
  to Type (R (R (R (R (R (R (Tag (R (R (R (C f0)))))))))))
    = TypeArray ((unI0 . unI) f0)

-- Lifting data types to replacement types, should be automatically generated
class LiftR a top where
  liftR :: a -> ReplType a top

instance LiftR Class top where
  liftR (ClassC s m) = ClassClassCR s (liftR m)

instance LiftR Const top where
  liftR (ConstInt i)  = ConstConstIntR i
  liftR (ConstBool b) = ConstConstBoolR b
  liftR (ConstChar c) = ConstConstCharR c

instance LiftR Decl top where
  liftR (DeclC t s) = DeclDeclCR (liftR t) s
  
instance LiftR DeclL top where
  liftR []     = ListNilR
  liftR (x:xs) = ListConsR (liftR x) (liftR xs)

instance LiftR Expr top where
  liftR (ExprConst c)    = ExprExprConstR (liftR c)
  liftR (ExprVar v)      = ExprExprVarR v
  liftR (ExprOper o l r) = ExprExprOperR o (liftR l) (liftR r)
  liftR (ExprFun f a)    = ExprExprFunR f (liftR a)

instance LiftR ExprL top where
  liftR []     = ListNilR
  liftR (x:xs) = ListConsR (liftR x) (liftR xs)

instance LiftR Member top where
  liftR (MemberD d)       = MemberMemberDR (liftR d)
  liftR (MemberM t n d s) = MemberMemberMR (liftR t) n (liftR d) (liftR s)

instance LiftR MemberL top where
  liftR []     = ListNilR
  liftR (x:xs) = ListConsR (liftR x) (liftR xs)

instance LiftR Stat top where
  liftR (StatDecl d)    = StatStatDeclR (liftR d)
  liftR (StatExpr e)    = StatStatExprR (liftR e)
  liftR (StatIf e t f)  = StatStatIfR (liftR e) (liftR t) (liftR f)
  liftR (StatWhile e s) = StatStatWhileR (liftR e) (liftR s)
  liftR (StatReturn e)  = StatStatReturnR (liftR e)
  liftR (StatBlock s)   = StatStatBlockR (liftR s)

instance LiftR StatL top where
  liftR []     = ListNilR
  liftR (x:xs) = ListConsR (liftR x) (liftR xs)

instance LiftR Type top where
  liftR (TypeVoid)    = TypeTypeVoidR
  liftR (TypePrim s)  = TypeTypePrimR s
  liftR (TypeObj s)   = TypeTypeObjR s
  liftR (TypeArray t) = TypeTypeArrayR (liftR t)
