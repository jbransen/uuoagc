{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
import Data
-- import Generics.MultiRec

data AST :: * -> * where
  IClass  :: AST Class
  IMember :: AST Member
  IStat   :: AST Stat

data U         (r :: * -> *) iT = U
data I xi      (r :: * -> *) iT = I { unI :: r xi }
data K a       (r :: * -> *) iT = K { unK :: a }
data (f :+: g) (r :: * -> *) iT = L (f r iT) | R (g r iT)
data (f :*: g) (r :: * -> *) iT = f r iT :*: g r iT
data (f :>: ix) (r :: * -> *) ix' where
  Tag :: f r ix -> (f :>: ix) r ix

type CSharp_PF = (     I Decl
                   :+: I Expr
                   :+: (I Expr :*: I Stat :*: I Stat)
                 ) :>: Stat
                 :+: ( I Const
                   :+: K String
                   :+: (K String :*: I Expr :*: I Expr)
                 ) :>: Expr

type family PF (phi :: * -> *) :: (* -> *) -> * -> *
type instance PF AST = CSharp_PF


class SEq phi (f :: (* -> *) -> * -> *) where
  shallowEq :: f r ix  -> f r ix -> Bool

instance SEq phi (I xi) where
  shallowEq _ _ = True

instance SEq phi U where
  shallowEq _ _ = True

instance Eq a => SEq phi (K a) where
  shallowEq (K a) (K b) = a == b

instance (SEq phi f, SEq phi g) => SEq phi (f :+: g) where
  shallowEq (L a) (L b) = shallowEq a b
  shallowEq (R a) (R b) = shallowEq a b
  shallowEq _     _     = False

instance (SEq phi f, SEq phi g) => SEq phi (f :*: g) where
  shallowEq (a :*: b) (c :*: d) = shallowEq a c && shallowEq b d

instance SEq phi f => SEq phi (f :>: ix) where
  shallowEq (Tag a) (Tag b) = shallowEq a b
