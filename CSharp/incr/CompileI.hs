{-# LANGUAGE GADTs, TypeFamilies, RankNTypes, ScopedTypeVariables #-}
{-# LANGUAGE CPP #-}

module CompileI where

import Prelude hiding (LT, GT, EQ)
import Data.Map (Map, findWithDefault, empty, fromList)
import Data.Char (ord)

#if GATHER_STATS
import System.IO.Unsafe (unsafePerformIO)
import Data.IORef (newIORef, readIORef, writeIORef, modifyIORef, IORef)
#endif

import SSM

generateCode :: Class -> (Code, TClass Class)
generateCode c = tclass_v0 t t where t = semClass c

generateCode2 :: TClass Class -> [MyInsert phi] -> (Code, TClass Class)
generateCode2 t ins = tclass_v0 t2 t2 where
  lu :: forall t. Path Class t -> SemType t Class
  lu = tclass_lookup t t
  t2 = foldl (\t (MyInsert _ p r) -> tclass_change t t lu p r) t ins

data MyInsert phi where
  MyInsert :: forall phi r. phi r -> Path Class r -> ReplType r Class -> MyInsert phi

opCodes :: Map String Instr
opCodes
 = fromList
     [ ( "+" , ADD )
     , ( "-" , SUB )
     , ( "*" , MUL )
     , ( "/" , DIV )
     , ( "%" , MOD )
     , ( "<=", LE  ) 
     , ( ">=", GE  )
     , ( "<" , LT  )
     , ( ">" , GT  )
     , ( "==", EQ  )
     , ( "!=", NE  )
     , ( "&&", AND )
     , ( "||", OR  )
     , ( "^" , XOR )
     ]


#if GATHER_STATS
counterSem :: IORef Int
counterSem = unsafePerformIO $ newIORef 0

counterAG :: IORef Int
counterAG = unsafePerformIO $ newIORef 0

counterEQ :: IORef Int
counterEQ = unsafePerformIO $ newIORef 0
#endif

tickSem, tickAG, tickEQ :: a -> a
#if GATHER_STATS
tickSem x = unsafePerformIO $ modifyIORef counterSem succ >> return x
tickAG x = unsafePerformIO $ modifyIORef counterAG succ >> return x
tickEQ x = unsafePerformIO $ modifyIORef counterEQ succ >> return x
#else
tickSem = id
tickAG = id
tickEQ = id
#endif

printStats, resetStats :: IO ()
#if GATHER_STATS
printStats = do
  s <- readIORef counterSem
  a <- readIORef counterAG
  e <- readIORef counterEQ
  putStrLn $ "Sem = " ++ show s ++ "; AG = " ++ show a ++ "; EQ = " ++ show e

resetStats = writeIORef counterSem 0 >> writeIORef counterAG 0 >> writeIORef counterEQ 0
#else
printStats = return ()
resetStats = return ()
#endif

-- Data types
data Class
  = ClassC String MemberL
  deriving (Eq,Ord,Show)

data Const
  = ConstInt Int
  | ConstBool Bool
  | ConstChar Char
  deriving (Eq,Ord,Show)

data Decl
  = DeclC Type String
  | DeclInit Type String Expr
  deriving (Eq,Ord,Show)

type DeclL = [ Decl ]

data Expr
  = ExprConst Const
  | ExprVar String
  | ExprOper String Expr Expr
  | ExprFun String ExprL
  deriving (Eq,Ord,Show)

type ExprL = [ Expr ]

data Member
  = MemberD Decl
  | MemberM Type String DeclL Stat
  deriving (Eq,Ord,Show)

type MemberL = [ Member ]

data Stat
  = StatDecl Decl
  | StatExpr Expr
  | StatIf Expr Stat Stat
  | StatWhile Expr Stat
  | StatFor Decl Expr Expr Stat
  | StatReturn Expr
  | StatCat Stat Stat
  | StatBlock StatL
  deriving (Eq,Ord,Show)

type StatL = [ Stat ]

data Type
  = TypeVoid
  | TypePrim String
  | TypeObj String
  | TypeArray Type
  deriving (Eq,Ord,Show)

-- Path
data Path f t where
  End :: Path t t
  PathL_hd :: (Path a t) -> Path [ a ] t
  PathL_tl :: (Path [ a ] t) -> Path [ a ] t
  ClassClassCP_members :: (Path MemberL t) -> Path Class t
  DeclDeclCP_vtype :: (Path Type t) -> Path Decl t
  DeclDeclInitP_vtype :: (Path Type t) -> Path Decl t
  DeclDeclInitP_init :: (Path Expr t) -> Path Decl t
  ExprExprConstP_const :: (Path Const t) -> Path Expr t
  ExprExprOperP_left :: (Path Expr t) -> Path Expr t
  ExprExprOperP_right :: (Path Expr t) -> Path Expr t
  ExprExprFunP_params :: (Path ExprL t) -> Path Expr t
  MemberMemberDP_decl :: (Path Decl t) -> Path Member t
  MemberMemberMP_rtype :: (Path Type t) -> Path Member t
  MemberMemberMP_params :: (Path DeclL t) -> Path Member t
  MemberMemberMP_body :: (Path Stat t) -> Path Member t
  StatStatDeclP_decl :: (Path Decl t) -> Path Stat t
  StatStatExprP_expr :: (Path Expr t) -> Path Stat t
  StatStatIfP_cond :: (Path Expr t) -> Path Stat t
  StatStatIfP_true :: (Path Stat t) -> Path Stat t
  StatStatIfP_false :: (Path Stat t) -> Path Stat t
  StatStatWhileP_cond :: (Path Expr t) -> Path Stat t
  StatStatWhileP_body :: (Path Stat t) -> Path Stat t
  StatStatForP_init :: (Path Decl t) -> Path Stat t
  StatStatForP_cond :: (Path Expr t) -> Path Stat t
  StatStatForP_incr :: (Path Expr t) -> Path Stat t
  StatStatForP_body :: (Path Stat t) -> Path Stat t
  StatStatReturnP_expr :: (Path Expr t) -> Path Stat t
  StatStatCatP_l :: (Path Stat t) -> Path Stat t
  StatStatCatP_r :: (Path Stat t) -> Path Stat t
  StatStatBlockP_stats :: (Path StatL t) -> Path Stat t
  TypeTypeArrayP_itype :: (Path Type t) -> Path Type t

-- Replacement types
data ListR a ar top
  = List_Ref (Path top [ a ])
  | ListConsR ar (ListR a ar top)
  | ListNilR

data ClassR top
  = Class_Ref (Path top Class)
  | ClassClassCR String (MemberLR top)

data ConstR top
  = Const_Ref (Path top Const)
  | ConstConstIntR Int
  | ConstConstBoolR Bool
  | ConstConstCharR Char

data DeclR top
  = Decl_Ref (Path top Decl)
  | DeclDeclCR (TypeR top) String
  | DeclDeclInitR (TypeR top) String (ExprR top)

type DeclLR top = ListR Decl (ReplType Decl top) top

data ExprR top
  = Expr_Ref (Path top Expr)
  | ExprExprConstR (ConstR top)
  | ExprExprVarR String
  | ExprExprOperR String (ExprR top) (ExprR top)
  | ExprExprFunR String (ExprLR top)

type ExprLR top = ListR Expr (ReplType Expr top) top

data MemberR top
  = Member_Ref (Path top Member)
  | MemberMemberDR (DeclR top)
  | MemberMemberMR (TypeR top) String (DeclLR top) (StatR top)

type MemberLR top = ListR Member (ReplType Member top) top

data StatR top
  = Stat_Ref (Path top Stat)
  | StatStatDeclR (DeclR top)
  | StatStatExprR (ExprR top)
  | StatStatIfR (ExprR top) (StatR top) (StatR top)
  | StatStatWhileR (ExprR top) (StatR top)
  | StatStatForR (DeclR top) (ExprR top) (ExprR top) (StatR top)
  | StatStatReturnR (ExprR top)
  | StatStatCatR (StatR top) (StatR top)
  | StatStatBlockR (StatLR top)

type StatLR top = ListR Stat (ReplType Stat top) top

data TypeR top
  = Type_Ref (Path top Type)
  | TypeTypeVoidR
  | TypeTypePrimR String
  | TypeTypeObjR String
  | TypeTypeArrayR (TypeR top)

type family ReplType a b :: *
type instance ReplType Class top = ClassR top
type instance ReplType Const top = ConstR top
type instance ReplType Decl top = DeclR top
type instance ReplType DeclL top = DeclLR top
type instance ReplType Expr top = ExprR top
type instance ReplType ExprL top = ExprLR top
type instance ReplType Member top = MemberR top
type instance ReplType MemberL top = MemberLR top
type instance ReplType Stat top = StatR top
type instance ReplType StatL top = StatLR top
type instance ReplType Type top = TypeR top

-- Semantic types
data TClass top
  = TClassClassC {
      tclass_lookup :: forall t. (TClass top) -> (Path Class t) -> SemType t top,
      tclass_change :: forall r. (TClass top) -> (forall t. (Path top t) -> SemType t top) -> (Path Class r) -> (ReplType r top) -> TClass top,
      tclass_v0 :: (TClass top) -> (Code, TClass top),
      tclass_v0_dirty :: Bool,
      tclass_members :: TMemberL top
    }

data TConst top
  = TConstConstInt {
      tconst_lookup :: forall t. (TConst top) -> (Path Const t) -> SemType t top,
      tconst_change :: forall r. (TConst top) -> (forall t. (Path top t) -> SemType t top) -> (Path Const r) -> (ReplType r top) -> TConst top,
      tconst_v0 :: (TConst top) -> (forall t. (Path Const t) -> Path Stat t) -> ((Code, Const, ConstR Stat), TConst top),
      tconst_v0_dirty :: Bool
    }
  | TConstConstBool {
      tconst_lookup :: forall t. (TConst top) -> (Path Const t) -> SemType t top,
      tconst_change :: forall r. (TConst top) -> (forall t. (Path top t) -> SemType t top) -> (Path Const r) -> (ReplType r top) -> TConst top,
      tconst_v0 :: (TConst top) -> (forall t. (Path Const t) -> Path Stat t) -> ((Code, Const, ConstR Stat), TConst top),
      tconst_v0_dirty :: Bool
    }
  | TConstConstChar {
      tconst_lookup :: forall t. (TConst top) -> (Path Const t) -> SemType t top,
      tconst_change :: forall r. (TConst top) -> (forall t. (Path top t) -> SemType t top) -> (Path Const r) -> (ReplType r top) -> TConst top,
      tconst_v0 :: (TConst top) -> (forall t. (Path Const t) -> Path Stat t) -> ((Code, Const, ConstR Stat), TConst top),
      tconst_v0_dirty :: Bool
    }

data TDecl top
  = TDeclDeclC {
      tdecl_lookup :: forall t. (TDecl top) -> (Path Decl t) -> SemType t top,
      tdecl_change :: forall r. (TDecl top) -> (forall t. (Path top t) -> SemType t top) -> (Path Decl r) -> (ReplType r top) -> TDecl top,
      tdecl_v0 :: (TDecl top) -> (forall t. (Path Decl t) -> Path Stat t) -> ((Decl, DeclR Stat, [String]), TDecl top),
      tdecl_v1 :: (TDecl top) -> (Map String Int) -> (Code, TDecl top),
      tdecl_v0_dirty :: Bool,
      tdecl_v1_dirty :: Bool,
      tdecl_vtype :: TType top
    }
  | TDeclDeclInit {
      tdecl_lookup :: forall t. (TDecl top) -> (Path Decl t) -> SemType t top,
      tdecl_change :: forall r. (TDecl top) -> (forall t. (Path top t) -> SemType t top) -> (Path Decl r) -> (ReplType r top) -> TDecl top,
      tdecl_v0 :: (TDecl top) -> (forall t. (Path Decl t) -> Path Stat t) -> ((Decl, DeclR Stat, [String]), TDecl top),
      tdecl_v1 :: (TDecl top) -> (Map String Int) -> (Code, TDecl top),
      tdecl_v0_dirty :: Bool,
      tdecl_v1_dirty :: Bool,
      tdecl_vtype :: TType top,
      tdecl_init :: TExpr top,
      tdecl_stat :: Maybe (TStat Stat),
      tdecl_init_copy :: Expr,
      tdecl_init_copyRStat :: ExprR Stat
    }

data TDeclL top
  = TDeclLCons {
      tdecll_lookup :: forall t. (TDeclL top) -> (Path DeclL t) -> SemType t top,
      tdecll_change :: forall r. (TDeclL top) -> (forall t. (Path top t) -> SemType t top) -> (Path DeclL r) -> (ReplType r top) -> TDeclL top,
      tdecll_v0 :: (TDeclL top) -> ((Code, [String], Int), TDeclL top),
      tdecll_v0_dirty :: Bool,
      tdecll_hd :: TDecl top,
      tdecll_tl :: TDeclL top
    }
  | TDeclLNil {
      tdecll_lookup :: forall t. (TDeclL top) -> (Path DeclL t) -> SemType t top,
      tdecll_change :: forall r. (TDeclL top) -> (forall t. (Path top t) -> SemType t top) -> (Path DeclL r) -> (ReplType r top) -> TDeclL top,
      tdecll_v0 :: (TDeclL top) -> ((Code, [String], Int), TDeclL top),
      tdecll_v0_dirty :: Bool
    }

data TExpr top
  = TExprExprConst {
      texpr_lookup :: forall t. (TExpr top) -> (Path Expr t) -> SemType t top,
      texpr_change :: forall r. (TExpr top) -> (forall t. (Path top t) -> SemType t top) -> (Path Expr r) -> (ReplType r top) -> TExpr top,
      texpr_v0 :: (TExpr top) -> (forall t. (Path Expr t) -> Path Stat t) -> ((Expr, ExprR Stat), TExpr top),
      texpr_v1 :: (TExpr top) -> (Map String Int) -> ((Code, Code), TExpr top),
      texpr_v0_dirty :: Bool,
      texpr_v1_dirty :: Bool,
      texpr_const :: TConst top,
      texpr_const_code :: Code
    }
  | TExprExprVar {
      texpr_lookup :: forall t. (TExpr top) -> (Path Expr t) -> SemType t top,
      texpr_change :: forall r. (TExpr top) -> (forall t. (Path top t) -> SemType t top) -> (Path Expr r) -> (ReplType r top) -> TExpr top,
      texpr_v0 :: (TExpr top) -> (forall t. (Path Expr t) -> Path Stat t) -> ((Expr, ExprR Stat), TExpr top),
      texpr_v1 :: (TExpr top) -> (Map String Int) -> ((Code, Code), TExpr top),
      texpr_v0_dirty :: Bool,
      texpr_v1_dirty :: Bool
    }
  | TExprExprOper {
      texpr_lookup :: forall t. (TExpr top) -> (Path Expr t) -> SemType t top,
      texpr_change :: forall r. (TExpr top) -> (forall t. (Path top t) -> SemType t top) -> (Path Expr r) -> (ReplType r top) -> TExpr top,
      texpr_v0 :: (TExpr top) -> (forall t. (Path Expr t) -> Path Stat t) -> ((Expr, ExprR Stat), TExpr top),
      texpr_v1 :: (TExpr top) -> (Map String Int) -> ((Code, Code), TExpr top),
      texpr_v0_dirty :: Bool,
      texpr_v1_dirty :: Bool,
      texpr_left :: TExpr top,
      texpr_right :: TExpr top
    }
  | TExprExprFun {
      texpr_lookup :: forall t. (TExpr top) -> (Path Expr t) -> SemType t top,
      texpr_change :: forall r. (TExpr top) -> (forall t. (Path top t) -> SemType t top) -> (Path Expr r) -> (ReplType r top) -> TExpr top,
      texpr_v0 :: (TExpr top) -> (forall t. (Path Expr t) -> Path Stat t) -> ((Expr, ExprR Stat), TExpr top),
      texpr_v1 :: (TExpr top) -> (Map String Int) -> ((Code, Code), TExpr top),
      texpr_v0_dirty :: Bool,
      texpr_v1_dirty :: Bool,
      texpr_params :: TExprL top
    }

data TExprL top
  = TExprLCons {
      texprl_lookup :: forall t. (TExprL top) -> (Path ExprL t) -> SemType t top,
      texprl_change :: forall r. (TExprL top) -> (forall t. (Path top t) -> SemType t top) -> (Path ExprL r) -> (ReplType r top) -> TExprL top,
      texprl_v0 :: (TExprL top) -> (forall t. (Path ExprL t) -> Path Stat t) -> ((ExprL, ExprLR Stat), TExprL top),
      texprl_v1 :: (TExprL top) -> (Map String Int) -> ((Code, Int), TExprL top),
      texprl_v0_dirty :: Bool,
      texprl_v1_dirty :: Bool,
      texprl_hd :: TExpr top,
      texprl_tl :: TExprL top
    }
  | TExprLNil {
      texprl_lookup :: forall t. (TExprL top) -> (Path ExprL t) -> SemType t top,
      texprl_change :: forall r. (TExprL top) -> (forall t. (Path top t) -> SemType t top) -> (Path ExprL r) -> (ReplType r top) -> TExprL top,
      texprl_v0 :: (TExprL top) -> (forall t. (Path ExprL t) -> Path Stat t) -> ((ExprL, ExprLR Stat), TExprL top),
      texprl_v1 :: (TExprL top) -> (Map String Int) -> ((Code, Int), TExprL top),
      texprl_v0_dirty :: Bool,
      texprl_v1_dirty :: Bool
    }

data TMember top
  = TMemberMemberD {
      tmember_lookup :: forall t. (TMember top) -> (Path Member t) -> SemType t top,
      tmember_change :: forall r. (TMember top) -> (forall t. (Path top t) -> SemType t top) -> (Path Member r) -> (ReplType r top) -> TMember top,
      tmember_v0 :: (TMember top) -> (Code, TMember top),
      tmember_v0_dirty :: Bool,
      tmember_decl :: TDecl top
    }
  | TMemberMemberM {
      tmember_lookup :: forall t. (TMember top) -> (Path Member t) -> SemType t top,
      tmember_change :: forall r. (TMember top) -> (forall t. (Path top t) -> SemType t top) -> (Path Member r) -> (ReplType r top) -> TMember top,
      tmember_v0 :: (TMember top) -> (Code, TMember top),
      tmember_v0_dirty :: Bool,
      tmember_rtype :: TType top,
      tmember_params :: TDeclL top,
      tmember_body :: TStat top
    }

data TMemberL top
  = TMemberLCons {
      tmemberl_lookup :: forall t. (TMemberL top) -> (Path MemberL t) -> SemType t top,
      tmemberl_change :: forall r. (TMemberL top) -> (forall t. (Path top t) -> SemType t top) -> (Path MemberL r) -> (ReplType r top) -> TMemberL top,
      tmemberl_v0 :: (TMemberL top) -> (Code, TMemberL top),
      tmemberl_v0_dirty :: Bool,
      tmemberl_hd :: TMember top,
      tmemberl_tl :: TMemberL top
    }
  | TMemberLNil {
      tmemberl_lookup :: forall t. (TMemberL top) -> (Path MemberL t) -> SemType t top,
      tmemberl_change :: forall r. (TMemberL top) -> (forall t. (Path top t) -> SemType t top) -> (Path MemberL r) -> (ReplType r top) -> TMemberL top,
      tmemberl_v0 :: (TMemberL top) -> (Code, TMemberL top),
      tmemberl_v0_dirty :: Bool
    }

data TStat top
  = TStatStatDecl {
      tstat_lookup :: forall t. (TStat top) -> (Path Stat t) -> SemType t top,
      tstat_change :: forall r. (TStat top) -> (forall t. (Path top t) -> SemType t top) -> (Path Stat r) -> (ReplType r top) -> TStat top,
      tstat_v0 :: (TStat top) -> (forall t. (Path Stat t) -> Path Stat t) -> ((Stat, StatR Stat, [String]), TStat top),
      tstat_v1 :: (TStat top) -> (Map String Int) -> (Code, TStat top),
      tstat_v0_dirty :: Bool,
      tstat_v1_dirty :: Bool,
      tstat_decl :: TDecl top
    }
  | TStatStatExpr {
      tstat_lookup :: forall t. (TStat top) -> (Path Stat t) -> SemType t top,
      tstat_change :: forall r. (TStat top) -> (forall t. (Path top t) -> SemType t top) -> (Path Stat r) -> (ReplType r top) -> TStat top,
      tstat_v0 :: (TStat top) -> (forall t. (Path Stat t) -> Path Stat t) -> ((Stat, StatR Stat, [String]), TStat top),
      tstat_v1 :: (TStat top) -> (Map String Int) -> (Code, TStat top),
      tstat_v0_dirty :: Bool,
      tstat_v1_dirty :: Bool,
      tstat_expr :: TExpr top
    }
  | TStatStatIf {
      tstat_lookup :: forall t. (TStat top) -> (Path Stat t) -> SemType t top,
      tstat_change :: forall r. (TStat top) -> (forall t. (Path top t) -> SemType t top) -> (Path Stat r) -> (ReplType r top) -> TStat top,
      tstat_v0 :: (TStat top) -> (forall t. (Path Stat t) -> Path Stat t) -> ((Stat, StatR Stat, [String]), TStat top),
      tstat_v1 :: (TStat top) -> (Map String Int) -> (Code, TStat top),
      tstat_v0_dirty :: Bool,
      tstat_v1_dirty :: Bool,
      tstat_cond :: TExpr top,
      tstat_true :: TStat top,
      tstat_false :: TStat top
    }
  | TStatStatWhile {
      tstat_lookup :: forall t. (TStat top) -> (Path Stat t) -> SemType t top,
      tstat_change :: forall r. (TStat top) -> (forall t. (Path top t) -> SemType t top) -> (Path Stat r) -> (ReplType r top) -> TStat top,
      tstat_v0 :: (TStat top) -> (forall t. (Path Stat t) -> Path Stat t) -> ((Stat, StatR Stat, [String]), TStat top),
      tstat_v1 :: (TStat top) -> (Map String Int) -> (Code, TStat top),
      tstat_v0_dirty :: Bool,
      tstat_v1_dirty :: Bool,
      tstat_cond :: TExpr top,
      tstat_body :: TStat top
    }
  | TStatStatFor {
      tstat_lookup :: forall t. (TStat top) -> (Path Stat t) -> SemType t top,
      tstat_change :: forall r. (TStat top) -> (forall t. (Path top t) -> SemType t top) -> (Path Stat r) -> (ReplType r top) -> TStat top,
      tstat_v0 :: (TStat top) -> (forall t. (Path Stat t) -> Path Stat t) -> ((Stat, StatR Stat, [String]), TStat top),
      tstat_v1 :: (TStat top) -> (Map String Int) -> (Code, TStat top),
      tstat_v0_dirty :: Bool,
      tstat_v1_dirty :: Bool,
      tstat_init :: TDecl top,
      tstat_cond :: TExpr top,
      tstat_incr :: TExpr top,
      tstat_body :: TStat top,
      tstat_block :: Maybe (TStat Stat)
    }
  | TStatStatReturn {
      tstat_lookup :: forall t. (TStat top) -> (Path Stat t) -> SemType t top,
      tstat_change :: forall r. (TStat top) -> (forall t. (Path top t) -> SemType t top) -> (Path Stat r) -> (ReplType r top) -> TStat top,
      tstat_v0 :: (TStat top) -> (forall t. (Path Stat t) -> Path Stat t) -> ((Stat, StatR Stat, [String]), TStat top),
      tstat_v1 :: (TStat top) -> (Map String Int) -> (Code, TStat top),
      tstat_v0_dirty :: Bool,
      tstat_v1_dirty :: Bool,
      tstat_expr :: TExpr top
    }
  | TStatStatCat {
      tstat_lookup :: forall t. (TStat top) -> (Path Stat t) -> SemType t top,
      tstat_change :: forall r. (TStat top) -> (forall t. (Path top t) -> SemType t top) -> (Path Stat r) -> (ReplType r top) -> TStat top,
      tstat_v0 :: (TStat top) -> (forall t. (Path Stat t) -> Path Stat t) -> ((Stat, StatR Stat, [String]), TStat top),
      tstat_v1 :: (TStat top) -> (Map String Int) -> (Code, TStat top),
      tstat_v0_dirty :: Bool,
      tstat_v1_dirty :: Bool,
      tstat_l :: TStat top,
      tstat_r :: TStat top
    }
  | TStatStatBlock {
      tstat_lookup :: forall t. (TStat top) -> (Path Stat t) -> SemType t top,
      tstat_change :: forall r. (TStat top) -> (forall t. (Path top t) -> SemType t top) -> (Path Stat r) -> (ReplType r top) -> TStat top,
      tstat_v0 :: (TStat top) -> (forall t. (Path Stat t) -> Path Stat t) -> ((Stat, StatR Stat, [String]), TStat top),
      tstat_v1 :: (TStat top) -> (Map String Int) -> (Code, TStat top),
      tstat_v0_dirty :: Bool,
      tstat_v1_dirty :: Bool,
      tstat_stats :: TStatL top
    }

data TStatL top
  = TStatLCons {
      tstatl_lookup :: forall t. (TStatL top) -> (Path StatL t) -> SemType t top,
      tstatl_change :: forall r. (TStatL top) -> (forall t. (Path top t) -> SemType t top) -> (Path StatL r) -> (ReplType r top) -> TStatL top,
      tstatl_v0 :: (TStatL top) -> (forall t. (Path StatL t) -> Path Stat t) -> ((StatL, StatLR Stat, [String]), TStatL top),
      tstatl_v1 :: (TStatL top) -> (Map String Int) -> ((Code, Int), TStatL top),
      tstatl_v0_dirty :: Bool,
      tstatl_v1_dirty :: Bool,
      tstatl_hd :: TStat top,
      tstatl_tl :: TStatL top
    }
  | TStatLNil {
      tstatl_lookup :: forall t. (TStatL top) -> (Path StatL t) -> SemType t top,
      tstatl_change :: forall r. (TStatL top) -> (forall t. (Path top t) -> SemType t top) -> (Path StatL r) -> (ReplType r top) -> TStatL top,
      tstatl_v0 :: (TStatL top) -> (forall t. (Path StatL t) -> Path Stat t) -> ((StatL, StatLR Stat, [String]), TStatL top),
      tstatl_v1 :: (TStatL top) -> (Map String Int) -> ((Code, Int), TStatL top),
      tstatl_v0_dirty :: Bool,
      tstatl_v1_dirty :: Bool
    }

data TType top
  = TTypeTypeVoid {
      ttype_lookup :: forall t. (TType top) -> (Path Type t) -> SemType t top,
      ttype_change :: forall r. (TType top) -> (forall t. (Path top t) -> SemType t top) -> (Path Type r) -> (ReplType r top) -> TType top,
      ttype_v0 :: (TType top) -> (forall t. (Path Type t) -> Path Stat t) -> ((Type, TypeR Stat), TType top),
      ttype_v0_dirty :: Bool
    }
  | TTypeTypePrim {
      ttype_lookup :: forall t. (TType top) -> (Path Type t) -> SemType t top,
      ttype_change :: forall r. (TType top) -> (forall t. (Path top t) -> SemType t top) -> (Path Type r) -> (ReplType r top) -> TType top,
      ttype_v0 :: (TType top) -> (forall t. (Path Type t) -> Path Stat t) -> ((Type, TypeR Stat), TType top),
      ttype_v0_dirty :: Bool
    }
  | TTypeTypeObj {
      ttype_lookup :: forall t. (TType top) -> (Path Type t) -> SemType t top,
      ttype_change :: forall r. (TType top) -> (forall t. (Path top t) -> SemType t top) -> (Path Type r) -> (ReplType r top) -> TType top,
      ttype_v0 :: (TType top) -> (forall t. (Path Type t) -> Path Stat t) -> ((Type, TypeR Stat), TType top),
      ttype_v0_dirty :: Bool
    }
  | TTypeTypeArray {
      ttype_lookup :: forall t. (TType top) -> (Path Type t) -> SemType t top,
      ttype_change :: forall r. (TType top) -> (forall t. (Path top t) -> SemType t top) -> (Path Type r) -> (ReplType r top) -> TType top,
      ttype_v0 :: (TType top) -> (forall t. (Path Type t) -> Path Stat t) -> ((Type, TypeR Stat), TType top),
      ttype_v0_dirty :: Bool,
      ttype_itype :: TType top
    }

type family SemType a :: * -> *
type instance SemType Class = TClass
type instance SemType Const = TConst
type instance SemType Decl = TDecl
type instance SemType DeclL = TDeclL
type instance SemType Expr = TExpr
type instance SemType ExprL = TExprL
type instance SemType Member = TMember
type instance SemType MemberL = TMemberL
type instance SemType Stat = TStat
type instance SemType StatL = TStatL
type instance SemType Type = TType

-- Semantic functions
semClass :: Class -> TClass top
semClass (ClassC name members) = semClass_ClassC name (semMemberL members)

semConst :: Const -> TConst top
semConst (ConstInt val) = semConst_ConstInt val
semConst (ConstBool val) = semConst_ConstBool val
semConst (ConstChar val) = semConst_ConstChar val

semDecl :: Decl -> TDecl top
semDecl (DeclC vtype name) = semDecl_DeclC (semType vtype) name
semDecl (DeclInit vtype name init) = semDecl_DeclInit (semType vtype) name (semExpr init)

semDeclL :: DeclL -> TDeclL top
semDeclL = foldr semDeclL_Cons semDeclL_Nil . map semDecl

semExpr :: Expr -> TExpr top
semExpr (ExprConst const) = semExpr_ExprConst (semConst const)
semExpr (ExprVar name) = semExpr_ExprVar name
semExpr (ExprOper op left right) = semExpr_ExprOper op (semExpr left) (semExpr right)
semExpr (ExprFun name params) = semExpr_ExprFun name (semExprL params)

semExprL :: ExprL -> TExprL top
semExprL = foldr semExprL_Cons semExprL_Nil . map semExpr

semMember :: Member -> TMember top
semMember (MemberD decl) = semMember_MemberD (semDecl decl)
semMember (MemberM rtype name params body) = semMember_MemberM (semType rtype) name (semDeclL params) (semStat body)

semMemberL :: MemberL -> TMemberL top
semMemberL = foldr semMemberL_Cons semMemberL_Nil . map semMember

semStat :: Stat -> TStat top
semStat (StatDecl decl) = semStat_StatDecl (semDecl decl)
semStat (StatExpr expr) = semStat_StatExpr (semExpr expr)
semStat (StatIf cond true false) = semStat_StatIf (semExpr cond) (semStat true) (semStat false)
semStat (StatWhile cond body) = semStat_StatWhile (semExpr cond) (semStat body)
semStat (StatFor init cond incr body) = semStat_StatFor (semDecl init) (semExpr cond) (semExpr incr) (semStat body)
semStat (StatReturn expr) = semStat_StatReturn (semExpr expr)
semStat (StatCat l r) = semStat_StatCat (semStat l) (semStat r)
semStat (StatBlock stats) = semStat_StatBlock (semStatL stats)

semStatL :: StatL -> TStatL top
semStatL = foldr semStatL_Cons semStatL_Nil . map semStat

semType :: Type -> TType top
semType (TypeVoid) = semType_TypeVoid
semType (TypePrim ptype) = semType_TypePrim ptype
semType (TypeObj otype) = semType_TypeObj otype
semType (TypeArray itype) = semType_TypeArray (semType itype)

semClassR :: (forall t. (Path top t) -> SemType t top) -> (ClassR top) -> TClass top
semClassR lu (Class_Ref p) = lu p
semClassR lu (ClassClassCR name members) = semClass_ClassC name (semMemberLR lu members)

semConstR :: (forall t. (Path top t) -> SemType t top) -> (ConstR top) -> TConst top
semConstR lu (Const_Ref p) = lu p
semConstR lu (ConstConstIntR val) = semConst_ConstInt val
semConstR lu (ConstConstBoolR val) = semConst_ConstBool val
semConstR lu (ConstConstCharR val) = semConst_ConstChar val

semDeclR :: (forall t. (Path top t) -> SemType t top) -> (DeclR top) -> TDecl top
semDeclR lu (Decl_Ref p) = lu p
semDeclR lu (DeclDeclCR vtype name) = semDecl_DeclC (semTypeR lu vtype) name
semDeclR lu (DeclDeclInitR vtype name init) = semDecl_DeclInit (semTypeR lu vtype) name (semExprR lu init)

semDeclLR :: (forall t. (Path top t) -> SemType t top) -> (DeclLR top) -> TDeclL top
semDeclLR lu (List_Ref p) = lu p
semDeclLR lu (ListConsR hd tl) = semDeclL_Cons (semDeclR lu hd) (semDeclLR lu tl)
semDeclLR lu (ListNilR) = semDeclL_Nil

semExprR :: (forall t. (Path top t) -> SemType t top) -> (ExprR top) -> TExpr top
semExprR lu (Expr_Ref p) = lu p
semExprR lu (ExprExprConstR const) = semExpr_ExprConst (semConstR lu const)
semExprR lu (ExprExprVarR name) = semExpr_ExprVar name
semExprR lu (ExprExprOperR op left right) = semExpr_ExprOper op (semExprR lu left) (semExprR lu right)
semExprR lu (ExprExprFunR name params) = semExpr_ExprFun name (semExprLR lu params)

semExprLR :: (forall t. (Path top t) -> SemType t top) -> (ExprLR top) -> TExprL top
semExprLR lu (List_Ref p) = lu p
semExprLR lu (ListConsR hd tl) = semExprL_Cons (semExprR lu hd) (semExprLR lu tl)
semExprLR lu (ListNilR) = semExprL_Nil

semMemberR :: (forall t. (Path top t) -> SemType t top) -> (MemberR top) -> TMember top
semMemberR lu (Member_Ref p) = lu p
semMemberR lu (MemberMemberDR decl) = semMember_MemberD (semDeclR lu decl)
semMemberR lu (MemberMemberMR rtype name params body) = semMember_MemberM (semTypeR lu rtype) name (semDeclLR lu params) (semStatR lu body)

semMemberLR :: (forall t. (Path top t) -> SemType t top) -> (MemberLR top) -> TMemberL top
semMemberLR lu (List_Ref p) = lu p
semMemberLR lu (ListConsR hd tl) = semMemberL_Cons (semMemberR lu hd) (semMemberLR lu tl)
semMemberLR lu (ListNilR) = semMemberL_Nil

semStatR :: (forall t. (Path top t) -> SemType t top) -> (StatR top) -> TStat top
semStatR lu (Stat_Ref p) = lu p
semStatR lu (StatStatDeclR decl) = semStat_StatDecl (semDeclR lu decl)
semStatR lu (StatStatExprR expr) = semStat_StatExpr (semExprR lu expr)
semStatR lu (StatStatIfR cond true false) = semStat_StatIf (semExprR lu cond) (semStatR lu true) (semStatR lu false)
semStatR lu (StatStatWhileR cond body) = semStat_StatWhile (semExprR lu cond) (semStatR lu body)
semStatR lu (StatStatForR init cond incr body) = semStat_StatFor (semDeclR lu init) (semExprR lu cond) (semExprR lu incr) (semStatR lu body)
semStatR lu (StatStatReturnR expr) = semStat_StatReturn (semExprR lu expr)
semStatR lu (StatStatCatR l r) = semStat_StatCat (semStatR lu l) (semStatR lu r)
semStatR lu (StatStatBlockR stats) = semStat_StatBlock (semStatLR lu stats)

semStatLR :: (forall t. (Path top t) -> SemType t top) -> (StatLR top) -> TStatL top
semStatLR lu (List_Ref p) = lu p
semStatLR lu (ListConsR hd tl) = semStatL_Cons (semStatR lu hd) (semStatLR lu tl)
semStatLR lu (ListNilR) = semStatL_Nil

semTypeR :: (forall t. (Path top t) -> SemType t top) -> (TypeR top) -> TType top
semTypeR lu (Type_Ref p) = lu p
semTypeR lu (TypeTypeVoidR) = semType_TypeVoid
semTypeR lu (TypeTypePrimR ptype) = semType_TypePrim ptype
semTypeR lu (TypeTypeObjR otype) = semType_TypeObj otype
semTypeR lu (TypeTypeArrayR itype) = semType_TypeArray (semTypeR lu itype)

-- Production semantic functions
semClass_ClassC :: forall top. String -> (TMemberL top) -> TClass top
semClass_ClassC _name _members = TClassClassC {
                                   tclass_lookup = lookup,
                                   tclass_change = change,
                                   tclass_v0 = v0,
                                   tclass_v0_dirty = True,
                                   tclass_members = _members
                                 } where
  lookup :: forall t. (TClass top) -> (Path Class t) -> SemType t top
  lookup cur End = tickAG cur
  lookup cur (ClassClassCP_members ps) = tickAG (tmemberl_lookup (tclass_members cur) (tclass_members cur) ps)
  change :: forall r. (TClass top) -> (forall t. (Path top t) -> SemType t top) -> (Path Class r) -> (ReplType r top) -> TClass top
  change cur lu End repl = tickAG (semClassR lu repl)
  change cur lu (ClassClassCP_members ps) repl = tickAG (update_members ps (cur {
                                                                              tclass_members = tmemberl_change (tclass_members cur) (tclass_members cur) lu ps repl
                                                                            }))
  update :: (TClass top) -> TClass top
  update cur = tickAG (cur {
                         tclass_v0_dirty = tclass_v0_dirty cur || tmemberl_v0_dirty (tclass_members cur)
                       })
  update_members :: (Path f t) -> (TClass top) -> TClass top
  update_members End cur = tickAG (cur {
                                     tclass_v0_dirty = True
                                   })
  update_members _ cur = tickAG (update cur)
  v0 :: (TClass top) -> (Code, TClass top)
  v0 cur = tickAG (_lhsOcode, res) where
    (_lhsOcode, members) = tickAG (realv0 (tclass_members cur))
    res = tickAG (update (cur {
                            tclass_v0 = memv0,
                            tclass_v0_dirty = False,
                            tclass_members = members
                          }))
    memv0 :: (TClass top) -> (Code, TClass top)
    memv0 cur' = tickAG (if not (tclass_v0_dirty cur')
                         then (_lhsOcode, cur')
                         else v0 cur')
  realv0 :: (TMemberL top) -> (Code, TMemberL top)
  realv0 members0 = (_lhsOcode, members1) where
    (_membersIcode, members1) = tmemberl_v0 members0 members0
    _lhsOcode = tickSem ([ Bsr "Main" , HALT ] ++ _membersIcode)

semConst_ConstInt :: forall top. Int -> TConst top
semConst_ConstInt _val = TConstConstInt {
                           tconst_lookup = lookup,
                           tconst_change = change,
                           tconst_v0 = v0,
                           tconst_v0_dirty = True
                         } where
  lookup :: forall t. (TConst top) -> (Path Const t) -> SemType t top
  lookup cur End = tickAG cur
  change :: forall r. (TConst top) -> (forall t. (Path top t) -> SemType t top) -> (Path Const r) -> (ReplType r top) -> TConst top
  change cur lu End repl = tickAG (semConstR lu repl)
  update :: (TConst top) -> TConst top
  update cur = tickAG cur
  v0 :: (TConst top) -> (forall t. (Path Const t) -> Path Stat t) -> ((Code, Const, ConstR Stat), TConst top)
  v0 cur pStat_copy = tickAG ((_lhsOcode, _lhsOcopy, _lhsOcopyRStat), res) where
    (_lhsOcode, _lhsOcopy, _lhsOcopyRStat) = tickAG (realv0 () pStat_copy)
    res = tickAG (update (cur {
                            tconst_v0 = memv0,
                            tconst_v0_dirty = False
                          }))
    memv0 :: (TConst top) -> (forall t. (Path Const t) -> Path Stat t) -> ((Code, Const, ConstR Stat), TConst top)
    memv0 cur' pStat_copy' = tickAG (if not (tconst_v0_dirty cur')
                                     then ((_lhsOcode, _lhsOcopy, Const_Ref (pStat_copy End)), cur')
                                     else v0 cur' pStat_copy')
  realv0 :: () -> (forall t. (Path Const t) -> Path Stat t) -> (Code, Const, ConstR Stat)
  realv0 () pStat_copy = (_lhsOcode, _lhsOcopy, _lhsOcopyRStat) where
    _loc_copy = tickSem (ConstInt _val)
    _loc_copyRStat = ConstConstIntR _val
    _lhsOcopy = tickSem _loc_copy
    _lhsOcopyRStat = _loc_copyRStat
    _lhsOcode = tickSem ([ LDC _val ])

semConst_ConstBool :: forall top. Bool -> TConst top
semConst_ConstBool _val = TConstConstBool {
                            tconst_lookup = lookup,
                            tconst_change = change,
                            tconst_v0 = v0,
                            tconst_v0_dirty = True
                          } where
  lookup :: forall t. (TConst top) -> (Path Const t) -> SemType t top
  lookup cur End = tickAG cur
  change :: forall r. (TConst top) -> (forall t. (Path top t) -> SemType t top) -> (Path Const r) -> (ReplType r top) -> TConst top
  change cur lu End repl = tickAG (semConstR lu repl)
  update :: (TConst top) -> TConst top
  update cur = tickAG cur
  v0 :: (TConst top) -> (forall t. (Path Const t) -> Path Stat t) -> ((Code, Const, ConstR Stat), TConst top)
  v0 cur pStat_copy = tickAG ((_lhsOcode, _lhsOcopy, _lhsOcopyRStat), res) where
    (_lhsOcode, _lhsOcopy, _lhsOcopyRStat) = tickAG (realv0 () pStat_copy)
    res = tickAG (update (cur {
                            tconst_v0 = memv0,
                            tconst_v0_dirty = False
                          }))
    memv0 :: (TConst top) -> (forall t. (Path Const t) -> Path Stat t) -> ((Code, Const, ConstR Stat), TConst top)
    memv0 cur' pStat_copy' = tickAG (if not (tconst_v0_dirty cur')
                                     then ((_lhsOcode, _lhsOcopy, Const_Ref (pStat_copy End)), cur')
                                     else v0 cur' pStat_copy')
  realv0 :: () -> (forall t. (Path Const t) -> Path Stat t) -> (Code, Const, ConstR Stat)
  realv0 () pStat_copy = (_lhsOcode, _lhsOcopy, _lhsOcopyRStat) where
    _loc_copy = tickSem (ConstBool _val)
    _loc_copyRStat = ConstConstBoolR _val
    _lhsOcopy = tickSem _loc_copy
    _lhsOcopyRStat = _loc_copyRStat
    _lhsOcode = tickSem ([ LDC ( if _val then 1 else 0 ) ])

semConst_ConstChar :: forall top. Char -> TConst top
semConst_ConstChar _val = TConstConstChar {
                            tconst_lookup = lookup,
                            tconst_change = change,
                            tconst_v0 = v0,
                            tconst_v0_dirty = True
                          } where
  lookup :: forall t. (TConst top) -> (Path Const t) -> SemType t top
  lookup cur End = tickAG cur
  change :: forall r. (TConst top) -> (forall t. (Path top t) -> SemType t top) -> (Path Const r) -> (ReplType r top) -> TConst top
  change cur lu End repl = tickAG (semConstR lu repl)
  update :: (TConst top) -> TConst top
  update cur = tickAG cur
  v0 :: (TConst top) -> (forall t. (Path Const t) -> Path Stat t) -> ((Code, Const, ConstR Stat), TConst top)
  v0 cur pStat_copy = tickAG ((_lhsOcode, _lhsOcopy, _lhsOcopyRStat), res) where
    (_lhsOcode, _lhsOcopy, _lhsOcopyRStat) = tickAG (realv0 () pStat_copy)
    res = tickAG (update (cur {
                            tconst_v0 = memv0,
                            tconst_v0_dirty = False
                          }))
    memv0 :: (TConst top) -> (forall t. (Path Const t) -> Path Stat t) -> ((Code, Const, ConstR Stat), TConst top)
    memv0 cur' pStat_copy' = tickAG (if not (tconst_v0_dirty cur')
                                     then ((_lhsOcode, _lhsOcopy, Const_Ref (pStat_copy End)), cur')
                                     else v0 cur' pStat_copy')
  realv0 :: () -> (forall t. (Path Const t) -> Path Stat t) -> (Code, Const, ConstR Stat)
  realv0 () pStat_copy = (_lhsOcode, _lhsOcopy, _lhsOcopyRStat) where
    _loc_copy = tickSem (ConstChar _val)
    _loc_copyRStat = ConstConstCharR _val
    _lhsOcopy = tickSem _loc_copy
    _lhsOcopyRStat = _loc_copyRStat
    _lhsOcode = tickSem ([ LDC ( ord _val ) ])

semDecl_DeclC :: forall top. (TType top) -> String -> TDecl top
semDecl_DeclC _vtype _name = TDeclDeclC {
                               tdecl_lookup = lookup,
                               tdecl_change = change,
                               tdecl_v0 = v0,
                               tdecl_v1 = v1,
                               tdecl_v0_dirty = True,
                               tdecl_v1_dirty = True,
                               tdecl_vtype = _vtype
                             } where
  lookup :: forall t. (TDecl top) -> (Path Decl t) -> SemType t top
  lookup cur End = tickAG cur
  lookup cur (DeclDeclCP_vtype ps) = tickAG (ttype_lookup (tdecl_vtype cur) (tdecl_vtype cur) ps)
  change :: forall r. (TDecl top) -> (forall t. (Path top t) -> SemType t top) -> (Path Decl r) -> (ReplType r top) -> TDecl top
  change cur lu End repl = tickAG (semDeclR lu repl)
  change cur lu (DeclDeclCP_vtype ps) repl = tickAG (update_vtype ps (cur {
                                                                        tdecl_vtype = ttype_change (tdecl_vtype cur) (tdecl_vtype cur) lu ps repl
                                                                      }))
  update :: (TDecl top) -> TDecl top
  update cur = tickAG (cur {
                         tdecl_v0_dirty = tdecl_v0_dirty cur || ttype_v0_dirty (tdecl_vtype cur)
                       })
  update_vtype :: (Path f t) -> (TDecl top) -> TDecl top
  update_vtype End cur = tickAG (cur {
                                   tdecl_v0_dirty = True,
                                   tdecl_v1_dirty = True
                                 })
  update_vtype _ cur = tickAG (update cur)
  v0 :: (TDecl top) -> (forall t. (Path Decl t) -> Path Stat t) -> ((Decl, DeclR Stat, [String]), TDecl top)
  v0 cur pStat_copy = tickAG ((_lhsOcopy, _lhsOcopyRStat, _lhsOdeclVars), res) where
    ((_lhsOcopy, _lhsOcopyRStat, _lhsOdeclVars), vtype) = tickAG (realv0 (tdecl_vtype cur) pStat_copy)
    res = tickAG (update (cur {
                            tdecl_v0 = memv0,
                            tdecl_v0_dirty = False,
                            tdecl_vtype = vtype
                          }))
    memv0 :: (TDecl top) -> (forall t. (Path Decl t) -> Path Stat t) -> ((Decl, DeclR Stat, [String]), TDecl top)
    memv0 cur' pStat_copy' = tickAG (if not (tdecl_v0_dirty cur')
                                     then ((_lhsOcopy, Decl_Ref (pStat_copy End), _lhsOdeclVars), cur')
                                     else v0 cur' pStat_copy')
  v1 :: (TDecl top) -> (Map String Int) -> (Code, TDecl top)
  v1 cur inh = tickAG (_lhsOcode, res) where
    (_lhsOcode, vtype) = tickAG (realv1 (tdecl_vtype cur) inh)
    res = tickAG (update (cur {
                            tdecl_v1 = memv1,
                            tdecl_v1_dirty = False,
                            tdecl_vtype = vtype
                          }))
    memv1 :: (TDecl top) -> (Map String Int) -> (Code, TDecl top)
    memv1 cur' inh' = tickAG (if tickEQ (inh == inh') && not (tdecl_v1_dirty cur')
                              then (_lhsOcode, cur')
                              else v1 cur' inh')
  realv0 :: (TType top) -> (forall t. (Path Decl t) -> Path Stat t) -> ((Decl, DeclR Stat, [String]), TType top)
  realv0 vtype0 pStat_copy = ((_lhsOcopy, _lhsOcopyRStat, _lhsOdeclVars), vtype1) where
    _lhsOdeclVars = tickSem ([ _name ])
    ((_vtypeIcopy, _vtypeIcopyRStat), vtype1) = ttype_v0 vtype0 vtype0 (pStat_copy . DeclDeclCP_vtype . id)
    _loc_copy = tickSem (DeclC _vtypeIcopy _name)
    _loc_copyRStat = DeclDeclCR _vtypeIcopyRStat _name
    _lhsOcopy = tickSem _loc_copy
    _lhsOcopyRStat = _loc_copyRStat
  realv1 :: (TType top) -> (Map String Int) -> (Code, TType top)
  realv1 vtype1 _lhsIenv = (_lhsOcode, vtype1) where
    _lhsOcode = tickSem []

semDecl_DeclInit :: forall top. (TType top) -> String -> (TExpr top) -> TDecl top
semDecl_DeclInit _vtype _name _init = TDeclDeclInit {
                                        tdecl_lookup = lookup,
                                        tdecl_change = change,
                                        tdecl_v0 = v0,
                                        tdecl_v1 = v1,
                                        tdecl_v0_dirty = True,
                                        tdecl_v1_dirty = True,
                                        tdecl_vtype = _vtype,
                                        tdecl_init = _init,
                                        tdecl_stat = Nothing,
                                        tdecl_init_copy = undefined,
                                        tdecl_init_copyRStat = undefined
                                      } where
  lookup :: forall t. (TDecl top) -> (Path Decl t) -> SemType t top
  lookup cur End = tickAG cur
  lookup cur (DeclDeclInitP_vtype ps) = tickAG (ttype_lookup (tdecl_vtype cur) (tdecl_vtype cur) ps)
  lookup cur (DeclDeclInitP_init ps) = tickAG (texpr_lookup (tdecl_init cur) (tdecl_init cur) ps)
  change :: forall r. (TDecl top) -> (forall t. (Path top t) -> SemType t top) -> (Path Decl r) -> (ReplType r top) -> TDecl top
  change cur lu End repl = tickAG (semDeclR lu repl)
  change cur lu (DeclDeclInitP_vtype ps) repl = tickAG (update_vtype ps (cur {
                                                                           tdecl_vtype = ttype_change (tdecl_vtype cur) (tdecl_vtype cur) lu ps repl
                                                                         }))
  change cur lu (DeclDeclInitP_init ps) repl = tickAG (update_init ps (cur {
                                                                         tdecl_init = texpr_change (tdecl_init cur) (tdecl_init cur) lu ps repl
                                                                       }))
  update :: (TDecl top) -> TDecl top
  update cur = tickAG (cur {
                         tdecl_v0_dirty = tdecl_v0_dirty cur || ttype_v0_dirty (tdecl_vtype cur) || texpr_v0_dirty (tdecl_init cur),
                         tdecl_v1_dirty = tdecl_v1_dirty cur
                       })
  update_vtype :: (Path f t) -> (TDecl top) -> TDecl top
  update_vtype End cur = tickAG (cur {
                                   tdecl_v0_dirty = True,
                                   tdecl_v1_dirty = True
                                 })
  update_vtype _ cur = tickAG (update cur)
  update_init :: (Path f t) -> (TDecl top) -> TDecl top
  update_init End cur = tickAG (cur {
                                  tdecl_v0_dirty = True,
                                  tdecl_v1_dirty = True
                                })
  update_init _ cur = tickAG (update cur)
  v0 :: (TDecl top) -> (forall t. (Path Decl t) -> Path Stat t) -> ((Decl, DeclR Stat, [String]), TDecl top)
  v0 cur pStat_copy = tickAG ((_lhsOcopy, _lhsOcopyRStat, _lhsOdeclVars), res) where
    ((_lhsOcopy, _lhsOcopyRStat, _lhsOdeclVars), vtype, init, _initIcopy, _initIcopyRStat) = tickAG (realv0 (tdecl_vtype cur, tdecl_init cur) pStat_copy)
    res = tickAG (update (cur {
                            tdecl_v0 = memv0,
                            tdecl_v0_dirty = False,
                            tdecl_vtype = vtype,
                            tdecl_init = init,
                            tdecl_init_copy = _initIcopy,
                            tdecl_init_copyRStat = _initIcopyRStat
                          }))
    memv0 :: (TDecl top) -> (forall t. (Path Decl t) -> Path Stat t) -> ((Decl, DeclR Stat, [String]), TDecl top)
    memv0 cur' pStat_copy' = tickAG (if not (tdecl_v0_dirty cur')
                                     then ((_lhsOcopy, Decl_Ref (pStat_copy End), _lhsOdeclVars), cur')
                                     else v0 cur' pStat_copy')
  v1 :: (TDecl top) -> (Map String Int) -> (Code, TDecl top)
  v1 cur inh = tickAG (_lhsOcode, res) where
    (_lhsOcode, stat, vtype, init) = tickAG (realv1 (tdecl_stat cur, tdecl_vtype cur, tdecl_init cur) inh (tdecl_init_copy cur) (tdecl_init_copyRStat cur))
    res = tickAG (update (cur {
                            tdecl_v1 = memv1,
                            tdecl_v1_dirty = False,
                            tdecl_stat = Just stat,
                            tdecl_vtype = vtype,
                            tdecl_init = init
                          }))
    memv1 :: (TDecl top) -> (Map String Int) -> (Code, TDecl top)
    memv1 cur' inh' = tickAG (if tickEQ (inh == inh') && not (tdecl_v1_dirty cur')
                              then (_lhsOcode, cur')
                              else v1 cur' inh')
  realv0 :: (TType top, TExpr top) -> (forall t. (Path Decl t) -> Path Stat t) -> ((Decl, DeclR Stat, [String]), TType top, TExpr top, Expr, ExprR Stat)
  realv0 (vtype0, init0) pStat_copy = ((_lhsOcopy, _lhsOcopyRStat, _lhsOdeclVars), vtype1, init1, _initIcopy, _initIcopyRStat) where
    _lhsOdeclVars = tickSem ([ _name ])
    ((_vtypeIcopy, _vtypeIcopyRStat), vtype1) = ttype_v0 vtype0 vtype0 (pStat_copy . DeclDeclInitP_vtype . id)
    ((_initIcopy, _initIcopyRStat), init1) = texpr_v0 init0 init0 (pStat_copy . DeclDeclInitP_init . id)
    _loc_copy = tickSem (DeclInit _vtypeIcopy _name _initIcopy)
    _loc_copyRStat = DeclDeclInitR _vtypeIcopyRStat _name _initIcopyRStat
    _lhsOcopy = tickSem _loc_copy
    _lhsOcopyRStat = _loc_copyRStat
  realv1 :: (Maybe (TStat Stat), TType top, TExpr top) -> (Map String Int) -> Expr -> (ExprR Stat) -> (Code, TStat Stat, TType top, TExpr top)
  realv1 (_stat, vtype1, init1) _lhsIenv _initIcopy _initIcopyRStat = (_lhsOcode, stat2, vtype1, init1) where
    _loc_inst_stat = tickSem (StatExpr ( ExprOper "=" ( ExprVar _name ) _initIcopy ))
    _loc_inst_statRStat = StatStatExprR (ExprExprOperR "=" (ExprExprVarR _name) _initIcopyRStat)
    stat0 = case _stat of
              (Nothing) -> semStat _loc_inst_stat
              (Just v) -> tstat_change v v (tstat_lookup v v) End _loc_inst_statRStat
    ((_statIcopy, _statIcopyRStat, _statIdeclVars), stat1) = tstat_v0 stat0 stat0 undefined
    _statOenv = tickSem _lhsIenv
    (_statIcode, stat2) = tstat_v1 stat1 stat1 (_statOenv)
    _lhsOcode = tickSem _statIcode

semDeclL_Cons :: forall top. (TDecl top) -> (TDeclL top) -> TDeclL top
semDeclL_Cons _hd _tl = TDeclLCons {
                          tdecll_lookup = lookup,
                          tdecll_change = change,
                          tdecll_v0 = v0,
                          tdecll_v0_dirty = True,
                          tdecll_hd = _hd,
                          tdecll_tl = _tl
                        } where
  lookup :: forall t. (TDeclL top) -> (Path DeclL t) -> SemType t top
  lookup cur End = tickAG cur
  lookup cur (PathL_hd ps) = tickAG (tdecl_lookup (tdecll_hd cur) (tdecll_hd cur) ps)
  lookup cur (PathL_tl ps) = tickAG (tdecll_lookup (tdecll_tl cur) (tdecll_tl cur) ps)
  change :: forall r. (TDeclL top) -> (forall t. (Path top t) -> SemType t top) -> (Path DeclL r) -> (ReplType r top) -> TDeclL top
  change cur lu End repl = tickAG (semDeclLR lu repl)
  change cur lu (PathL_hd ps) repl = tickAG (update_hd ps (cur {
                                                             tdecll_hd = tdecl_change (tdecll_hd cur) (tdecll_hd cur) lu ps repl
                                                           }))
  change cur lu (PathL_tl ps) repl = tickAG (update_tl ps (cur {
                                                             tdecll_tl = tdecll_change (tdecll_tl cur) (tdecll_tl cur) lu ps repl
                                                           }))
  update :: (TDeclL top) -> TDeclL top
  update cur = tickAG (cur {
                         tdecll_v0_dirty = tdecll_v0_dirty cur || tdecll_v0_dirty (tdecll_tl cur) || tdecl_v0_dirty (tdecll_hd cur) || tdecl_v1_dirty (tdecll_hd cur)
                       })
  update_hd :: (Path f t) -> (TDeclL top) -> TDeclL top
  update_hd End cur = tickAG (cur {
                                tdecll_v0_dirty = True
                              })
  update_hd _ cur = tickAG (update cur)
  update_tl :: (Path f t) -> (TDeclL top) -> TDeclL top
  update_tl End cur = tickAG (cur {
                                tdecll_v0_dirty = True
                              })
  update_tl _ cur = tickAG (update cur)
  v0 :: (TDeclL top) -> ((Code, [String], Int), TDeclL top)
  v0 cur = tickAG ((_lhsOcode, _lhsOdeclVars, _lhsOlength), res) where
    ((_lhsOcode, _lhsOdeclVars, _lhsOlength), hd, tl) = tickAG (realv0 (tdecll_hd cur, tdecll_tl cur))
    res = tickAG (update (cur {
                            tdecll_v0 = memv0,
                            tdecll_v0_dirty = False,
                            tdecll_hd = hd,
                            tdecll_tl = tl
                          }))
    memv0 :: (TDeclL top) -> ((Code, [String], Int), TDeclL top)
    memv0 cur' = tickAG (if not (tdecll_v0_dirty cur')
                         then ((_lhsOcode, _lhsOdeclVars, _lhsOlength), cur')
                         else v0 cur')
  realv0 :: (TDecl top, TDeclL top) -> ((Code, [String], Int), TDecl top, TDeclL top)
  realv0 (hd0, tl0) = ((_lhsOcode, _lhsOdeclVars, _lhsOlength), hd2, tl1) where
    ((_tlIcode, _tlIdeclVars, _tlIlength), tl1) = tdecll_v0 tl0 tl0
    _lhsOlength = tickSem (1 + _tlIlength)
    ((_hdIcopy, _hdIcopyRStat, _hdIdeclVars), hd1) = tdecl_v0 hd0 hd0 undefined
    _lhsOdeclVars = tickSem (_hdIdeclVars ++ _tlIdeclVars)
    _hdOenv = tickSem empty
    (_hdIcode, hd2) = tdecl_v1 hd1 hd1 (_hdOenv)
    _lhsOcode = tickSem (_hdIcode ++ _tlIcode)

semDeclL_Nil :: forall top. TDeclL top
semDeclL_Nil = TDeclLNil {
                 tdecll_lookup = lookup,
                 tdecll_change = change,
                 tdecll_v0 = v0,
                 tdecll_v0_dirty = True
               } where
  lookup :: forall t. (TDeclL top) -> (Path DeclL t) -> SemType t top
  lookup cur End = tickAG cur
  change :: forall r. (TDeclL top) -> (forall t. (Path top t) -> SemType t top) -> (Path DeclL r) -> (ReplType r top) -> TDeclL top
  change cur lu End repl = tickAG (semDeclLR lu repl)
  update :: (TDeclL top) -> TDeclL top
  update cur = tickAG cur
  v0 :: (TDeclL top) -> ((Code, [String], Int), TDeclL top)
  v0 cur = tickAG ((_lhsOcode, _lhsOdeclVars, _lhsOlength), res) where
    (_lhsOcode, _lhsOdeclVars, _lhsOlength) = tickAG (realv0 ())
    res = tickAG (update (cur {
                            tdecll_v0 = memv0,
                            tdecll_v0_dirty = False
                          }))
    memv0 :: (TDeclL top) -> ((Code, [String], Int), TDeclL top)
    memv0 cur' = tickAG (if not (tdecll_v0_dirty cur')
                         then ((_lhsOcode, _lhsOdeclVars, _lhsOlength), cur')
                         else v0 cur')
  realv0 :: () -> (Code, [String], Int)
  realv0 () = (_lhsOcode, _lhsOdeclVars, _lhsOlength) where
    _lhsOlength = tickSem 0
    _lhsOdeclVars = tickSem []
    _lhsOcode = tickSem []

semExpr_ExprConst :: forall top. (TConst top) -> TExpr top
semExpr_ExprConst _const = TExprExprConst {
                             texpr_lookup = lookup,
                             texpr_change = change,
                             texpr_v0 = v0,
                             texpr_v1 = v1,
                             texpr_v0_dirty = True,
                             texpr_v1_dirty = True,
                             texpr_const = _const,
                             texpr_const_code = undefined
                           } where
  lookup :: forall t. (TExpr top) -> (Path Expr t) -> SemType t top
  lookup cur End = tickAG cur
  lookup cur (ExprExprConstP_const ps) = tickAG (tconst_lookup (texpr_const cur) (texpr_const cur) ps)
  change :: forall r. (TExpr top) -> (forall t. (Path top t) -> SemType t top) -> (Path Expr r) -> (ReplType r top) -> TExpr top
  change cur lu End repl = tickAG (semExprR lu repl)
  change cur lu (ExprExprConstP_const ps) repl = tickAG (update_const ps (cur {
                                                                            texpr_const = tconst_change (texpr_const cur) (texpr_const cur) lu ps repl
                                                                          }))
  update :: (TExpr top) -> TExpr top
  update cur = tickAG (cur {
                         texpr_v0_dirty = texpr_v0_dirty cur || tconst_v0_dirty (texpr_const cur)
                       })
  update_const :: (Path f t) -> (TExpr top) -> TExpr top
  update_const End cur = tickAG (cur {
                                   texpr_v0_dirty = True,
                                   texpr_v1_dirty = True
                                 })
  update_const _ cur = tickAG (update cur)
  v0 :: (TExpr top) -> (forall t. (Path Expr t) -> Path Stat t) -> ((Expr, ExprR Stat), TExpr top)
  v0 cur pStat_copy = tickAG ((_lhsOcopy, _lhsOcopyRStat), res) where
    ((_lhsOcopy, _lhsOcopyRStat), const, _constIcode) = tickAG (realv0 (texpr_const cur) pStat_copy)
    res = tickAG (update (cur {
                            texpr_v0 = memv0,
                            texpr_v0_dirty = False,
                            texpr_const = const,
                            texpr_const_code = _constIcode
                          }))
    memv0 :: (TExpr top) -> (forall t. (Path Expr t) -> Path Stat t) -> ((Expr, ExprR Stat), TExpr top)
    memv0 cur' pStat_copy' = tickAG (if not (texpr_v0_dirty cur')
                                     then ((_lhsOcopy, Expr_Ref (pStat_copy End)), cur')
                                     else v0 cur' pStat_copy')
  v1 :: (TExpr top) -> (Map String Int) -> ((Code, Code), TExpr top)
  v1 cur inh = tickAG ((_lhsOaddress, _lhsOcode), res) where
    ((_lhsOaddress, _lhsOcode), const) = tickAG (realv1 (texpr_const cur) inh (texpr_const_code cur))
    res = tickAG (update (cur {
                            texpr_v1 = memv1,
                            texpr_v1_dirty = False,
                            texpr_const = const
                          }))
    memv1 :: (TExpr top) -> (Map String Int) -> ((Code, Code), TExpr top)
    memv1 cur' inh' = tickAG (if tickEQ (inh == inh') && not (texpr_v1_dirty cur')
                              then ((_lhsOaddress, _lhsOcode), cur')
                              else v1 cur' inh')
  realv0 :: (TConst top) -> (forall t. (Path Expr t) -> Path Stat t) -> ((Expr, ExprR Stat), TConst top, Code)
  realv0 const0 pStat_copy = ((_lhsOcopy, _lhsOcopyRStat), const1, _constIcode) where
    ((_constIcode, _constIcopy, _constIcopyRStat), const1) = tconst_v0 const0 const0 (pStat_copy . ExprExprConstP_const . id)
    _loc_copy = tickSem (ExprConst _constIcopy)
    _loc_copyRStat = ExprExprConstR _constIcopyRStat
    _lhsOcopy = tickSem _loc_copy
    _lhsOcopyRStat = _loc_copyRStat
  realv1 :: (TConst top) -> (Map String Int) -> Code -> ((Code, Code), TConst top)
  realv1 const1 _lhsIenv _constIcode = ((_lhsOaddress, _lhsOcode), const1) where
    _lhsOcode = tickSem _constIcode
    _lhsOaddress = tickSem (error "Not a valid expression")

semExpr_ExprVar :: forall top. String -> TExpr top
semExpr_ExprVar _name = TExprExprVar {
                          texpr_lookup = lookup,
                          texpr_change = change,
                          texpr_v0 = v0,
                          texpr_v1 = v1,
                          texpr_v0_dirty = True,
                          texpr_v1_dirty = True
                        } where
  lookup :: forall t. (TExpr top) -> (Path Expr t) -> SemType t top
  lookup cur End = tickAG cur
  change :: forall r. (TExpr top) -> (forall t. (Path top t) -> SemType t top) -> (Path Expr r) -> (ReplType r top) -> TExpr top
  change cur lu End repl = tickAG (semExprR lu repl)
  update :: (TExpr top) -> TExpr top
  update cur = tickAG cur
  v0 :: (TExpr top) -> (forall t. (Path Expr t) -> Path Stat t) -> ((Expr, ExprR Stat), TExpr top)
  v0 cur pStat_copy = tickAG ((_lhsOcopy, _lhsOcopyRStat), res) where
    (_lhsOcopy, _lhsOcopyRStat) = tickAG (realv0 () pStat_copy)
    res = tickAG (update (cur {
                            texpr_v0 = memv0,
                            texpr_v0_dirty = False
                          }))
    memv0 :: (TExpr top) -> (forall t. (Path Expr t) -> Path Stat t) -> ((Expr, ExprR Stat), TExpr top)
    memv0 cur' pStat_copy' = tickAG (if not (texpr_v0_dirty cur')
                                     then ((_lhsOcopy, Expr_Ref (pStat_copy End)), cur')
                                     else v0 cur' pStat_copy')
  v1 :: (TExpr top) -> (Map String Int) -> ((Code, Code), TExpr top)
  v1 cur inh = tickAG ((_lhsOaddress, _lhsOcode), res) where
    (_lhsOaddress, _lhsOcode) = tickAG (realv1 () inh)
    res = tickAG (update (cur {
                            texpr_v1 = memv1,
                            texpr_v1_dirty = False
                          }))
    memv1 :: (TExpr top) -> (Map String Int) -> ((Code, Code), TExpr top)
    memv1 cur' inh' = tickAG (if tickEQ (inh == inh') && not (texpr_v1_dirty cur')
                              then ((_lhsOaddress, _lhsOcode), cur')
                              else v1 cur' inh')
  realv0 :: () -> (forall t. (Path Expr t) -> Path Stat t) -> (Expr, ExprR Stat)
  realv0 () pStat_copy = (_lhsOcopy, _lhsOcopyRStat) where
    _loc_copy = tickSem (ExprVar _name)
    _loc_copyRStat = ExprExprVarR _name
    _lhsOcopy = tickSem _loc_copy
    _lhsOcopyRStat = _loc_copyRStat
  realv1 :: () -> (Map String Int) -> (Code, Code)
  realv1 () _lhsIenv = (_lhsOaddress, _lhsOcode) where
    _loc_address = tickSem (findWithDefault ( error $ _name ++ " not declared." ) _name _lhsIenv)
    _lhsOcode = tickSem ([ LDL _loc_address ])
    _lhsOaddress = tickSem ([ LDLA _loc_address ])

semExpr_ExprOper :: forall top. String -> (TExpr top) -> (TExpr top) -> TExpr top
semExpr_ExprOper _op _left _right = TExprExprOper {
                                      texpr_lookup = lookup,
                                      texpr_change = change,
                                      texpr_v0 = v0,
                                      texpr_v1 = v1,
                                      texpr_v0_dirty = True,
                                      texpr_v1_dirty = True,
                                      texpr_left = _left,
                                      texpr_right = _right
                                    } where
  lookup :: forall t. (TExpr top) -> (Path Expr t) -> SemType t top
  lookup cur End = tickAG cur
  lookup cur (ExprExprOperP_left ps) = tickAG (texpr_lookup (texpr_left cur) (texpr_left cur) ps)
  lookup cur (ExprExprOperP_right ps) = tickAG (texpr_lookup (texpr_right cur) (texpr_right cur) ps)
  change :: forall r. (TExpr top) -> (forall t. (Path top t) -> SemType t top) -> (Path Expr r) -> (ReplType r top) -> TExpr top
  change cur lu End repl = tickAG (semExprR lu repl)
  change cur lu (ExprExprOperP_left ps) repl = tickAG (update_left ps (cur {
                                                                         texpr_left = texpr_change (texpr_left cur) (texpr_left cur) lu ps repl
                                                                       }))
  change cur lu (ExprExprOperP_right ps) repl = tickAG (update_right ps (cur {
                                                                           texpr_right = texpr_change (texpr_right cur) (texpr_right cur) lu ps repl
                                                                         }))
  update :: (TExpr top) -> TExpr top
  update cur = tickAG (cur {
                         texpr_v0_dirty = texpr_v0_dirty cur || texpr_v0_dirty (texpr_left cur) || texpr_v0_dirty (texpr_right cur),
                         texpr_v1_dirty = texpr_v1_dirty cur || texpr_v1_dirty (texpr_left cur) || texpr_v1_dirty (texpr_right cur)
                       })
  update_left :: (Path f t) -> (TExpr top) -> TExpr top
  update_left End cur = tickAG (cur {
                                  texpr_v0_dirty = True,
                                  texpr_v1_dirty = True
                                })
  update_left _ cur = tickAG (update cur)
  update_right :: (Path f t) -> (TExpr top) -> TExpr top
  update_right End cur = tickAG (cur {
                                   texpr_v0_dirty = True,
                                   texpr_v1_dirty = True
                                 })
  update_right _ cur = tickAG (update cur)
  v0 :: (TExpr top) -> (forall t. (Path Expr t) -> Path Stat t) -> ((Expr, ExprR Stat), TExpr top)
  v0 cur pStat_copy = tickAG ((_lhsOcopy, _lhsOcopyRStat), res) where
    ((_lhsOcopy, _lhsOcopyRStat), left, right) = tickAG (realv0 (texpr_left cur, texpr_right cur) pStat_copy)
    res = tickAG (update (cur {
                            texpr_v0 = memv0,
                            texpr_v0_dirty = False,
                            texpr_left = left,
                            texpr_right = right
                          }))
    memv0 :: (TExpr top) -> (forall t. (Path Expr t) -> Path Stat t) -> ((Expr, ExprR Stat), TExpr top)
    memv0 cur' pStat_copy' = tickAG (if not (texpr_v0_dirty cur')
                                     then ((_lhsOcopy, Expr_Ref (pStat_copy End)), cur')
                                     else v0 cur' pStat_copy')
  v1 :: (TExpr top) -> (Map String Int) -> ((Code, Code), TExpr top)
  v1 cur inh = tickAG ((_lhsOaddress, _lhsOcode), res) where
    ((_lhsOaddress, _lhsOcode), left, right) = tickAG (realv1 (texpr_left cur, texpr_right cur) inh)
    res = tickAG (update (cur {
                            texpr_v1 = memv1,
                            texpr_v1_dirty = False,
                            texpr_left = left,
                            texpr_right = right
                          }))
    memv1 :: (TExpr top) -> (Map String Int) -> ((Code, Code), TExpr top)
    memv1 cur' inh' = tickAG (if tickEQ (inh == inh') && not (texpr_v1_dirty cur')
                              then ((_lhsOaddress, _lhsOcode), cur')
                              else v1 cur' inh')
  realv0 :: (TExpr top, TExpr top) -> (forall t. (Path Expr t) -> Path Stat t) -> ((Expr, ExprR Stat), TExpr top, TExpr top)
  realv0 (left0, right0) pStat_copy = ((_lhsOcopy, _lhsOcopyRStat), left1, right1) where
    ((_leftIcopy, _leftIcopyRStat), left1) = texpr_v0 left0 left0 (pStat_copy . ExprExprOperP_left . id)
    ((_rightIcopy, _rightIcopyRStat), right1) = texpr_v0 right0 right0 (pStat_copy . ExprExprOperP_right . id)
    _loc_copy = tickSem (ExprOper _op _leftIcopy _rightIcopy)
    _loc_copyRStat = ExprExprOperR _op _leftIcopyRStat _rightIcopyRStat
    _lhsOcopy = tickSem _loc_copy
    _lhsOcopyRStat = _loc_copyRStat
  realv1 :: (TExpr top, TExpr top) -> (Map String Int) -> ((Code, Code), TExpr top, TExpr top)
  realv1 (left1, right1) _lhsIenv = ((_lhsOaddress, _lhsOcode), left2, right2) where
    _leftOenv = tickSem _lhsIenv
    ((_leftIaddress, _leftIcode), left2) = texpr_v1 left1 left1 (_leftOenv)
    _rightOenv = tickSem _lhsIenv
    ((_rightIaddress, _rightIcode), right2) = texpr_v1 right1 right1 (_rightOenv)
    _lhsOcode = tickSem (case _op of { "=" -> _rightIcode ++ [ LDS 0 ] ++ _leftIaddress ++ [ STA 0 ] ; op -> _leftIcode ++ _rightIcode ++ [ findWithDefault ( error "Unknown operator" ) op opCodes ] })
    _lhsOaddress = tickSem (error "Not a valid expression")

semExpr_ExprFun :: forall top. String -> (TExprL top) -> TExpr top
semExpr_ExprFun _name _params = TExprExprFun {
                                  texpr_lookup = lookup,
                                  texpr_change = change,
                                  texpr_v0 = v0,
                                  texpr_v1 = v1,
                                  texpr_v0_dirty = True,
                                  texpr_v1_dirty = True,
                                  texpr_params = _params
                                } where
  lookup :: forall t. (TExpr top) -> (Path Expr t) -> SemType t top
  lookup cur End = tickAG cur
  lookup cur (ExprExprFunP_params ps) = tickAG (texprl_lookup (texpr_params cur) (texpr_params cur) ps)
  change :: forall r. (TExpr top) -> (forall t. (Path top t) -> SemType t top) -> (Path Expr r) -> (ReplType r top) -> TExpr top
  change cur lu End repl = tickAG (semExprR lu repl)
  change cur lu (ExprExprFunP_params ps) repl = tickAG (update_params ps (cur {
                                                                            texpr_params = texprl_change (texpr_params cur) (texpr_params cur) lu ps repl
                                                                          }))
  update :: (TExpr top) -> TExpr top
  update cur = tickAG (cur {
                         texpr_v0_dirty = texpr_v0_dirty cur || texprl_v0_dirty (texpr_params cur),
                         texpr_v1_dirty = texpr_v1_dirty cur || texprl_v1_dirty (texpr_params cur)
                       })
  update_params :: (Path f t) -> (TExpr top) -> TExpr top
  update_params End cur = tickAG (cur {
                                    texpr_v0_dirty = True,
                                    texpr_v1_dirty = True
                                  })
  update_params _ cur = tickAG (update cur)
  v0 :: (TExpr top) -> (forall t. (Path Expr t) -> Path Stat t) -> ((Expr, ExprR Stat), TExpr top)
  v0 cur pStat_copy = tickAG ((_lhsOcopy, _lhsOcopyRStat), res) where
    ((_lhsOcopy, _lhsOcopyRStat), params) = tickAG (realv0 (texpr_params cur) pStat_copy)
    res = tickAG (update (cur {
                            texpr_v0 = memv0,
                            texpr_v0_dirty = False,
                            texpr_params = params
                          }))
    memv0 :: (TExpr top) -> (forall t. (Path Expr t) -> Path Stat t) -> ((Expr, ExprR Stat), TExpr top)
    memv0 cur' pStat_copy' = tickAG (if not (texpr_v0_dirty cur')
                                     then ((_lhsOcopy, Expr_Ref (pStat_copy End)), cur')
                                     else v0 cur' pStat_copy')
  v1 :: (TExpr top) -> (Map String Int) -> ((Code, Code), TExpr top)
  v1 cur inh = tickAG ((_lhsOaddress, _lhsOcode), res) where
    ((_lhsOaddress, _lhsOcode), params) = tickAG (realv1 (texpr_params cur) inh)
    res = tickAG (update (cur {
                            texpr_v1 = memv1,
                            texpr_v1_dirty = False,
                            texpr_params = params
                          }))
    memv1 :: (TExpr top) -> (Map String Int) -> ((Code, Code), TExpr top)
    memv1 cur' inh' = tickAG (if tickEQ (inh == inh') && not (texpr_v1_dirty cur')
                              then ((_lhsOaddress, _lhsOcode), cur')
                              else v1 cur' inh')
  realv0 :: (TExprL top) -> (forall t. (Path Expr t) -> Path Stat t) -> ((Expr, ExprR Stat), TExprL top)
  realv0 params0 pStat_copy = ((_lhsOcopy, _lhsOcopyRStat), params1) where
    ((_paramsIcopy, _paramsIcopyRStat), params1) = texprl_v0 params0 params0 (pStat_copy . ExprExprFunP_params . id)
    _loc_copy = tickSem (ExprFun _name _paramsIcopy)
    _loc_copyRStat = ExprExprFunR _name _paramsIcopyRStat
    _lhsOcopy = tickSem _loc_copy
    _lhsOcopyRStat = _loc_copyRStat
  realv1 :: (TExprL top) -> (Map String Int) -> ((Code, Code), TExprL top)
  realv1 params1 _lhsIenv = ((_lhsOaddress, _lhsOcode), params2) where
    _paramsOenv = tickSem _lhsIenv
    ((_paramsIcode, _paramsIlength), params2) = texprl_v1 params1 params1 (_paramsOenv)
    _loc_cleanup = tickSem (if _paramsIlength == 0 then [] else [ AJS ( - _paramsIlength ) ])
    _lhsOcode = tickSem (case _name of { "print" -> _paramsIcode ++ [ LDS 0 , TRAP 0 ] ; _ -> _paramsIcode ++ [ Bsr _name ] ++ _loc_cleanup ++ [ LDR R3 ] })
    _lhsOaddress = tickSem (error "Not a valid expression")

semExprL_Cons :: forall top. (TExpr top) -> (TExprL top) -> TExprL top
semExprL_Cons _hd _tl = TExprLCons {
                          texprl_lookup = lookup,
                          texprl_change = change,
                          texprl_v0 = v0,
                          texprl_v1 = v1,
                          texprl_v0_dirty = True,
                          texprl_v1_dirty = True,
                          texprl_hd = _hd,
                          texprl_tl = _tl
                        } where
  lookup :: forall t. (TExprL top) -> (Path ExprL t) -> SemType t top
  lookup cur End = tickAG cur
  lookup cur (PathL_hd ps) = tickAG (texpr_lookup (texprl_hd cur) (texprl_hd cur) ps)
  lookup cur (PathL_tl ps) = tickAG (texprl_lookup (texprl_tl cur) (texprl_tl cur) ps)
  change :: forall r. (TExprL top) -> (forall t. (Path top t) -> SemType t top) -> (Path ExprL r) -> (ReplType r top) -> TExprL top
  change cur lu End repl = tickAG (semExprLR lu repl)
  change cur lu (PathL_hd ps) repl = tickAG (update_hd ps (cur {
                                                             texprl_hd = texpr_change (texprl_hd cur) (texprl_hd cur) lu ps repl
                                                           }))
  change cur lu (PathL_tl ps) repl = tickAG (update_tl ps (cur {
                                                             texprl_tl = texprl_change (texprl_tl cur) (texprl_tl cur) lu ps repl
                                                           }))
  update :: (TExprL top) -> TExprL top
  update cur = tickAG (cur {
                         texprl_v0_dirty = texprl_v0_dirty cur || texpr_v0_dirty (texprl_hd cur) || texprl_v0_dirty (texprl_tl cur),
                         texprl_v1_dirty = texprl_v1_dirty cur || texprl_v1_dirty (texprl_tl cur) || texpr_v1_dirty (texprl_hd cur)
                       })
  update_hd :: (Path f t) -> (TExprL top) -> TExprL top
  update_hd End cur = tickAG (cur {
                                texprl_v0_dirty = True,
                                texprl_v1_dirty = True
                              })
  update_hd _ cur = tickAG (update cur)
  update_tl :: (Path f t) -> (TExprL top) -> TExprL top
  update_tl End cur = tickAG (cur {
                                texprl_v0_dirty = True,
                                texprl_v1_dirty = True
                              })
  update_tl _ cur = tickAG (update cur)
  v0 :: (TExprL top) -> (forall t. (Path ExprL t) -> Path Stat t) -> ((ExprL, ExprLR Stat), TExprL top)
  v0 cur pStat_copy = tickAG ((_lhsOcopy, _lhsOcopyRStat), res) where
    ((_lhsOcopy, _lhsOcopyRStat), hd, tl) = tickAG (realv0 (texprl_hd cur, texprl_tl cur) pStat_copy)
    res = tickAG (update (cur {
                            texprl_v0 = memv0,
                            texprl_v0_dirty = False,
                            texprl_hd = hd,
                            texprl_tl = tl
                          }))
    memv0 :: (TExprL top) -> (forall t. (Path ExprL t) -> Path Stat t) -> ((ExprL, ExprLR Stat), TExprL top)
    memv0 cur' pStat_copy' = tickAG (if not (texprl_v0_dirty cur')
                                     then ((_lhsOcopy, List_Ref (pStat_copy End)), cur')
                                     else v0 cur' pStat_copy')
  v1 :: (TExprL top) -> (Map String Int) -> ((Code, Int), TExprL top)
  v1 cur inh = tickAG ((_lhsOcode, _lhsOlength), res) where
    ((_lhsOcode, _lhsOlength), hd, tl) = tickAG (realv1 (texprl_hd cur, texprl_tl cur) inh)
    res = tickAG (update (cur {
                            texprl_v1 = memv1,
                            texprl_v1_dirty = False,
                            texprl_hd = hd,
                            texprl_tl = tl
                          }))
    memv1 :: (TExprL top) -> (Map String Int) -> ((Code, Int), TExprL top)
    memv1 cur' inh' = tickAG (if tickEQ (inh == inh') && not (texprl_v1_dirty cur')
                              then ((_lhsOcode, _lhsOlength), cur')
                              else v1 cur' inh')
  realv0 :: (TExpr top, TExprL top) -> (forall t. (Path ExprL t) -> Path Stat t) -> ((ExprL, ExprLR Stat), TExpr top, TExprL top)
  realv0 (hd0, tl0) pStat_copy = ((_lhsOcopy, _lhsOcopyRStat), hd1, tl1) where
    ((_hdIcopy, _hdIcopyRStat), hd1) = texpr_v0 hd0 hd0 (pStat_copy . PathL_hd . id)
    ((_tlIcopy, _tlIcopyRStat), tl1) = texprl_v0 tl0 tl0 (pStat_copy . PathL_tl . id)
    _loc_copy = tickSem ((:) _hdIcopy _tlIcopy)
    _loc_copyRStat = ListConsR _hdIcopyRStat _tlIcopyRStat
    _lhsOcopy = tickSem _loc_copy
    _lhsOcopyRStat = _loc_copyRStat
  realv1 :: (TExpr top, TExprL top) -> (Map String Int) -> ((Code, Int), TExpr top, TExprL top)
  realv1 (hd1, tl1) _lhsIenv = ((_lhsOcode, _lhsOlength), hd2, tl2) where
    _tlOenv = tickSem _lhsIenv
    ((_tlIcode, _tlIlength), tl2) = texprl_v1 tl1 tl1 (_tlOenv)
    _lhsOlength = tickSem (1 + _tlIlength)
    _hdOenv = tickSem _lhsIenv
    ((_hdIaddress, _hdIcode), hd2) = texpr_v1 hd1 hd1 (_hdOenv)
    _lhsOcode = tickSem (_hdIcode ++ _tlIcode)

semExprL_Nil :: forall top. TExprL top
semExprL_Nil = TExprLNil {
                 texprl_lookup = lookup,
                 texprl_change = change,
                 texprl_v0 = v0,
                 texprl_v1 = v1,
                 texprl_v0_dirty = True,
                 texprl_v1_dirty = True
               } where
  lookup :: forall t. (TExprL top) -> (Path ExprL t) -> SemType t top
  lookup cur End = tickAG cur
  change :: forall r. (TExprL top) -> (forall t. (Path top t) -> SemType t top) -> (Path ExprL r) -> (ReplType r top) -> TExprL top
  change cur lu End repl = tickAG (semExprLR lu repl)
  update :: (TExprL top) -> TExprL top
  update cur = tickAG cur
  v0 :: (TExprL top) -> (forall t. (Path ExprL t) -> Path Stat t) -> ((ExprL, ExprLR Stat), TExprL top)
  v0 cur pStat_copy = tickAG ((_lhsOcopy, _lhsOcopyRStat), res) where
    (_lhsOcopy, _lhsOcopyRStat) = tickAG (realv0 () pStat_copy)
    res = tickAG (update (cur {
                            texprl_v0 = memv0,
                            texprl_v0_dirty = False
                          }))
    memv0 :: (TExprL top) -> (forall t. (Path ExprL t) -> Path Stat t) -> ((ExprL, ExprLR Stat), TExprL top)
    memv0 cur' pStat_copy' = tickAG (if not (texprl_v0_dirty cur')
                                     then ((_lhsOcopy, List_Ref (pStat_copy End)), cur')
                                     else v0 cur' pStat_copy')
  v1 :: (TExprL top) -> (Map String Int) -> ((Code, Int), TExprL top)
  v1 cur inh = tickAG ((_lhsOcode, _lhsOlength), res) where
    (_lhsOcode, _lhsOlength) = tickAG (realv1 () inh)
    res = tickAG (update (cur {
                            texprl_v1 = memv1,
                            texprl_v1_dirty = False
                          }))
    memv1 :: (TExprL top) -> (Map String Int) -> ((Code, Int), TExprL top)
    memv1 cur' inh' = tickAG (if tickEQ (inh == inh') && not (texprl_v1_dirty cur')
                              then ((_lhsOcode, _lhsOlength), cur')
                              else v1 cur' inh')
  realv0 :: () -> (forall t. (Path ExprL t) -> Path Stat t) -> (ExprL, ExprLR Stat)
  realv0 () pStat_copy = (_lhsOcopy, _lhsOcopyRStat) where
    _loc_copy = tickSem []
    _loc_copyRStat = ListNilR
    _lhsOcopy = tickSem _loc_copy
    _lhsOcopyRStat = _loc_copyRStat
  realv1 :: () -> (Map String Int) -> (Code, Int)
  realv1 () _lhsIenv = (_lhsOcode, _lhsOlength) where
    _lhsOlength = tickSem 0
    _lhsOcode = tickSem []

semMember_MemberD :: forall top. (TDecl top) -> TMember top
semMember_MemberD _decl = TMemberMemberD {
                            tmember_lookup = lookup,
                            tmember_change = change,
                            tmember_v0 = v0,
                            tmember_v0_dirty = True,
                            tmember_decl = _decl
                          } where
  lookup :: forall t. (TMember top) -> (Path Member t) -> SemType t top
  lookup cur End = tickAG cur
  lookup cur (MemberMemberDP_decl ps) = tickAG (tdecl_lookup (tmember_decl cur) (tmember_decl cur) ps)
  change :: forall r. (TMember top) -> (forall t. (Path top t) -> SemType t top) -> (Path Member r) -> (ReplType r top) -> TMember top
  change cur lu End repl = tickAG (semMemberR lu repl)
  change cur lu (MemberMemberDP_decl ps) repl = tickAG (update_decl ps (cur {
                                                                          tmember_decl = tdecl_change (tmember_decl cur) (tmember_decl cur) lu ps repl
                                                                        }))
  update :: (TMember top) -> TMember top
  update cur = tickAG (cur {
                         tmember_v0_dirty = tmember_v0_dirty cur || tdecl_v0_dirty (tmember_decl cur) || tdecl_v1_dirty (tmember_decl cur)
                       })
  update_decl :: (Path f t) -> (TMember top) -> TMember top
  update_decl End cur = tickAG (cur {
                                  tmember_v0_dirty = True
                                })
  update_decl _ cur = tickAG (update cur)
  v0 :: (TMember top) -> (Code, TMember top)
  v0 cur = tickAG (_lhsOcode, res) where
    (_lhsOcode, decl) = tickAG (realv0 (tmember_decl cur))
    res = tickAG (update (cur {
                            tmember_v0 = memv0,
                            tmember_v0_dirty = False,
                            tmember_decl = decl
                          }))
    memv0 :: (TMember top) -> (Code, TMember top)
    memv0 cur' = tickAG (if not (tmember_v0_dirty cur')
                         then (_lhsOcode, cur')
                         else v0 cur')
  realv0 :: (TDecl top) -> (Code, TDecl top)
  realv0 decl0 = (_lhsOcode, decl2) where
    ((_declIcopy, _declIcopyRStat, _declIdeclVars), decl1) = tdecl_v0 decl0 decl0 undefined
    _declOenv = tickSem empty
    (_declIcode, decl2) = tdecl_v1 decl1 decl1 (_declOenv)
    _lhsOcode = tickSem _declIcode

semMember_MemberM :: forall top. (TType top) -> String -> (TDeclL top) -> (TStat top) -> TMember top
semMember_MemberM _rtype _name _params _body = TMemberMemberM {
                                                 tmember_lookup = lookup,
                                                 tmember_change = change,
                                                 tmember_v0 = v0,
                                                 tmember_v0_dirty = True,
                                                 tmember_rtype = _rtype,
                                                 tmember_params = _params,
                                                 tmember_body = _body
                                               } where
  lookup :: forall t. (TMember top) -> (Path Member t) -> SemType t top
  lookup cur End = tickAG cur
  lookup cur (MemberMemberMP_rtype ps) = tickAG (ttype_lookup (tmember_rtype cur) (tmember_rtype cur) ps)
  lookup cur (MemberMemberMP_params ps) = tickAG (tdecll_lookup (tmember_params cur) (tmember_params cur) ps)
  lookup cur (MemberMemberMP_body ps) = tickAG (tstat_lookup (tmember_body cur) (tmember_body cur) ps)
  change :: forall r. (TMember top) -> (forall t. (Path top t) -> SemType t top) -> (Path Member r) -> (ReplType r top) -> TMember top
  change cur lu End repl = tickAG (semMemberR lu repl)
  change cur lu (MemberMemberMP_rtype ps) repl = tickAG (update_rtype ps (cur {
                                                                            tmember_rtype = ttype_change (tmember_rtype cur) (tmember_rtype cur) lu ps repl
                                                                          }))
  change cur lu (MemberMemberMP_params ps) repl = tickAG (update_params ps (cur {
                                                                              tmember_params = tdecll_change (tmember_params cur) (tmember_params cur) lu ps repl
                                                                            }))
  change cur lu (MemberMemberMP_body ps) repl = tickAG (update_body ps (cur {
                                                                          tmember_body = tstat_change (tmember_body cur) (tmember_body cur) lu ps repl
                                                                        }))
  update :: (TMember top) -> TMember top
  update cur = tickAG (cur {
                         tmember_v0_dirty = tmember_v0_dirty cur || tdecll_v0_dirty (tmember_params cur) || tstat_v0_dirty (tmember_body cur) || tstat_v1_dirty (tmember_body cur)
                       })
  update_rtype :: (Path f t) -> (TMember top) -> TMember top
  update_rtype End cur = tickAG (cur {
                                   tmember_v0_dirty = True
                                 })
  update_rtype _ cur = tickAG (update cur)
  update_params :: (Path f t) -> (TMember top) -> TMember top
  update_params End cur = tickAG (cur {
                                    tmember_v0_dirty = True
                                  })
  update_params _ cur = tickAG (update cur)
  update_body :: (Path f t) -> (TMember top) -> TMember top
  update_body End cur = tickAG (cur {
                                  tmember_v0_dirty = True
                                })
  update_body _ cur = tickAG (update cur)
  v0 :: (TMember top) -> (Code, TMember top)
  v0 cur = tickAG (_lhsOcode, res) where
    (_lhsOcode, rtype, params, body) = tickAG (realv0 (tmember_rtype cur, tmember_params cur, tmember_body cur))
    res = tickAG (update (cur {
                            tmember_v0 = memv0,
                            tmember_v0_dirty = False,
                            tmember_rtype = rtype,
                            tmember_params = params,
                            tmember_body = body
                          }))
    memv0 :: (TMember top) -> (Code, TMember top)
    memv0 cur' = tickAG (if not (tmember_v0_dirty cur')
                         then (_lhsOcode, cur')
                         else v0 cur')
  realv0 :: (TType top, TDeclL top, TStat top) -> (Code, TType top, TDeclL top, TStat top)
  realv0 (rtype0, params0, body0) = (_lhsOcode, rtype0, params1, body2) where
    ((_paramsIcode, _paramsIdeclVars, _paramsIlength), params1) = tdecll_v0 params0 params0
    ((_bodyIcopy, _bodyIcopyRStat, _bodyIdeclVars), body1) = tstat_v0 body0 body0 undefined
    _loc_locs = tickSem (zip _bodyIdeclVars [ 1 .. ])
    _loc_params = tickSem (zip ( reverse _paramsIdeclVars ) [ - 2 , - 3 .. ])
    _bodyOenv = tickSem (fromList $ _loc_params ++ _loc_locs)
    (_bodyIcode, body2) = tstat_v1 body1 body1 (_bodyOenv)
    _loc_annotes = tickSem ([ ANNOTE MP n n "green" v | ( v , n ) <- ( _loc_params ++ _loc_locs ) ])
    _lhsOcode = tickSem ([ LABEL _name , LINK ( length _loc_locs ) ] ++ _loc_annotes ++ _bodyIcode ++ [ UNLINK , RET ])

semMemberL_Cons :: forall top. (TMember top) -> (TMemberL top) -> TMemberL top
semMemberL_Cons _hd _tl = TMemberLCons {
                            tmemberl_lookup = lookup,
                            tmemberl_change = change,
                            tmemberl_v0 = v0,
                            tmemberl_v0_dirty = True,
                            tmemberl_hd = _hd,
                            tmemberl_tl = _tl
                          } where
  lookup :: forall t. (TMemberL top) -> (Path MemberL t) -> SemType t top
  lookup cur End = tickAG cur
  lookup cur (PathL_hd ps) = tickAG (tmember_lookup (tmemberl_hd cur) (tmemberl_hd cur) ps)
  lookup cur (PathL_tl ps) = tickAG (tmemberl_lookup (tmemberl_tl cur) (tmemberl_tl cur) ps)
  change :: forall r. (TMemberL top) -> (forall t. (Path top t) -> SemType t top) -> (Path MemberL r) -> (ReplType r top) -> TMemberL top
  change cur lu End repl = tickAG (semMemberLR lu repl)
  change cur lu (PathL_hd ps) repl = tickAG (update_hd ps (cur {
                                                             tmemberl_hd = tmember_change (tmemberl_hd cur) (tmemberl_hd cur) lu ps repl
                                                           }))
  change cur lu (PathL_tl ps) repl = tickAG (update_tl ps (cur {
                                                             tmemberl_tl = tmemberl_change (tmemberl_tl cur) (tmemberl_tl cur) lu ps repl
                                                           }))
  update :: (TMemberL top) -> TMemberL top
  update cur = tickAG (cur {
                         tmemberl_v0_dirty = tmemberl_v0_dirty cur || tmember_v0_dirty (tmemberl_hd cur) || tmemberl_v0_dirty (tmemberl_tl cur)
                       })
  update_hd :: (Path f t) -> (TMemberL top) -> TMemberL top
  update_hd End cur = tickAG (cur {
                                tmemberl_v0_dirty = True
                              })
  update_hd _ cur = tickAG (update cur)
  update_tl :: (Path f t) -> (TMemberL top) -> TMemberL top
  update_tl End cur = tickAG (cur {
                                tmemberl_v0_dirty = True
                              })
  update_tl _ cur = tickAG (update cur)
  v0 :: (TMemberL top) -> (Code, TMemberL top)
  v0 cur = tickAG (_lhsOcode, res) where
    (_lhsOcode, hd, tl) = tickAG (realv0 (tmemberl_hd cur, tmemberl_tl cur))
    res = tickAG (update (cur {
                            tmemberl_v0 = memv0,
                            tmemberl_v0_dirty = False,
                            tmemberl_hd = hd,
                            tmemberl_tl = tl
                          }))
    memv0 :: (TMemberL top) -> (Code, TMemberL top)
    memv0 cur' = tickAG (if not (tmemberl_v0_dirty cur')
                         then (_lhsOcode, cur')
                         else v0 cur')
  realv0 :: (TMember top, TMemberL top) -> (Code, TMember top, TMemberL top)
  realv0 (hd0, tl0) = (_lhsOcode, hd1, tl1) where
    (_hdIcode, hd1) = tmember_v0 hd0 hd0
    (_tlIcode, tl1) = tmemberl_v0 tl0 tl0
    _lhsOcode = tickSem (_hdIcode ++ _tlIcode)

semMemberL_Nil :: forall top. TMemberL top
semMemberL_Nil = TMemberLNil {
                   tmemberl_lookup = lookup,
                   tmemberl_change = change,
                   tmemberl_v0 = v0,
                   tmemberl_v0_dirty = True
                 } where
  lookup :: forall t. (TMemberL top) -> (Path MemberL t) -> SemType t top
  lookup cur End = tickAG cur
  change :: forall r. (TMemberL top) -> (forall t. (Path top t) -> SemType t top) -> (Path MemberL r) -> (ReplType r top) -> TMemberL top
  change cur lu End repl = tickAG (semMemberLR lu repl)
  update :: (TMemberL top) -> TMemberL top
  update cur = tickAG cur
  v0 :: (TMemberL top) -> (Code, TMemberL top)
  v0 cur = tickAG (_lhsOcode, res) where
    _lhsOcode = tickAG (realv0 ())
    res = tickAG (update (cur {
                            tmemberl_v0 = memv0,
                            tmemberl_v0_dirty = False
                          }))
    memv0 :: (TMemberL top) -> (Code, TMemberL top)
    memv0 cur' = tickAG (if not (tmemberl_v0_dirty cur')
                         then (_lhsOcode, cur')
                         else v0 cur')
  realv0 :: () -> Code
  realv0 () = _lhsOcode where
    _lhsOcode = tickSem []

semStat_StatDecl :: forall top. (TDecl top) -> TStat top
semStat_StatDecl _decl = TStatStatDecl {
                           tstat_lookup = lookup,
                           tstat_change = change,
                           tstat_v0 = v0,
                           tstat_v1 = v1,
                           tstat_v0_dirty = True,
                           tstat_v1_dirty = True,
                           tstat_decl = _decl
                         } where
  lookup :: forall t. (TStat top) -> (Path Stat t) -> SemType t top
  lookup cur End = tickAG cur
  lookup cur (StatStatDeclP_decl ps) = tickAG (tdecl_lookup (tstat_decl cur) (tstat_decl cur) ps)
  change :: forall r. (TStat top) -> (forall t. (Path top t) -> SemType t top) -> (Path Stat r) -> (ReplType r top) -> TStat top
  change cur lu End repl = tickAG (semStatR lu repl)
  change cur lu (StatStatDeclP_decl ps) repl = tickAG (update_decl ps (cur {
                                                                         tstat_decl = tdecl_change (tstat_decl cur) (tstat_decl cur) lu ps repl
                                                                       }))
  update :: (TStat top) -> TStat top
  update cur = tickAG (cur {
                         tstat_v0_dirty = tstat_v0_dirty cur || tdecl_v0_dirty (tstat_decl cur),
                         tstat_v1_dirty = tstat_v1_dirty cur || tdecl_v1_dirty (tstat_decl cur)
                       })
  update_decl :: (Path f t) -> (TStat top) -> TStat top
  update_decl End cur = tickAG (cur {
                                  tstat_v0_dirty = True,
                                  tstat_v1_dirty = True
                                })
  update_decl _ cur = tickAG (update cur)
  v0 :: (TStat top) -> (forall t. (Path Stat t) -> Path Stat t) -> ((Stat, StatR Stat, [String]), TStat top)
  v0 cur pStat_copy = tickAG ((_lhsOcopy, _lhsOcopyRStat, _lhsOdeclVars), res) where
    ((_lhsOcopy, _lhsOcopyRStat, _lhsOdeclVars), decl) = tickAG (realv0 (tstat_decl cur) pStat_copy)
    res = tickAG (update (cur {
                            tstat_v0 = memv0,
                            tstat_v0_dirty = False,
                            tstat_decl = decl
                          }))
    memv0 :: (TStat top) -> (forall t. (Path Stat t) -> Path Stat t) -> ((Stat, StatR Stat, [String]), TStat top)
    memv0 cur' pStat_copy' = tickAG (if not (tstat_v0_dirty cur')
                                     then ((_lhsOcopy, Stat_Ref (pStat_copy End), _lhsOdeclVars), cur')
                                     else v0 cur' pStat_copy')
  v1 :: (TStat top) -> (Map String Int) -> (Code, TStat top)
  v1 cur inh = tickAG (_lhsOcode, res) where
    (_lhsOcode, decl) = tickAG (realv1 (tstat_decl cur) inh)
    res = tickAG (update (cur {
                            tstat_v1 = memv1,
                            tstat_v1_dirty = False,
                            tstat_decl = decl
                          }))
    memv1 :: (TStat top) -> (Map String Int) -> (Code, TStat top)
    memv1 cur' inh' = tickAG (if tickEQ (inh == inh') && not (tstat_v1_dirty cur')
                              then (_lhsOcode, cur')
                              else v1 cur' inh')
  realv0 :: (TDecl top) -> (forall t. (Path Stat t) -> Path Stat t) -> ((Stat, StatR Stat, [String]), TDecl top)
  realv0 decl0 pStat_copy = ((_lhsOcopy, _lhsOcopyRStat, _lhsOdeclVars), decl1) where
    ((_declIcopy, _declIcopyRStat, _declIdeclVars), decl1) = tdecl_v0 decl0 decl0 (pStat_copy . StatStatDeclP_decl . id)
    _lhsOdeclVars = tickSem _declIdeclVars
    _loc_copy = tickSem (StatDecl _declIcopy)
    _loc_copyRStat = StatStatDeclR _declIcopyRStat
    _lhsOcopy = tickSem _loc_copy
    _lhsOcopyRStat = _loc_copyRStat
  realv1 :: (TDecl top) -> (Map String Int) -> (Code, TDecl top)
  realv1 decl1 _lhsIenv = (_lhsOcode, decl2) where
    _declOenv = tickSem _lhsIenv
    (_declIcode, decl2) = tdecl_v1 decl1 decl1 (_declOenv)
    _lhsOcode = tickSem _declIcode

semStat_StatExpr :: forall top. (TExpr top) -> TStat top
semStat_StatExpr _expr = TStatStatExpr {
                           tstat_lookup = lookup,
                           tstat_change = change,
                           tstat_v0 = v0,
                           tstat_v1 = v1,
                           tstat_v0_dirty = True,
                           tstat_v1_dirty = True,
                           tstat_expr = _expr
                         } where
  lookup :: forall t. (TStat top) -> (Path Stat t) -> SemType t top
  lookup cur End = tickAG cur
  lookup cur (StatStatExprP_expr ps) = tickAG (texpr_lookup (tstat_expr cur) (tstat_expr cur) ps)
  change :: forall r. (TStat top) -> (forall t. (Path top t) -> SemType t top) -> (Path Stat r) -> (ReplType r top) -> TStat top
  change cur lu End repl = tickAG (semStatR lu repl)
  change cur lu (StatStatExprP_expr ps) repl = tickAG (update_expr ps (cur {
                                                                         tstat_expr = texpr_change (tstat_expr cur) (tstat_expr cur) lu ps repl
                                                                       }))
  update :: (TStat top) -> TStat top
  update cur = tickAG (cur {
                         tstat_v0_dirty = tstat_v0_dirty cur || texpr_v0_dirty (tstat_expr cur),
                         tstat_v1_dirty = tstat_v1_dirty cur || texpr_v1_dirty (tstat_expr cur)
                       })
  update_expr :: (Path f t) -> (TStat top) -> TStat top
  update_expr End cur = tickAG (cur {
                                  tstat_v0_dirty = True,
                                  tstat_v1_dirty = True
                                })
  update_expr _ cur = tickAG (update cur)
  v0 :: (TStat top) -> (forall t. (Path Stat t) -> Path Stat t) -> ((Stat, StatR Stat, [String]), TStat top)
  v0 cur pStat_copy = tickAG ((_lhsOcopy, _lhsOcopyRStat, _lhsOdeclVars), res) where
    ((_lhsOcopy, _lhsOcopyRStat, _lhsOdeclVars), expr) = tickAG (realv0 (tstat_expr cur) pStat_copy)
    res = tickAG (update (cur {
                            tstat_v0 = memv0,
                            tstat_v0_dirty = False,
                            tstat_expr = expr
                          }))
    memv0 :: (TStat top) -> (forall t. (Path Stat t) -> Path Stat t) -> ((Stat, StatR Stat, [String]), TStat top)
    memv0 cur' pStat_copy' = tickAG (if not (tstat_v0_dirty cur')
                                     then ((_lhsOcopy, Stat_Ref (pStat_copy End), _lhsOdeclVars), cur')
                                     else v0 cur' pStat_copy')
  v1 :: (TStat top) -> (Map String Int) -> (Code, TStat top)
  v1 cur inh = tickAG (_lhsOcode, res) where
    (_lhsOcode, expr) = tickAG (realv1 (tstat_expr cur) inh)
    res = tickAG (update (cur {
                            tstat_v1 = memv1,
                            tstat_v1_dirty = False,
                            tstat_expr = expr
                          }))
    memv1 :: (TStat top) -> (Map String Int) -> (Code, TStat top)
    memv1 cur' inh' = tickAG (if tickEQ (inh == inh') && not (tstat_v1_dirty cur')
                              then (_lhsOcode, cur')
                              else v1 cur' inh')
  realv0 :: (TExpr top) -> (forall t. (Path Stat t) -> Path Stat t) -> ((Stat, StatR Stat, [String]), TExpr top)
  realv0 expr0 pStat_copy = ((_lhsOcopy, _lhsOcopyRStat, _lhsOdeclVars), expr1) where
    _lhsOdeclVars = tickSem []
    ((_exprIcopy, _exprIcopyRStat), expr1) = texpr_v0 expr0 expr0 (pStat_copy . StatStatExprP_expr . id)
    _loc_copy = tickSem (StatExpr _exprIcopy)
    _loc_copyRStat = StatStatExprR _exprIcopyRStat
    _lhsOcopy = tickSem _loc_copy
    _lhsOcopyRStat = _loc_copyRStat
  realv1 :: (TExpr top) -> (Map String Int) -> (Code, TExpr top)
  realv1 expr1 _lhsIenv = (_lhsOcode, expr2) where
    _exprOenv = tickSem _lhsIenv
    ((_exprIaddress, _exprIcode), expr2) = texpr_v1 expr1 expr1 (_exprOenv)
    _lhsOcode = tickSem (_exprIcode ++ [ pop ])

semStat_StatIf :: forall top. (TExpr top) -> (TStat top) -> (TStat top) -> TStat top
semStat_StatIf _cond _true _false = TStatStatIf {
                                      tstat_lookup = lookup,
                                      tstat_change = change,
                                      tstat_v0 = v0,
                                      tstat_v1 = v1,
                                      tstat_v0_dirty = True,
                                      tstat_v1_dirty = True,
                                      tstat_cond = _cond,
                                      tstat_true = _true,
                                      tstat_false = _false
                                    } where
  lookup :: forall t. (TStat top) -> (Path Stat t) -> SemType t top
  lookup cur End = tickAG cur
  lookup cur (StatStatIfP_cond ps) = tickAG (texpr_lookup (tstat_cond cur) (tstat_cond cur) ps)
  lookup cur (StatStatIfP_true ps) = tickAG (tstat_lookup (tstat_true cur) (tstat_true cur) ps)
  lookup cur (StatStatIfP_false ps) = tickAG (tstat_lookup (tstat_false cur) (tstat_false cur) ps)
  change :: forall r. (TStat top) -> (forall t. (Path top t) -> SemType t top) -> (Path Stat r) -> (ReplType r top) -> TStat top
  change cur lu End repl = tickAG (semStatR lu repl)
  change cur lu (StatStatIfP_cond ps) repl = tickAG (update_cond ps (cur {
                                                                       tstat_cond = texpr_change (tstat_cond cur) (tstat_cond cur) lu ps repl
                                                                     }))
  change cur lu (StatStatIfP_true ps) repl = tickAG (update_true ps (cur {
                                                                       tstat_true = tstat_change (tstat_true cur) (tstat_true cur) lu ps repl
                                                                     }))
  change cur lu (StatStatIfP_false ps) repl = tickAG (update_false ps (cur {
                                                                         tstat_false = tstat_change (tstat_false cur) (tstat_false cur) lu ps repl
                                                                       }))
  update :: (TStat top) -> TStat top
  update cur = tickAG (cur {
                         tstat_v0_dirty = tstat_v0_dirty cur || tstat_v0_dirty (tstat_true cur) || tstat_v0_dirty (tstat_false cur) || texpr_v0_dirty (tstat_cond cur),
                         tstat_v1_dirty = tstat_v1_dirty cur || texpr_v1_dirty (tstat_cond cur) || tstat_v1_dirty (tstat_true cur) || tstat_v1_dirty (tstat_false cur)
                       })
  update_cond :: (Path f t) -> (TStat top) -> TStat top
  update_cond End cur = tickAG (cur {
                                  tstat_v0_dirty = True,
                                  tstat_v1_dirty = True
                                })
  update_cond _ cur = tickAG (update cur)
  update_true :: (Path f t) -> (TStat top) -> TStat top
  update_true End cur = tickAG (cur {
                                  tstat_v0_dirty = True,
                                  tstat_v1_dirty = True
                                })
  update_true _ cur = tickAG (update cur)
  update_false :: (Path f t) -> (TStat top) -> TStat top
  update_false End cur = tickAG (cur {
                                   tstat_v0_dirty = True,
                                   tstat_v1_dirty = True
                                 })
  update_false _ cur = tickAG (update cur)
  v0 :: (TStat top) -> (forall t. (Path Stat t) -> Path Stat t) -> ((Stat, StatR Stat, [String]), TStat top)
  v0 cur pStat_copy = tickAG ((_lhsOcopy, _lhsOcopyRStat, _lhsOdeclVars), res) where
    ((_lhsOcopy, _lhsOcopyRStat, _lhsOdeclVars), cond, true, false) = tickAG (realv0 (tstat_cond cur, tstat_true cur, tstat_false cur) pStat_copy)
    res = tickAG (update (cur {
                            tstat_v0 = memv0,
                            tstat_v0_dirty = False,
                            tstat_cond = cond,
                            tstat_true = true,
                            tstat_false = false
                          }))
    memv0 :: (TStat top) -> (forall t. (Path Stat t) -> Path Stat t) -> ((Stat, StatR Stat, [String]), TStat top)
    memv0 cur' pStat_copy' = tickAG (if not (tstat_v0_dirty cur')
                                     then ((_lhsOcopy, Stat_Ref (pStat_copy End), _lhsOdeclVars), cur')
                                     else v0 cur' pStat_copy')
  v1 :: (TStat top) -> (Map String Int) -> (Code, TStat top)
  v1 cur inh = tickAG (_lhsOcode, res) where
    (_lhsOcode, cond, true, false) = tickAG (realv1 (tstat_cond cur, tstat_true cur, tstat_false cur) inh)
    res = tickAG (update (cur {
                            tstat_v1 = memv1,
                            tstat_v1_dirty = False,
                            tstat_cond = cond,
                            tstat_true = true,
                            tstat_false = false
                          }))
    memv1 :: (TStat top) -> (Map String Int) -> (Code, TStat top)
    memv1 cur' inh' = tickAG (if tickEQ (inh == inh') && not (tstat_v1_dirty cur')
                              then (_lhsOcode, cur')
                              else v1 cur' inh')
  realv0 :: (TExpr top, TStat top, TStat top) -> (forall t. (Path Stat t) -> Path Stat t) -> ((Stat, StatR Stat, [String]), TExpr top, TStat top, TStat top)
  realv0 (cond0, true0, false0) pStat_copy = ((_lhsOcopy, _lhsOcopyRStat, _lhsOdeclVars), cond1, true1, false1) where
    ((_trueIcopy, _trueIcopyRStat, _trueIdeclVars), true1) = tstat_v0 true0 true0 (pStat_copy . StatStatIfP_true . id)
    ((_falseIcopy, _falseIcopyRStat, _falseIdeclVars), false1) = tstat_v0 false0 false0 (pStat_copy . StatStatIfP_false . id)
    _lhsOdeclVars = tickSem (_trueIdeclVars ++ _falseIdeclVars)
    ((_condIcopy, _condIcopyRStat), cond1) = texpr_v0 cond0 cond0 (pStat_copy . StatStatIfP_cond . id)
    _loc_copy = tickSem (StatIf _condIcopy _trueIcopy _falseIcopy)
    _loc_copyRStat = StatStatIfR _condIcopyRStat _trueIcopyRStat _falseIcopyRStat
    _lhsOcopy = tickSem _loc_copy
    _lhsOcopyRStat = _loc_copyRStat
  realv1 :: (TExpr top, TStat top, TStat top) -> (Map String Int) -> (Code, TExpr top, TStat top, TStat top)
  realv1 (cond1, true1, false1) _lhsIenv = (_lhsOcode, cond2, true2, false2) where
    _condOenv = tickSem _lhsIenv
    ((_condIaddress, _condIcode), cond2) = texpr_v1 cond1 cond1 (_condOenv)
    _trueOenv = tickSem _lhsIenv
    (_trueIcode, true2) = tstat_v1 true1 true1 (_trueOenv)
    _falseOenv = tickSem _lhsIenv
    (_falseIcode, false2) = tstat_v1 false1 false1 (_falseOenv)
    _loc_nf = tickSem (codeSize _falseIcode)
    _loc_nt = tickSem (codeSize _trueIcode)
    _lhsOcode = tickSem (_condIcode ++ [ BRF ( _loc_nt + 2 ) ] ++ _trueIcode ++ [ BRA _loc_nf ] ++ _falseIcode)

semStat_StatWhile :: forall top. (TExpr top) -> (TStat top) -> TStat top
semStat_StatWhile _cond _body = TStatStatWhile {
                                  tstat_lookup = lookup,
                                  tstat_change = change,
                                  tstat_v0 = v0,
                                  tstat_v1 = v1,
                                  tstat_v0_dirty = True,
                                  tstat_v1_dirty = True,
                                  tstat_cond = _cond,
                                  tstat_body = _body
                                } where
  lookup :: forall t. (TStat top) -> (Path Stat t) -> SemType t top
  lookup cur End = tickAG cur
  lookup cur (StatStatWhileP_cond ps) = tickAG (texpr_lookup (tstat_cond cur) (tstat_cond cur) ps)
  lookup cur (StatStatWhileP_body ps) = tickAG (tstat_lookup (tstat_body cur) (tstat_body cur) ps)
  change :: forall r. (TStat top) -> (forall t. (Path top t) -> SemType t top) -> (Path Stat r) -> (ReplType r top) -> TStat top
  change cur lu End repl = tickAG (semStatR lu repl)
  change cur lu (StatStatWhileP_cond ps) repl = tickAG (update_cond ps (cur {
                                                                          tstat_cond = texpr_change (tstat_cond cur) (tstat_cond cur) lu ps repl
                                                                        }))
  change cur lu (StatStatWhileP_body ps) repl = tickAG (update_body ps (cur {
                                                                          tstat_body = tstat_change (tstat_body cur) (tstat_body cur) lu ps repl
                                                                        }))
  update :: (TStat top) -> TStat top
  update cur = tickAG (cur {
                         tstat_v0_dirty = tstat_v0_dirty cur || tstat_v0_dirty (tstat_body cur) || texpr_v0_dirty (tstat_cond cur),
                         tstat_v1_dirty = tstat_v1_dirty cur || texpr_v1_dirty (tstat_cond cur) || tstat_v1_dirty (tstat_body cur)
                       })
  update_cond :: (Path f t) -> (TStat top) -> TStat top
  update_cond End cur = tickAG (cur {
                                  tstat_v0_dirty = True,
                                  tstat_v1_dirty = True
                                })
  update_cond _ cur = tickAG (update cur)
  update_body :: (Path f t) -> (TStat top) -> TStat top
  update_body End cur = tickAG (cur {
                                  tstat_v0_dirty = True,
                                  tstat_v1_dirty = True
                                })
  update_body _ cur = tickAG (update cur)
  v0 :: (TStat top) -> (forall t. (Path Stat t) -> Path Stat t) -> ((Stat, StatR Stat, [String]), TStat top)
  v0 cur pStat_copy = tickAG ((_lhsOcopy, _lhsOcopyRStat, _lhsOdeclVars), res) where
    ((_lhsOcopy, _lhsOcopyRStat, _lhsOdeclVars), cond, body) = tickAG (realv0 (tstat_cond cur, tstat_body cur) pStat_copy)
    res = tickAG (update (cur {
                            tstat_v0 = memv0,
                            tstat_v0_dirty = False,
                            tstat_cond = cond,
                            tstat_body = body
                          }))
    memv0 :: (TStat top) -> (forall t. (Path Stat t) -> Path Stat t) -> ((Stat, StatR Stat, [String]), TStat top)
    memv0 cur' pStat_copy' = tickAG (if not (tstat_v0_dirty cur')
                                     then ((_lhsOcopy, Stat_Ref (pStat_copy End), _lhsOdeclVars), cur')
                                     else v0 cur' pStat_copy')
  v1 :: (TStat top) -> (Map String Int) -> (Code, TStat top)
  v1 cur inh = tickAG (_lhsOcode, res) where
    (_lhsOcode, cond, body) = tickAG (realv1 (tstat_cond cur, tstat_body cur) inh)
    res = tickAG (update (cur {
                            tstat_v1 = memv1,
                            tstat_v1_dirty = False,
                            tstat_cond = cond,
                            tstat_body = body
                          }))
    memv1 :: (TStat top) -> (Map String Int) -> (Code, TStat top)
    memv1 cur' inh' = tickAG (if tickEQ (inh == inh') && not (tstat_v1_dirty cur')
                              then (_lhsOcode, cur')
                              else v1 cur' inh')
  realv0 :: (TExpr top, TStat top) -> (forall t. (Path Stat t) -> Path Stat t) -> ((Stat, StatR Stat, [String]), TExpr top, TStat top)
  realv0 (cond0, body0) pStat_copy = ((_lhsOcopy, _lhsOcopyRStat, _lhsOdeclVars), cond1, body1) where
    ((_bodyIcopy, _bodyIcopyRStat, _bodyIdeclVars), body1) = tstat_v0 body0 body0 (pStat_copy . StatStatWhileP_body . id)
    _lhsOdeclVars = tickSem _bodyIdeclVars
    ((_condIcopy, _condIcopyRStat), cond1) = texpr_v0 cond0 cond0 (pStat_copy . StatStatWhileP_cond . id)
    _loc_copy = tickSem (StatWhile _condIcopy _bodyIcopy)
    _loc_copyRStat = StatStatWhileR _condIcopyRStat _bodyIcopyRStat
    _lhsOcopy = tickSem _loc_copy
    _lhsOcopyRStat = _loc_copyRStat
  realv1 :: (TExpr top, TStat top) -> (Map String Int) -> (Code, TExpr top, TStat top)
  realv1 (cond1, body1) _lhsIenv = (_lhsOcode, cond2, body2) where
    _condOenv = tickSem _lhsIenv
    ((_condIaddress, _condIcode), cond2) = texpr_v1 cond1 cond1 (_condOenv)
    _bodyOenv = tickSem _lhsIenv
    (_bodyIcode, body2) = tstat_v1 body1 body1 (_bodyOenv)
    _loc_nb = tickSem (codeSize _bodyIcode)
    _loc_nc = tickSem (codeSize _condIcode)
    _lhsOcode = tickSem ([ BRA _loc_nb ] ++ _bodyIcode ++ _condIcode ++ [ BRT ( - ( _loc_nb + _loc_nc + 2 ) ) ])

semStat_StatFor :: forall top. (TDecl top) -> (TExpr top) -> (TExpr top) -> (TStat top) -> TStat top
semStat_StatFor _init _cond _incr _body = TStatStatFor {
                                            tstat_lookup = lookup,
                                            tstat_change = change,
                                            tstat_v0 = v0,
                                            tstat_v1 = v1,
                                            tstat_v0_dirty = True,
                                            tstat_v1_dirty = True,
                                            tstat_init = _init,
                                            tstat_cond = _cond,
                                            tstat_incr = _incr,
                                            tstat_body = _body,
                                            tstat_block = Nothing
                                          } where
  lookup :: forall t. (TStat top) -> (Path Stat t) -> SemType t top
  lookup cur End = tickAG cur
  lookup cur (StatStatForP_init ps) = tickAG (tdecl_lookup (tstat_init cur) (tstat_init cur) ps)
  lookup cur (StatStatForP_cond ps) = tickAG (texpr_lookup (tstat_cond cur) (tstat_cond cur) ps)
  lookup cur (StatStatForP_incr ps) = tickAG (texpr_lookup (tstat_incr cur) (tstat_incr cur) ps)
  lookup cur (StatStatForP_body ps) = tickAG (tstat_lookup (tstat_body cur) (tstat_body cur) ps)
  change :: forall r. (TStat top) -> (forall t. (Path top t) -> SemType t top) -> (Path Stat r) -> (ReplType r top) -> TStat top
  change cur lu End repl = tickAG (semStatR lu repl)
  change cur lu (StatStatForP_init ps) repl = tickAG (update_init ps (cur {
                                                                        tstat_init = tdecl_change (tstat_init cur) (tstat_init cur) lu ps repl
                                                                      }))
  change cur lu (StatStatForP_cond ps) repl = tickAG (update_cond ps (cur {
                                                                        tstat_cond = texpr_change (tstat_cond cur) (tstat_cond cur) lu ps repl
                                                                      }))
  change cur lu (StatStatForP_incr ps) repl = tickAG (update_incr ps (cur {
                                                                        tstat_incr = texpr_change (tstat_incr cur) (tstat_incr cur) lu ps repl
                                                                      }))
  change cur lu (StatStatForP_body ps) repl = tickAG (update_body ps (cur {
                                                                        tstat_body = tstat_change (tstat_body cur) (tstat_body cur) lu ps repl
                                                                      }))
  update :: (TStat top) -> TStat top
  update cur = tickAG (cur {
                         tstat_v0_dirty = tstat_v0_dirty cur || tdecl_v0_dirty (tstat_init cur) || texpr_v0_dirty (tstat_cond cur) || texpr_v0_dirty (tstat_incr cur) || tstat_v0_dirty (tstat_body cur),
                         tstat_v1_dirty = tstat_v1_dirty cur
                       })
  update_init :: (Path f t) -> (TStat top) -> TStat top
  update_init End cur = tickAG (cur {
                                  tstat_v0_dirty = True,
                                  tstat_v1_dirty = True
                                })
  update_init _ cur = tickAG (update cur)
  update_cond :: (Path f t) -> (TStat top) -> TStat top
  update_cond End cur = tickAG (cur {
                                  tstat_v0_dirty = True,
                                  tstat_v1_dirty = True
                                })
  update_cond _ cur = tickAG (update cur)
  update_incr :: (Path f t) -> (TStat top) -> TStat top
  update_incr End cur = tickAG (cur {
                                  tstat_v0_dirty = True,
                                  tstat_v1_dirty = True
                                })
  update_incr _ cur = tickAG (update cur)
  update_body :: (Path f t) -> (TStat top) -> TStat top
  update_body End cur = tickAG (cur {
                                  tstat_v0_dirty = True,
                                  tstat_v1_dirty = True
                                })
  update_body _ cur = tickAG (update cur)
  v0 :: (TStat top) -> (forall t. (Path Stat t) -> Path Stat t) -> ((Stat, StatR Stat, [String]), TStat top)
  v0 cur pStat_copy = tickAG ((_lhsOcopy, _lhsOcopyRStat, _lhsOdeclVars), res) where
    ((_lhsOcopy, _lhsOcopyRStat, _lhsOdeclVars), block, init, cond, incr, body) = tickAG (realv0 (tstat_block cur, tstat_init cur, tstat_cond cur, tstat_incr cur, tstat_body cur) pStat_copy)
    res = tickAG (update (cur {
                            tstat_v0 = memv0,
                            tstat_v0_dirty = False,
                            tstat_block = Just block,
                            tstat_init = init,
                            tstat_cond = cond,
                            tstat_incr = incr,
                            tstat_body = body
                          }))
    memv0 :: (TStat top) -> (forall t. (Path Stat t) -> Path Stat t) -> ((Stat, StatR Stat, [String]), TStat top)
    memv0 cur' pStat_copy' = tickAG (if not (tstat_v0_dirty cur')
                                     then ((_lhsOcopy, Stat_Ref (pStat_copy End), _lhsOdeclVars), cur')
                                     else v0 cur' pStat_copy')
  v1 :: (TStat top) -> (Map String Int) -> (Code, TStat top)
  v1 cur inh = tickAG (_lhsOcode, res) where
    (_lhsOcode, block, init, cond, incr, body) = tickAG (realv1 (tstat_block cur, tstat_init cur, tstat_cond cur, tstat_incr cur, tstat_body cur) inh)
    res = tickAG (update (cur {
                            tstat_v1 = memv1,
                            tstat_v1_dirty = False,
                            tstat_block = Just block,
                            tstat_init = init,
                            tstat_cond = cond,
                            tstat_incr = incr,
                            tstat_body = body
                          }))
    memv1 :: (TStat top) -> (Map String Int) -> (Code, TStat top)
    memv1 cur' inh' = tickAG (if tickEQ (inh == inh') && not (tstat_v1_dirty cur')
                              then (_lhsOcode, cur')
                              else v1 cur' inh')
  realv0 :: (Maybe (TStat Stat), TDecl top, TExpr top, TExpr top, TStat top) -> (forall t. (Path Stat t) -> Path Stat t) -> ((Stat, StatR Stat, [String]), TStat Stat, TDecl top, TExpr top, TExpr top, TStat top)
  realv0 (_block, init0, cond0, incr0, body0) pStat_copy = ((_lhsOcopy, _lhsOcopyRStat, _lhsOdeclVars), block1, init1, cond1, incr1, body1) where
    ((_initIcopy, _initIcopyRStat, _initIdeclVars), init1) = tdecl_v0 init0 init0 (pStat_copy . StatStatCatP_l . StatStatDeclP_decl . id)
    ((_condIcopy, _condIcopyRStat), cond1) = texpr_v0 cond0 cond0 (pStat_copy . StatStatCatP_r . StatStatWhileP_cond . id)
    ((_incrIcopy, _incrIcopyRStat), incr1) = texpr_v0 incr0 incr0 (pStat_copy . StatStatCatP_r . StatStatWhileP_body . StatStatCatP_r . StatStatExprP_expr . id)
    ((_bodyIcopy, _bodyIcopyRStat, _bodyIdeclVars), body1) = tstat_v0 body0 body0 (pStat_copy . StatStatCatP_r . StatStatWhileP_body . StatStatCatP_l . id)
    _loc_inst_block = tickSem (StatCat ( StatDecl _initIcopy ) ( StatWhile _condIcopy ( StatCat _bodyIcopy ( StatExpr _incrIcopy ) ) ))
    _loc_inst_blockRStat = StatStatCatR (StatStatDeclR _initIcopyRStat) (StatStatWhileR _condIcopyRStat (StatStatCatR _bodyIcopyRStat (StatStatExprR _incrIcopyRStat)))
    block0 = case _block of
               (Nothing) -> semStat _loc_inst_block
               (Just v) -> tstat_change v v (tstat_lookup v v) End _loc_inst_blockRStat
    ((_blockIcopy, _blockIcopyRStat, _blockIdeclVars), block1) = tstat_v0 block0 block0 (pStat_copy . undefined)
    _lhsOdeclVars = tickSem _blockIdeclVars
    _loc_copy = tickSem (StatFor _initIcopy _condIcopy _incrIcopy _bodyIcopy)
    _loc_copyRStat = StatStatForR _initIcopyRStat _condIcopyRStat _incrIcopyRStat _bodyIcopyRStat
    _lhsOcopy = tickSem _loc_copy
    _lhsOcopyRStat = _loc_copyRStat
  realv1 :: (Maybe (TStat Stat), TDecl top, TExpr top, TExpr top, TStat top) -> (Map String Int) -> (Code, TStat Stat, TDecl top, TExpr top, TExpr top, TStat top)
  realv1 ((Just block1), init1, cond1, incr1, body1) _lhsIenv = (_lhsOcode, block2, init1, cond1, incr1, body1) where
    _blockOenv = tickSem _lhsIenv
    (_blockIcode, block2) = tstat_v1 block1 block1 (_blockOenv)
    _lhsOcode = tickSem _blockIcode

semStat_StatReturn :: forall top. (TExpr top) -> TStat top
semStat_StatReturn _expr = TStatStatReturn {
                             tstat_lookup = lookup,
                             tstat_change = change,
                             tstat_v0 = v0,
                             tstat_v1 = v1,
                             tstat_v0_dirty = True,
                             tstat_v1_dirty = True,
                             tstat_expr = _expr
                           } where
  lookup :: forall t. (TStat top) -> (Path Stat t) -> SemType t top
  lookup cur End = tickAG cur
  lookup cur (StatStatReturnP_expr ps) = tickAG (texpr_lookup (tstat_expr cur) (tstat_expr cur) ps)
  change :: forall r. (TStat top) -> (forall t. (Path top t) -> SemType t top) -> (Path Stat r) -> (ReplType r top) -> TStat top
  change cur lu End repl = tickAG (semStatR lu repl)
  change cur lu (StatStatReturnP_expr ps) repl = tickAG (update_expr ps (cur {
                                                                           tstat_expr = texpr_change (tstat_expr cur) (tstat_expr cur) lu ps repl
                                                                         }))
  update :: (TStat top) -> TStat top
  update cur = tickAG (cur {
                         tstat_v0_dirty = tstat_v0_dirty cur || texpr_v0_dirty (tstat_expr cur),
                         tstat_v1_dirty = tstat_v1_dirty cur || texpr_v1_dirty (tstat_expr cur)
                       })
  update_expr :: (Path f t) -> (TStat top) -> TStat top
  update_expr End cur = tickAG (cur {
                                  tstat_v0_dirty = True,
                                  tstat_v1_dirty = True
                                })
  update_expr _ cur = tickAG (update cur)
  v0 :: (TStat top) -> (forall t. (Path Stat t) -> Path Stat t) -> ((Stat, StatR Stat, [String]), TStat top)
  v0 cur pStat_copy = tickAG ((_lhsOcopy, _lhsOcopyRStat, _lhsOdeclVars), res) where
    ((_lhsOcopy, _lhsOcopyRStat, _lhsOdeclVars), expr) = tickAG (realv0 (tstat_expr cur) pStat_copy)
    res = tickAG (update (cur {
                            tstat_v0 = memv0,
                            tstat_v0_dirty = False,
                            tstat_expr = expr
                          }))
    memv0 :: (TStat top) -> (forall t. (Path Stat t) -> Path Stat t) -> ((Stat, StatR Stat, [String]), TStat top)
    memv0 cur' pStat_copy' = tickAG (if not (tstat_v0_dirty cur')
                                     then ((_lhsOcopy, Stat_Ref (pStat_copy End), _lhsOdeclVars), cur')
                                     else v0 cur' pStat_copy')
  v1 :: (TStat top) -> (Map String Int) -> (Code, TStat top)
  v1 cur inh = tickAG (_lhsOcode, res) where
    (_lhsOcode, expr) = tickAG (realv1 (tstat_expr cur) inh)
    res = tickAG (update (cur {
                            tstat_v1 = memv1,
                            tstat_v1_dirty = False,
                            tstat_expr = expr
                          }))
    memv1 :: (TStat top) -> (Map String Int) -> (Code, TStat top)
    memv1 cur' inh' = tickAG (if tickEQ (inh == inh') && not (tstat_v1_dirty cur')
                              then (_lhsOcode, cur')
                              else v1 cur' inh')
  realv0 :: (TExpr top) -> (forall t. (Path Stat t) -> Path Stat t) -> ((Stat, StatR Stat, [String]), TExpr top)
  realv0 expr0 pStat_copy = ((_lhsOcopy, _lhsOcopyRStat, _lhsOdeclVars), expr1) where
    _lhsOdeclVars = tickSem []
    ((_exprIcopy, _exprIcopyRStat), expr1) = texpr_v0 expr0 expr0 (pStat_copy . StatStatReturnP_expr . id)
    _loc_copy = tickSem (StatReturn _exprIcopy)
    _loc_copyRStat = StatStatReturnR _exprIcopyRStat
    _lhsOcopy = tickSem _loc_copy
    _lhsOcopyRStat = _loc_copyRStat
  realv1 :: (TExpr top) -> (Map String Int) -> (Code, TExpr top)
  realv1 expr1 _lhsIenv = (_lhsOcode, expr2) where
    _exprOenv = tickSem _lhsIenv
    ((_exprIaddress, _exprIcode), expr2) = texpr_v1 expr1 expr1 (_exprOenv)
    _lhsOcode = tickSem (_exprIcode ++ [ STR R3 , UNLINK , RET ])

semStat_StatCat :: forall top. (TStat top) -> (TStat top) -> TStat top
semStat_StatCat _l _r = TStatStatCat {
                          tstat_lookup = lookup,
                          tstat_change = change,
                          tstat_v0 = v0,
                          tstat_v1 = v1,
                          tstat_v0_dirty = True,
                          tstat_v1_dirty = True,
                          tstat_l = _l,
                          tstat_r = _r
                        } where
  lookup :: forall t. (TStat top) -> (Path Stat t) -> SemType t top
  lookup cur End = tickAG cur
  lookup cur (StatStatCatP_l ps) = tickAG (tstat_lookup (tstat_l cur) (tstat_l cur) ps)
  lookup cur (StatStatCatP_r ps) = tickAG (tstat_lookup (tstat_r cur) (tstat_r cur) ps)
  change :: forall r. (TStat top) -> (forall t. (Path top t) -> SemType t top) -> (Path Stat r) -> (ReplType r top) -> TStat top
  change cur lu End repl = tickAG (semStatR lu repl)
  change cur lu (StatStatCatP_l ps) repl = tickAG (update_l ps (cur {
                                                                  tstat_l = tstat_change (tstat_l cur) (tstat_l cur) lu ps repl
                                                                }))
  change cur lu (StatStatCatP_r ps) repl = tickAG (update_r ps (cur {
                                                                  tstat_r = tstat_change (tstat_r cur) (tstat_r cur) lu ps repl
                                                                }))
  update :: (TStat top) -> TStat top
  update cur = tickAG (cur {
                         tstat_v0_dirty = tstat_v0_dirty cur || tstat_v0_dirty (tstat_l cur) || tstat_v0_dirty (tstat_r cur),
                         tstat_v1_dirty = tstat_v1_dirty cur || tstat_v1_dirty (tstat_l cur) || tstat_v1_dirty (tstat_r cur)
                       })
  update_l :: (Path f t) -> (TStat top) -> TStat top
  update_l End cur = tickAG (cur {
                               tstat_v0_dirty = True,
                               tstat_v1_dirty = True
                             })
  update_l _ cur = tickAG (update cur)
  update_r :: (Path f t) -> (TStat top) -> TStat top
  update_r End cur = tickAG (cur {
                               tstat_v0_dirty = True,
                               tstat_v1_dirty = True
                             })
  update_r _ cur = tickAG (update cur)
  v0 :: (TStat top) -> (forall t. (Path Stat t) -> Path Stat t) -> ((Stat, StatR Stat, [String]), TStat top)
  v0 cur pStat_copy = tickAG ((_lhsOcopy, _lhsOcopyRStat, _lhsOdeclVars), res) where
    ((_lhsOcopy, _lhsOcopyRStat, _lhsOdeclVars), l, r) = tickAG (realv0 (tstat_l cur, tstat_r cur) pStat_copy)
    res = tickAG (update (cur {
                            tstat_v0 = memv0,
                            tstat_v0_dirty = False,
                            tstat_l = l,
                            tstat_r = r
                          }))
    memv0 :: (TStat top) -> (forall t. (Path Stat t) -> Path Stat t) -> ((Stat, StatR Stat, [String]), TStat top)
    memv0 cur' pStat_copy' = tickAG (if not (tstat_v0_dirty cur')
                                     then ((_lhsOcopy, Stat_Ref (pStat_copy End), _lhsOdeclVars), cur')
                                     else v0 cur' pStat_copy')
  v1 :: (TStat top) -> (Map String Int) -> (Code, TStat top)
  v1 cur inh = tickAG (_lhsOcode, res) where
    (_lhsOcode, l, r) = tickAG (realv1 (tstat_l cur, tstat_r cur) inh)
    res = tickAG (update (cur {
                            tstat_v1 = memv1,
                            tstat_v1_dirty = False,
                            tstat_l = l,
                            tstat_r = r
                          }))
    memv1 :: (TStat top) -> (Map String Int) -> (Code, TStat top)
    memv1 cur' inh' = tickAG (if tickEQ (inh == inh') && not (tstat_v1_dirty cur')
                              then (_lhsOcode, cur')
                              else v1 cur' inh')
  realv0 :: (TStat top, TStat top) -> (forall t. (Path Stat t) -> Path Stat t) -> ((Stat, StatR Stat, [String]), TStat top, TStat top)
  realv0 (l0, r0) pStat_copy = ((_lhsOcopy, _lhsOcopyRStat, _lhsOdeclVars), l1, r1) where
    ((_lIcopy, _lIcopyRStat, _lIdeclVars), l1) = tstat_v0 l0 l0 (pStat_copy . StatStatCatP_l . id)
    ((_rIcopy, _rIcopyRStat, _rIdeclVars), r1) = tstat_v0 r0 r0 (pStat_copy . StatStatCatP_r . id)
    _lhsOdeclVars = tickSem (_lIdeclVars ++ _rIdeclVars)
    _loc_copy = tickSem (StatCat _lIcopy _rIcopy)
    _loc_copyRStat = StatStatCatR _lIcopyRStat _rIcopyRStat
    _lhsOcopy = tickSem _loc_copy
    _lhsOcopyRStat = _loc_copyRStat
  realv1 :: (TStat top, TStat top) -> (Map String Int) -> (Code, TStat top, TStat top)
  realv1 (l1, r1) _lhsIenv = (_lhsOcode, l2, r2) where
    _lOenv = tickSem _lhsIenv
    (_lIcode, l2) = tstat_v1 l1 l1 (_lOenv)
    _rOenv = tickSem _lhsIenv
    (_rIcode, r2) = tstat_v1 r1 r1 (_rOenv)
    _lhsOcode = tickSem (_lIcode ++ _rIcode)

semStat_StatBlock :: forall top. (TStatL top) -> TStat top
semStat_StatBlock _stats = TStatStatBlock {
                             tstat_lookup = lookup,
                             tstat_change = change,
                             tstat_v0 = v0,
                             tstat_v1 = v1,
                             tstat_v0_dirty = True,
                             tstat_v1_dirty = True,
                             tstat_stats = _stats
                           } where
  lookup :: forall t. (TStat top) -> (Path Stat t) -> SemType t top
  lookup cur End = tickAG cur
  lookup cur (StatStatBlockP_stats ps) = tickAG (tstatl_lookup (tstat_stats cur) (tstat_stats cur) ps)
  change :: forall r. (TStat top) -> (forall t. (Path top t) -> SemType t top) -> (Path Stat r) -> (ReplType r top) -> TStat top
  change cur lu End repl = tickAG (semStatR lu repl)
  change cur lu (StatStatBlockP_stats ps) repl = tickAG (update_stats ps (cur {
                                                                            tstat_stats = tstatl_change (tstat_stats cur) (tstat_stats cur) lu ps repl
                                                                          }))
  update :: (TStat top) -> TStat top
  update cur = tickAG (cur {
                         tstat_v0_dirty = tstat_v0_dirty cur || tstatl_v0_dirty (tstat_stats cur),
                         tstat_v1_dirty = tstat_v1_dirty cur || tstatl_v1_dirty (tstat_stats cur)
                       })
  update_stats :: (Path f t) -> (TStat top) -> TStat top
  update_stats End cur = tickAG (cur {
                                   tstat_v0_dirty = True,
                                   tstat_v1_dirty = True
                                 })
  update_stats _ cur = tickAG (update cur)
  v0 :: (TStat top) -> (forall t. (Path Stat t) -> Path Stat t) -> ((Stat, StatR Stat, [String]), TStat top)
  v0 cur pStat_copy = tickAG ((_lhsOcopy, _lhsOcopyRStat, _lhsOdeclVars), res) where
    ((_lhsOcopy, _lhsOcopyRStat, _lhsOdeclVars), stats) = tickAG (realv0 (tstat_stats cur) pStat_copy)
    res = tickAG (update (cur {
                            tstat_v0 = memv0,
                            tstat_v0_dirty = False,
                            tstat_stats = stats
                          }))
    memv0 :: (TStat top) -> (forall t. (Path Stat t) -> Path Stat t) -> ((Stat, StatR Stat, [String]), TStat top)
    memv0 cur' pStat_copy' = tickAG (if not (tstat_v0_dirty cur')
                                     then ((_lhsOcopy, Stat_Ref (pStat_copy End), _lhsOdeclVars), cur')
                                     else v0 cur' pStat_copy')
  v1 :: (TStat top) -> (Map String Int) -> (Code, TStat top)
  v1 cur inh = tickAG (_lhsOcode, res) where
    (_lhsOcode, stats) = tickAG (realv1 (tstat_stats cur) inh)
    res = tickAG (update (cur {
                            tstat_v1 = memv1,
                            tstat_v1_dirty = False,
                            tstat_stats = stats
                          }))
    memv1 :: (TStat top) -> (Map String Int) -> (Code, TStat top)
    memv1 cur' inh' = tickAG (if tickEQ (inh == inh') && not (tstat_v1_dirty cur')
                              then (_lhsOcode, cur')
                              else v1 cur' inh')
  realv0 :: (TStatL top) -> (forall t. (Path Stat t) -> Path Stat t) -> ((Stat, StatR Stat, [String]), TStatL top)
  realv0 stats0 pStat_copy = ((_lhsOcopy, _lhsOcopyRStat, _lhsOdeclVars), stats1) where
    ((_statsIcopy, _statsIcopyRStat, _statsIdeclVars), stats1) = tstatl_v0 stats0 stats0 (pStat_copy . StatStatBlockP_stats . id)
    _lhsOdeclVars = tickSem _statsIdeclVars
    _loc_copy = tickSem (StatBlock _statsIcopy)
    _loc_copyRStat = StatStatBlockR _statsIcopyRStat
    _lhsOcopy = tickSem _loc_copy
    _lhsOcopyRStat = _loc_copyRStat
  realv1 :: (TStatL top) -> (Map String Int) -> (Code, TStatL top)
  realv1 stats1 _lhsIenv = (_lhsOcode, stats2) where
    _statsOenv = tickSem _lhsIenv
    ((_statsIcode, _statsIlength), stats2) = tstatl_v1 stats1 stats1 (_statsOenv)
    _lhsOcode = tickSem _statsIcode

semStatL_Cons :: forall top. (TStat top) -> (TStatL top) -> TStatL top
semStatL_Cons _hd _tl = TStatLCons {
                          tstatl_lookup = lookup,
                          tstatl_change = change,
                          tstatl_v0 = v0,
                          tstatl_v1 = v1,
                          tstatl_v0_dirty = True,
                          tstatl_v1_dirty = True,
                          tstatl_hd = _hd,
                          tstatl_tl = _tl
                        } where
  lookup :: forall t. (TStatL top) -> (Path StatL t) -> SemType t top
  lookup cur End = tickAG cur
  lookup cur (PathL_hd ps) = tickAG (tstat_lookup (tstatl_hd cur) (tstatl_hd cur) ps)
  lookup cur (PathL_tl ps) = tickAG (tstatl_lookup (tstatl_tl cur) (tstatl_tl cur) ps)
  change :: forall r. (TStatL top) -> (forall t. (Path top t) -> SemType t top) -> (Path StatL r) -> (ReplType r top) -> TStatL top
  change cur lu End repl = tickAG (semStatLR lu repl)
  change cur lu (PathL_hd ps) repl = tickAG (update_hd ps (cur {
                                                             tstatl_hd = tstat_change (tstatl_hd cur) (tstatl_hd cur) lu ps repl
                                                           }))
  change cur lu (PathL_tl ps) repl = tickAG (update_tl ps (cur {
                                                             tstatl_tl = tstatl_change (tstatl_tl cur) (tstatl_tl cur) lu ps repl
                                                           }))
  update :: (TStatL top) -> TStatL top
  update cur = tickAG (cur {
                         tstatl_v0_dirty = tstatl_v0_dirty cur || tstat_v0_dirty (tstatl_hd cur) || tstatl_v0_dirty (tstatl_tl cur),
                         tstatl_v1_dirty = tstatl_v1_dirty cur || tstatl_v1_dirty (tstatl_tl cur) || tstat_v1_dirty (tstatl_hd cur)
                       })
  update_hd :: (Path f t) -> (TStatL top) -> TStatL top
  update_hd End cur = tickAG (cur {
                                tstatl_v0_dirty = True,
                                tstatl_v1_dirty = True
                              })
  update_hd _ cur = tickAG (update cur)
  update_tl :: (Path f t) -> (TStatL top) -> TStatL top
  update_tl End cur = tickAG (cur {
                                tstatl_v0_dirty = True,
                                tstatl_v1_dirty = True
                              })
  update_tl _ cur = tickAG (update cur)
  v0 :: (TStatL top) -> (forall t. (Path StatL t) -> Path Stat t) -> ((StatL, StatLR Stat, [String]), TStatL top)
  v0 cur pStat_copy = tickAG ((_lhsOcopy, _lhsOcopyRStat, _lhsOdeclVars), res) where
    ((_lhsOcopy, _lhsOcopyRStat, _lhsOdeclVars), hd, tl) = tickAG (realv0 (tstatl_hd cur, tstatl_tl cur) pStat_copy)
    res = tickAG (update (cur {
                            tstatl_v0 = memv0,
                            tstatl_v0_dirty = False,
                            tstatl_hd = hd,
                            tstatl_tl = tl
                          }))
    memv0 :: (TStatL top) -> (forall t. (Path StatL t) -> Path Stat t) -> ((StatL, StatLR Stat, [String]), TStatL top)
    memv0 cur' pStat_copy' = tickAG (if not (tstatl_v0_dirty cur')
                                     then ((_lhsOcopy, List_Ref (pStat_copy End), _lhsOdeclVars), cur')
                                     else v0 cur' pStat_copy')
  v1 :: (TStatL top) -> (Map String Int) -> ((Code, Int), TStatL top)
  v1 cur inh = tickAG ((_lhsOcode, _lhsOlength), res) where
    ((_lhsOcode, _lhsOlength), hd, tl) = tickAG (realv1 (tstatl_hd cur, tstatl_tl cur) inh)
    res = tickAG (update (cur {
                            tstatl_v1 = memv1,
                            tstatl_v1_dirty = False,
                            tstatl_hd = hd,
                            tstatl_tl = tl
                          }))
    memv1 :: (TStatL top) -> (Map String Int) -> ((Code, Int), TStatL top)
    memv1 cur' inh' = tickAG (if tickEQ (inh == inh') && not (tstatl_v1_dirty cur')
                              then ((_lhsOcode, _lhsOlength), cur')
                              else v1 cur' inh')
  realv0 :: (TStat top, TStatL top) -> (forall t. (Path StatL t) -> Path Stat t) -> ((StatL, StatLR Stat, [String]), TStat top, TStatL top)
  realv0 (hd0, tl0) pStat_copy = ((_lhsOcopy, _lhsOcopyRStat, _lhsOdeclVars), hd1, tl1) where
    ((_hdIcopy, _hdIcopyRStat, _hdIdeclVars), hd1) = tstat_v0 hd0 hd0 (pStat_copy . PathL_hd . id)
    ((_tlIcopy, _tlIcopyRStat, _tlIdeclVars), tl1) = tstatl_v0 tl0 tl0 (pStat_copy . PathL_tl . id)
    _lhsOdeclVars = tickSem (_hdIdeclVars ++ _tlIdeclVars)
    _loc_copy = tickSem ((:) _hdIcopy _tlIcopy)
    _loc_copyRStat = ListConsR _hdIcopyRStat _tlIcopyRStat
    _lhsOcopy = tickSem _loc_copy
    _lhsOcopyRStat = _loc_copyRStat
  realv1 :: (TStat top, TStatL top) -> (Map String Int) -> ((Code, Int), TStat top, TStatL top)
  realv1 (hd1, tl1) _lhsIenv = ((_lhsOcode, _lhsOlength), hd2, tl2) where
    _tlOenv = tickSem _lhsIenv
    ((_tlIcode, _tlIlength), tl2) = tstatl_v1 tl1 tl1 (_tlOenv)
    _lhsOlength = tickSem (1 + _tlIlength)
    _hdOenv = tickSem _lhsIenv
    (_hdIcode, hd2) = tstat_v1 hd1 hd1 (_hdOenv)
    _lhsOcode = tickSem (_hdIcode ++ _tlIcode)

semStatL_Nil :: forall top. TStatL top
semStatL_Nil = TStatLNil {
                 tstatl_lookup = lookup,
                 tstatl_change = change,
                 tstatl_v0 = v0,
                 tstatl_v1 = v1,
                 tstatl_v0_dirty = True,
                 tstatl_v1_dirty = True
               } where
  lookup :: forall t. (TStatL top) -> (Path StatL t) -> SemType t top
  lookup cur End = tickAG cur
  change :: forall r. (TStatL top) -> (forall t. (Path top t) -> SemType t top) -> (Path StatL r) -> (ReplType r top) -> TStatL top
  change cur lu End repl = tickAG (semStatLR lu repl)
  update :: (TStatL top) -> TStatL top
  update cur = tickAG cur
  v0 :: (TStatL top) -> (forall t. (Path StatL t) -> Path Stat t) -> ((StatL, StatLR Stat, [String]), TStatL top)
  v0 cur pStat_copy = tickAG ((_lhsOcopy, _lhsOcopyRStat, _lhsOdeclVars), res) where
    (_lhsOcopy, _lhsOcopyRStat, _lhsOdeclVars) = tickAG (realv0 () pStat_copy)
    res = tickAG (update (cur {
                            tstatl_v0 = memv0,
                            tstatl_v0_dirty = False
                          }))
    memv0 :: (TStatL top) -> (forall t. (Path StatL t) -> Path Stat t) -> ((StatL, StatLR Stat, [String]), TStatL top)
    memv0 cur' pStat_copy' = tickAG (if not (tstatl_v0_dirty cur')
                                     then ((_lhsOcopy, List_Ref (pStat_copy End), _lhsOdeclVars), cur')
                                     else v0 cur' pStat_copy')
  v1 :: (TStatL top) -> (Map String Int) -> ((Code, Int), TStatL top)
  v1 cur inh = tickAG ((_lhsOcode, _lhsOlength), res) where
    (_lhsOcode, _lhsOlength) = tickAG (realv1 () inh)
    res = tickAG (update (cur {
                            tstatl_v1 = memv1,
                            tstatl_v1_dirty = False
                          }))
    memv1 :: (TStatL top) -> (Map String Int) -> ((Code, Int), TStatL top)
    memv1 cur' inh' = tickAG (if tickEQ (inh == inh') && not (tstatl_v1_dirty cur')
                              then ((_lhsOcode, _lhsOlength), cur')
                              else v1 cur' inh')
  realv0 :: () -> (forall t. (Path StatL t) -> Path Stat t) -> (StatL, StatLR Stat, [String])
  realv0 () pStat_copy = (_lhsOcopy, _lhsOcopyRStat, _lhsOdeclVars) where
    _lhsOdeclVars = tickSem []
    _loc_copy = tickSem []
    _loc_copyRStat = ListNilR
    _lhsOcopy = tickSem _loc_copy
    _lhsOcopyRStat = _loc_copyRStat
  realv1 :: () -> (Map String Int) -> (Code, Int)
  realv1 () _lhsIenv = (_lhsOcode, _lhsOlength) where
    _lhsOlength = tickSem 0
    _lhsOcode = tickSem []

semType_TypeVoid :: forall top. TType top
semType_TypeVoid = TTypeTypeVoid {
                     ttype_lookup = lookup,
                     ttype_change = change,
                     ttype_v0 = v0,
                     ttype_v0_dirty = True
                   } where
  lookup :: forall t. (TType top) -> (Path Type t) -> SemType t top
  lookup cur End = tickAG cur
  change :: forall r. (TType top) -> (forall t. (Path top t) -> SemType t top) -> (Path Type r) -> (ReplType r top) -> TType top
  change cur lu End repl = tickAG (semTypeR lu repl)
  update :: (TType top) -> TType top
  update cur = tickAG cur
  v0 :: (TType top) -> (forall t. (Path Type t) -> Path Stat t) -> ((Type, TypeR Stat), TType top)
  v0 cur pStat_copy = tickAG ((_lhsOcopy, _lhsOcopyRStat), res) where
    (_lhsOcopy, _lhsOcopyRStat) = tickAG (realv0 () pStat_copy)
    res = tickAG (update (cur {
                            ttype_v0 = memv0,
                            ttype_v0_dirty = False
                          }))
    memv0 :: (TType top) -> (forall t. (Path Type t) -> Path Stat t) -> ((Type, TypeR Stat), TType top)
    memv0 cur' pStat_copy' = tickAG (if not (ttype_v0_dirty cur')
                                     then ((_lhsOcopy, Type_Ref (pStat_copy End)), cur')
                                     else v0 cur' pStat_copy')
  realv0 :: () -> (forall t. (Path Type t) -> Path Stat t) -> (Type, TypeR Stat)
  realv0 () pStat_copy = (_lhsOcopy, _lhsOcopyRStat) where
    _loc_copy = tickSem TypeVoid
    _loc_copyRStat = TypeTypeVoidR
    _lhsOcopy = tickSem _loc_copy
    _lhsOcopyRStat = _loc_copyRStat

semType_TypePrim :: forall top. String -> TType top
semType_TypePrim _ptype = TTypeTypePrim {
                            ttype_lookup = lookup,
                            ttype_change = change,
                            ttype_v0 = v0,
                            ttype_v0_dirty = True
                          } where
  lookup :: forall t. (TType top) -> (Path Type t) -> SemType t top
  lookup cur End = tickAG cur
  change :: forall r. (TType top) -> (forall t. (Path top t) -> SemType t top) -> (Path Type r) -> (ReplType r top) -> TType top
  change cur lu End repl = tickAG (semTypeR lu repl)
  update :: (TType top) -> TType top
  update cur = tickAG cur
  v0 :: (TType top) -> (forall t. (Path Type t) -> Path Stat t) -> ((Type, TypeR Stat), TType top)
  v0 cur pStat_copy = tickAG ((_lhsOcopy, _lhsOcopyRStat), res) where
    (_lhsOcopy, _lhsOcopyRStat) = tickAG (realv0 () pStat_copy)
    res = tickAG (update (cur {
                            ttype_v0 = memv0,
                            ttype_v0_dirty = False
                          }))
    memv0 :: (TType top) -> (forall t. (Path Type t) -> Path Stat t) -> ((Type, TypeR Stat), TType top)
    memv0 cur' pStat_copy' = tickAG (if not (ttype_v0_dirty cur')
                                     then ((_lhsOcopy, Type_Ref (pStat_copy End)), cur')
                                     else v0 cur' pStat_copy')
  realv0 :: () -> (forall t. (Path Type t) -> Path Stat t) -> (Type, TypeR Stat)
  realv0 () pStat_copy = (_lhsOcopy, _lhsOcopyRStat) where
    _loc_copy = tickSem (TypePrim _ptype)
    _loc_copyRStat = TypeTypePrimR _ptype
    _lhsOcopy = tickSem _loc_copy
    _lhsOcopyRStat = _loc_copyRStat

semType_TypeObj :: forall top. String -> TType top
semType_TypeObj _otype = TTypeTypeObj {
                           ttype_lookup = lookup,
                           ttype_change = change,
                           ttype_v0 = v0,
                           ttype_v0_dirty = True
                         } where
  lookup :: forall t. (TType top) -> (Path Type t) -> SemType t top
  lookup cur End = tickAG cur
  change :: forall r. (TType top) -> (forall t. (Path top t) -> SemType t top) -> (Path Type r) -> (ReplType r top) -> TType top
  change cur lu End repl = tickAG (semTypeR lu repl)
  update :: (TType top) -> TType top
  update cur = tickAG cur
  v0 :: (TType top) -> (forall t. (Path Type t) -> Path Stat t) -> ((Type, TypeR Stat), TType top)
  v0 cur pStat_copy = tickAG ((_lhsOcopy, _lhsOcopyRStat), res) where
    (_lhsOcopy, _lhsOcopyRStat) = tickAG (realv0 () pStat_copy)
    res = tickAG (update (cur {
                            ttype_v0 = memv0,
                            ttype_v0_dirty = False
                          }))
    memv0 :: (TType top) -> (forall t. (Path Type t) -> Path Stat t) -> ((Type, TypeR Stat), TType top)
    memv0 cur' pStat_copy' = tickAG (if not (ttype_v0_dirty cur')
                                     then ((_lhsOcopy, Type_Ref (pStat_copy End)), cur')
                                     else v0 cur' pStat_copy')
  realv0 :: () -> (forall t. (Path Type t) -> Path Stat t) -> (Type, TypeR Stat)
  realv0 () pStat_copy = (_lhsOcopy, _lhsOcopyRStat) where
    _loc_copy = tickSem (TypeObj _otype)
    _loc_copyRStat = TypeTypeObjR _otype
    _lhsOcopy = tickSem _loc_copy
    _lhsOcopyRStat = _loc_copyRStat

semType_TypeArray :: forall top. (TType top) -> TType top
semType_TypeArray _itype = TTypeTypeArray {
                             ttype_lookup = lookup,
                             ttype_change = change,
                             ttype_v0 = v0,
                             ttype_v0_dirty = True,
                             ttype_itype = _itype
                           } where
  lookup :: forall t. (TType top) -> (Path Type t) -> SemType t top
  lookup cur End = tickAG cur
  lookup cur (TypeTypeArrayP_itype ps) = tickAG (ttype_lookup (ttype_itype cur) (ttype_itype cur) ps)
  change :: forall r. (TType top) -> (forall t. (Path top t) -> SemType t top) -> (Path Type r) -> (ReplType r top) -> TType top
  change cur lu End repl = tickAG (semTypeR lu repl)
  change cur lu (TypeTypeArrayP_itype ps) repl = tickAG (update_itype ps (cur {
                                                                            ttype_itype = ttype_change (ttype_itype cur) (ttype_itype cur) lu ps repl
                                                                          }))
  update :: (TType top) -> TType top
  update cur = tickAG (cur {
                         ttype_v0_dirty = ttype_v0_dirty cur || ttype_v0_dirty (ttype_itype cur)
                       })
  update_itype :: (Path f t) -> (TType top) -> TType top
  update_itype End cur = tickAG (cur {
                                   ttype_v0_dirty = True
                                 })
  update_itype _ cur = tickAG (update cur)
  v0 :: (TType top) -> (forall t. (Path Type t) -> Path Stat t) -> ((Type, TypeR Stat), TType top)
  v0 cur pStat_copy = tickAG ((_lhsOcopy, _lhsOcopyRStat), res) where
    ((_lhsOcopy, _lhsOcopyRStat), itype) = tickAG (realv0 (ttype_itype cur) pStat_copy)
    res = tickAG (update (cur {
                            ttype_v0 = memv0,
                            ttype_v0_dirty = False,
                            ttype_itype = itype
                          }))
    memv0 :: (TType top) -> (forall t. (Path Type t) -> Path Stat t) -> ((Type, TypeR Stat), TType top)
    memv0 cur' pStat_copy' = tickAG (if not (ttype_v0_dirty cur')
                                     then ((_lhsOcopy, Type_Ref (pStat_copy End)), cur')
                                     else v0 cur' pStat_copy')
  realv0 :: (TType top) -> (forall t. (Path Type t) -> Path Stat t) -> ((Type, TypeR Stat), TType top)
  realv0 itype0 pStat_copy = ((_lhsOcopy, _lhsOcopyRStat), itype1) where
    ((_itypeIcopy, _itypeIcopyRStat), itype1) = ttype_v0 itype0 itype0 (pStat_copy . TypeTypeArrayP_itype . id)
    _loc_copy = tickSem (TypeArray _itypeIcopy)
    _loc_copyRStat = TypeTypeArrayR _itypeIcopyRStat
    _lhsOcopy = tickSem _loc_copy
    _lhsOcopyRStat = _loc_copyRStat

