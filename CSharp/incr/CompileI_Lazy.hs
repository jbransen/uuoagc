module CompileI_Lazy where

import CompileI (Class (..), Const (..), Decl (..), DeclL, Expr (..), ExprL, Member (..), MemberL, Stat (..), StatL, Type (..))
import Prelude hiding (LT, GT, EQ)
import Data.Map (Map, findWithDefault, empty, fromList)
import Data.Char (ord)

import SSM

generateCode :: Class -> Code
generateCode = semClass

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

-- Types
type TClass = Code

type TConst = (Code, Const)

type TDecl = (Decl, [String], (Map String Int) -> Code)

type TDeclL = (Code, [String], Int)

type TExpr = (Expr, (Map String Int) -> (Code, Code))

type TExprL = (ExprL, (Map String Int) -> (Code, Int))

type TMember = Code

type TMemberL = Code

type TStat = (Stat, [String], (Map String Int) -> Code)

type TStatL = (StatL, [String], (Map String Int) -> (Code, Int))

type TType = Type

-- Semantic functions
semClass :: Class -> TClass
semClass (ClassC name members) = semClass_ClassC name (semMemberL members)

semConst :: Const -> TConst
semConst (ConstInt val) = semConst_ConstInt val
semConst (ConstBool val) = semConst_ConstBool val
semConst (ConstChar val) = semConst_ConstChar val

semDecl :: Decl -> TDecl
semDecl (DeclC vtype name) = semDecl_DeclC (semType vtype) name
semDecl (DeclInit vtype name init) = semDecl_DeclInit (semType vtype) name (semExpr init)

semDeclL :: DeclL -> TDeclL
semDeclL = foldr semDeclL_Cons semDeclL_Nil . map semDecl

semExpr :: Expr -> TExpr
semExpr (ExprConst const) = semExpr_ExprConst (semConst const)
semExpr (ExprVar name) = semExpr_ExprVar name
semExpr (ExprOper op left right) = semExpr_ExprOper op (semExpr left) (semExpr right)
semExpr (ExprFun name params) = semExpr_ExprFun name (semExprL params)

semExprL :: ExprL -> TExprL
semExprL = foldr semExprL_Cons semExprL_Nil . map semExpr

semMember :: Member -> TMember
semMember (MemberD decl) = semMember_MemberD (semDecl decl)
semMember (MemberM rtype name params body) = semMember_MemberM (semType rtype) name (semDeclL params) (semStat body)

semMemberL :: MemberL -> TMemberL
semMemberL = foldr semMemberL_Cons semMemberL_Nil . map semMember

semStat :: Stat -> TStat
semStat (StatDecl decl) = semStat_StatDecl (semDecl decl)
semStat (StatExpr expr) = semStat_StatExpr (semExpr expr)
semStat (StatIf cond true false) = semStat_StatIf (semExpr cond) (semStat true) (semStat false)
semStat (StatWhile cond body) = semStat_StatWhile (semExpr cond) (semStat body)
semStat (StatFor init cond incr body) = semStat_StatFor (semDecl init) (semExpr cond) (semExpr incr) (semStat body)
semStat (StatReturn expr) = semStat_StatReturn (semExpr expr)
semStat (StatCat l r) = semStat_StatCat (semStat l) (semStat r)
semStat (StatBlock stats) = semStat_StatBlock (semStatL stats)

semStatL :: StatL -> TStatL
semStatL = foldr semStatL_Cons semStatL_Nil . map semStat

semType :: Type -> TType
semType (TypeVoid) = semType_TypeVoid
semType (TypePrim ptype) = semType_TypePrim ptype
semType (TypeObj otype) = semType_TypeObj otype
semType (TypeArray itype) = semType_TypeArray (semType itype)

-- Production semantic functions
semClass_ClassC _name _members = v0 _members where
  v0 members0 = _lhsOcode where
    _membersIcode = members0
    _lhsOcode = [ Bsr "Main" , HALT ] ++ _membersIcode

semConst_ConstInt _val = v0 where
  v0 = (_lhsOcode, _lhsOcopy) where
    _loc_copy = ConstInt _val
    _lhsOcopy = _loc_copy
    _lhsOcode = [ LDC _val ]

semConst_ConstBool _val = v0 where
  v0 = (_lhsOcode, _lhsOcopy) where
    _loc_copy = ConstBool _val
    _lhsOcopy = _loc_copy
    _lhsOcode = [ LDC ( if _val then 1 else 0 ) ]

semConst_ConstChar _val = v0 where
  v0 = (_lhsOcode, _lhsOcopy) where
    _loc_copy = ConstChar _val
    _lhsOcopy = _loc_copy
    _lhsOcode = [ LDC ( ord _val ) ]

semDecl_DeclC _vtype _name = v0 _vtype where
  v0 vtype0 = (_lhsOcopy, _lhsOdeclVars, v1) where
    _lhsOdeclVars = [ _name ]
    _vtypeIcopy = vtype0
    _loc_copy = DeclC _vtypeIcopy _name
    _lhsOcopy = _loc_copy
  v1 _lhsIenv = _lhsOcode where
    _lhsOcode = []

semDecl_DeclInit _vtype _name _init = v0 _vtype _init where
  v0 vtype0 init0 = (_lhsOcopy, _lhsOdeclVars, v1 _initIcopy) where
    _lhsOdeclVars = [ _name ]
    _vtypeIcopy = vtype0
    (_initIcopy, init1) = init0
    _loc_copy = DeclInit _vtypeIcopy _name _initIcopy
    _lhsOcopy = _loc_copy
  v1 _initIcopy _lhsIenv = _lhsOcode where
    _loc_inst_stat = StatExpr ( ExprOper "=" ( ExprVar _name ) _initIcopy )
    stat0 = semStat _loc_inst_stat
    (_statIcopy, _statIdeclVars, stat1) = stat0
    _statOenv = _lhsIenv
    _statIcode = stat1 _statOenv
    _lhsOcode = _statIcode

semDeclL_Cons _hd _tl = v0 _hd _tl where
  v0 hd0 tl0 = (_lhsOcode, _lhsOdeclVars, _lhsOlength) where
    (_tlIcode, _tlIdeclVars, _tlIlength) = tl0
    _lhsOlength = 1 + _tlIlength
    (_hdIcopy, _hdIdeclVars, hd1) = hd0
    _lhsOdeclVars = _hdIdeclVars ++ _tlIdeclVars
    _hdOenv = empty
    _hdIcode = hd1 _hdOenv
    _lhsOcode = _hdIcode ++ _tlIcode

semDeclL_Nil = v0 where
  v0 = (_lhsOcode, _lhsOdeclVars, _lhsOlength) where
    _lhsOlength = 0
    _lhsOdeclVars = []
    _lhsOcode = []

semExpr_ExprConst _const = v0 _const where
  v0 const0 = (_lhsOcopy, v1 _constIcode) where
    (_constIcode, _constIcopy) = const0
    _loc_copy = ExprConst _constIcopy
    _lhsOcopy = _loc_copy
  v1 _constIcode _lhsIenv = (_lhsOaddress, _lhsOcode) where
    _lhsOcode = _constIcode
    _lhsOaddress = error "Not a valid expression"

semExpr_ExprVar _name = v0 where
  v0 = (_lhsOcopy, v1) where
    _loc_copy = ExprVar _name
    _lhsOcopy = _loc_copy
  v1 _lhsIenv = (_lhsOaddress, _lhsOcode) where
    _loc_address = findWithDefault ( error $ _name ++ " not declared." ) _name _lhsIenv
    _lhsOcode = [ LDL _loc_address ]
    _lhsOaddress = [ LDLA _loc_address ]

semExpr_ExprOper _op _left _right = v0 _left _right where
  v0 left0 right0 = (_lhsOcopy, v1 left1 right1) where
    (_leftIcopy, left1) = left0
    (_rightIcopy, right1) = right0
    _loc_copy = ExprOper _op _leftIcopy _rightIcopy
    _lhsOcopy = _loc_copy
  v1 left1 right1 _lhsIenv = (_lhsOaddress, _lhsOcode) where
    _leftOenv = _lhsIenv
    (_leftIaddress, _leftIcode) = left1 _leftOenv
    _rightOenv = _lhsIenv
    (_rightIaddress, _rightIcode) = right1 _rightOenv
    _lhsOcode = case _op of { "=" -> _rightIcode ++ [ LDS 0 ] ++ _leftIaddress ++ [ STA 0 ] ; op -> _leftIcode ++ _rightIcode ++ [ findWithDefault ( error "Unknown operator" ) op opCodes ] }
    _lhsOaddress = error "Not a valid expression"

semExpr_ExprFun _name _params = v0 _params where
  v0 params0 = (_lhsOcopy, v1 params1) where
    (_paramsIcopy, params1) = params0
    _loc_copy = ExprFun _name _paramsIcopy
    _lhsOcopy = _loc_copy
  v1 params1 _lhsIenv = (_lhsOaddress, _lhsOcode) where
    _paramsOenv = _lhsIenv
    (_paramsIcode, _paramsIlength) = params1 _paramsOenv
    _loc_cleanup = if _paramsIlength == 0 then [] else [ AJS ( - _paramsIlength ) ]
    _lhsOcode = case _name of { "print" -> _paramsIcode ++ [ LDS 0 , TRAP 0 ] ; _ -> _paramsIcode ++ [ Bsr _name ] ++ _loc_cleanup ++ [ LDR R3 ] }
    _lhsOaddress = error "Not a valid expression"

semExprL_Cons _hd _tl = v0 _hd _tl where
  v0 hd0 tl0 = (_lhsOcopy, v1 hd1 tl1) where
    (_hdIcopy, hd1) = hd0
    (_tlIcopy, tl1) = tl0
    _loc_copy = (:) _hdIcopy _tlIcopy
    _lhsOcopy = _loc_copy
  v1 hd1 tl1 _lhsIenv = (_lhsOcode, _lhsOlength) where
    _tlOenv = _lhsIenv
    (_tlIcode, _tlIlength) = tl1 _tlOenv
    _lhsOlength = 1 + _tlIlength
    _hdOenv = _lhsIenv
    (_hdIaddress, _hdIcode) = hd1 _hdOenv
    _lhsOcode = _hdIcode ++ _tlIcode

semExprL_Nil = v0 where
  v0 = (_lhsOcopy, v1) where
    _loc_copy = []
    _lhsOcopy = _loc_copy
  v1 _lhsIenv = (_lhsOcode, _lhsOlength) where
    _lhsOlength = 0
    _lhsOcode = []

semMember_MemberD _decl = v0 _decl where
  v0 decl0 = _lhsOcode where
    (_declIcopy, _declIdeclVars, decl1) = decl0
    _declOenv = empty
    _declIcode = decl1 _declOenv
    _lhsOcode = _declIcode

semMember_MemberM _rtype _name _params _body = v0 _rtype _params _body where
  v0 rtype0 params0 body0 = _lhsOcode where
    (_paramsIcode, _paramsIdeclVars, _paramsIlength) = params0
    (_bodyIcopy, _bodyIdeclVars, body1) = body0
    _loc_locs = zip _bodyIdeclVars [ 1 .. ]
    _loc_params = zip ( reverse _paramsIdeclVars ) [ - 2 , - 3 .. ]
    _bodyOenv = fromList $ _loc_params ++ _loc_locs
    _bodyIcode = body1 _bodyOenv
    _loc_annotes = [ ANNOTE MP n n "green" v | ( v , n ) <- ( _loc_params ++ _loc_locs ) ]
    _lhsOcode = [ LABEL _name , LINK ( length _loc_locs ) ] ++ _loc_annotes ++ _bodyIcode ++ [ UNLINK , RET ]

semMemberL_Cons _hd _tl = v0 _hd _tl where
  v0 hd0 tl0 = _lhsOcode where
    _hdIcode = hd0
    _tlIcode = tl0
    _lhsOcode = _hdIcode ++ _tlIcode

semMemberL_Nil = v0 where
  v0 = _lhsOcode where
    _lhsOcode = []

semStat_StatDecl _decl = v0 _decl where
  v0 decl0 = (_lhsOcopy, _lhsOdeclVars, v1 decl1) where
    (_declIcopy, _declIdeclVars, decl1) = decl0
    _lhsOdeclVars = _declIdeclVars
    _loc_copy = StatDecl _declIcopy
    _lhsOcopy = _loc_copy
  v1 decl1 _lhsIenv = _lhsOcode where
    _declOenv = _lhsIenv
    _declIcode = decl1 _declOenv
    _lhsOcode = _declIcode

semStat_StatExpr _expr = v0 _expr where
  v0 expr0 = (_lhsOcopy, _lhsOdeclVars, v1 expr1) where
    _lhsOdeclVars = []
    (_exprIcopy, expr1) = expr0
    _loc_copy = StatExpr _exprIcopy
    _lhsOcopy = _loc_copy
  v1 expr1 _lhsIenv = _lhsOcode where
    _exprOenv = _lhsIenv
    (_exprIaddress, _exprIcode) = expr1 _exprOenv
    _lhsOcode = _exprIcode ++ [ pop ]

semStat_StatIf _cond _true _false = v0 _cond _true _false where
  v0 cond0 true0 false0 = (_lhsOcopy, _lhsOdeclVars, v1 cond1 true1 false1) where
    (_trueIcopy, _trueIdeclVars, true1) = true0
    (_falseIcopy, _falseIdeclVars, false1) = false0
    _lhsOdeclVars = _trueIdeclVars ++ _falseIdeclVars
    (_condIcopy, cond1) = cond0
    _loc_copy = StatIf _condIcopy _trueIcopy _falseIcopy
    _lhsOcopy = _loc_copy
  v1 cond1 true1 false1 _lhsIenv = _lhsOcode where
    _condOenv = _lhsIenv
    (_condIaddress, _condIcode) = cond1 _condOenv
    _trueOenv = _lhsIenv
    _trueIcode = true1 _trueOenv
    _falseOenv = _lhsIenv
    _falseIcode = false1 _falseOenv
    _loc_nf = codeSize _falseIcode
    _loc_nt = codeSize _trueIcode
    _lhsOcode = _condIcode ++ [ BRF ( _loc_nt + 2 ) ] ++ _trueIcode ++ [ BRA _loc_nf ] ++ _falseIcode

semStat_StatWhile _cond _body = v0 _cond _body where
  v0 cond0 body0 = (_lhsOcopy, _lhsOdeclVars, v1 cond1 body1) where
    (_bodyIcopy, _bodyIdeclVars, body1) = body0
    _lhsOdeclVars = _bodyIdeclVars
    (_condIcopy, cond1) = cond0
    _loc_copy = StatWhile _condIcopy _bodyIcopy
    _lhsOcopy = _loc_copy
  v1 cond1 body1 _lhsIenv = _lhsOcode where
    _condOenv = _lhsIenv
    (_condIaddress, _condIcode) = cond1 _condOenv
    _bodyOenv = _lhsIenv
    _bodyIcode = body1 _bodyOenv
    _loc_nb = codeSize _bodyIcode
    _loc_nc = codeSize _condIcode
    _lhsOcode = [ BRA _loc_nb ] ++ _bodyIcode ++ _condIcode ++ [ BRT ( - ( _loc_nb + _loc_nc + 2 ) ) ]

semStat_StatFor _init _cond _incr _body = v0 _init _cond _incr _body where
  v0 init0 cond0 incr0 body0 = (_lhsOcopy, _lhsOdeclVars, v1 block1 init1 cond1 incr1 body1) where
    (_initIcopy, _initIdeclVars, init1) = init0
    (_condIcopy, cond1) = cond0
    (_incrIcopy, incr1) = incr0
    (_bodyIcopy, _bodyIdeclVars, body1) = body0
    _loc_inst_block = StatCat ( StatDecl _initIcopy ) ( StatWhile _condIcopy ( StatCat _bodyIcopy ( StatExpr _incrIcopy ) ) )
    block0 = semStat _loc_inst_block
    (_blockIcopy, _blockIdeclVars, block1) = block0
    _lhsOdeclVars = _blockIdeclVars
    _loc_copy = StatFor _initIcopy _condIcopy _incrIcopy _bodyIcopy
    _lhsOcopy = _loc_copy
  v1 block1 init1 cond1 incr1 body1 _lhsIenv = _lhsOcode where
    _blockOenv = _lhsIenv
    _blockIcode = block1 _blockOenv
    _lhsOcode = _blockIcode

semStat_StatReturn _expr = v0 _expr where
  v0 expr0 = (_lhsOcopy, _lhsOdeclVars, v1 expr1) where
    _lhsOdeclVars = []
    (_exprIcopy, expr1) = expr0
    _loc_copy = StatReturn _exprIcopy
    _lhsOcopy = _loc_copy
  v1 expr1 _lhsIenv = _lhsOcode where
    _exprOenv = _lhsIenv
    (_exprIaddress, _exprIcode) = expr1 _exprOenv
    _lhsOcode = _exprIcode ++ [ STR R3 , UNLINK , RET ]

semStat_StatCat _l _r = v0 _l _r where
  v0 l0 r0 = (_lhsOcopy, _lhsOdeclVars, v1 l1 r1) where
    (_lIcopy, _lIdeclVars, l1) = l0
    (_rIcopy, _rIdeclVars, r1) = r0
    _lhsOdeclVars = _lIdeclVars ++ _rIdeclVars
    _loc_copy = StatCat _lIcopy _rIcopy
    _lhsOcopy = _loc_copy
  v1 l1 r1 _lhsIenv = _lhsOcode where
    _lOenv = _lhsIenv
    _lIcode = l1 _lOenv
    _rOenv = _lhsIenv
    _rIcode = r1 _rOenv
    _lhsOcode = _lIcode ++ _rIcode

semStat_StatBlock _stats = v0 _stats where
  v0 stats0 = (_lhsOcopy, _lhsOdeclVars, v1 stats1) where
    (_statsIcopy, _statsIdeclVars, stats1) = stats0
    _lhsOdeclVars = _statsIdeclVars
    _loc_copy = StatBlock _statsIcopy
    _lhsOcopy = _loc_copy
  v1 stats1 _lhsIenv = _lhsOcode where
    _statsOenv = _lhsIenv
    (_statsIcode, _statsIlength) = stats1 _statsOenv
    _lhsOcode = _statsIcode

semStatL_Cons _hd _tl = v0 _hd _tl where
  v0 hd0 tl0 = (_lhsOcopy, _lhsOdeclVars, v1 hd1 tl1) where
    (_hdIcopy, _hdIdeclVars, hd1) = hd0
    (_tlIcopy, _tlIdeclVars, tl1) = tl0
    _lhsOdeclVars = _hdIdeclVars ++ _tlIdeclVars
    _loc_copy = (:) _hdIcopy _tlIcopy
    _lhsOcopy = _loc_copy
  v1 hd1 tl1 _lhsIenv = (_lhsOcode, _lhsOlength) where
    _tlOenv = _lhsIenv
    (_tlIcode, _tlIlength) = tl1 _tlOenv
    _lhsOlength = 1 + _tlIlength
    _hdOenv = _lhsIenv
    _hdIcode = hd1 _hdOenv
    _lhsOcode = _hdIcode ++ _tlIcode

semStatL_Nil = v0 where
  v0 = (_lhsOcopy, _lhsOdeclVars, v1) where
    _lhsOdeclVars = []
    _loc_copy = []
    _lhsOcopy = _loc_copy
  v1 _lhsIenv = (_lhsOcode, _lhsOlength) where
    _lhsOlength = 0
    _lhsOcode = []

semType_TypeVoid = v0 where
  v0 = _lhsOcopy where
    _loc_copy = TypeVoid
    _lhsOcopy = _loc_copy

semType_TypePrim _ptype = v0 where
  v0 = _lhsOcopy where
    _loc_copy = TypePrim _ptype
    _lhsOcopy = _loc_copy

semType_TypeObj _otype = v0 where
  v0 = _lhsOcopy where
    _loc_copy = TypeObj _otype
    _lhsOcopy = _loc_copy

semType_TypeArray _itype = v0 _itype where
  v0 itype0 = _lhsOcopy where
    _itypeIcopy = itype0
    _loc_copy = TypeArray _itypeIcopy
    _lhsOcopy = _loc_copy

