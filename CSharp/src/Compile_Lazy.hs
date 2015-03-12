module Compile_Lazy where

import SSM
import Data
import Data.Map (Map)
import qualified Data.Map as Map


-- Manual code generation

type T_Decl = Map String Int -> ([Instr], [String])
type T_Stat = Map String Int -> ([Instr], [String])

type T_Member = [Instr]
type T_Type = ()
type T_DeclL = T_Decl

semDecl :: Decl -> T_Decl
semDecl (DeclC _vtype _name) = semDeclDeclC (semType _vtype) _name

semType :: Type -> T_Type
semType = undefined

semDeclDeclC :: T_Type -> String -> T_Decl
semDeclDeclC vtype_ name_ =
  \ _lhsIenv ->
   let  _lhsOdeclVars :: [String]
        _lhsOdeclVars = [ name_ ]
        _lhsOcode :: Code
        _lhsOcode = []
   in   ( _lhsOcode,_lhsOdeclVars)


semMemberMemberM ::  T_Type -> String -> T_DeclL -> T_Stat
                     -> T_Member
semMemberMemberM rtype_ name_ params_ body_ =
  let _paramsIcode      ::  Code
      _paramsIdeclVars  ::  [String]
      _paramsOenv       ::  Map String Int
      _paramsOenv       =   Map.empty
      ( _paramsIcode,_paramsIdeclVars) = params_ _paramsOenv
      _loc_params       =   zip (reverse _paramsIdeclVars) [-2,-3..]
      _loc_locs         =   zip _bodyIdeclVars [1..]
      _bodyOenv         ::  Map String Int
      _bodyOenv         =   Map.fromList (_loc_params ++ _loc_locs)
      _bodyIcode        ::  Code
      _bodyIdeclVars    ::  [String]
      ( _bodyIcode,_bodyIdeclVars) = body_ _bodyOenv
      _lhsOcode         ::  Code
      _lhsOcode         =   [ LABEL name_, LINK (length _loc_locs ) ]
                            ++ _bodyIcode
                            ++ [ UNLINK, RET ]
  in  ( _lhsOcode)
