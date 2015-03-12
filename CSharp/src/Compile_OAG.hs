module Compile_Lazy where

import SSM
import Data
import Data.Map (Map)
import qualified Data.Map as Map


-- Manual code generation

type T_Decl = T_Stat

type T_Stat = ([String], T_Stat_1)
type T_Stat_1 = Map String Int -> [Instr]

type T_Type = ()
type T_DeclL = T_Decl
type T_Member = [Instr]
type T_Expr = Map String Int -> [Instr] -- more in practice

semMemberMemberM ::  T_Type -> String -> T_DeclL -> T_Stat
                     -> T_Member
semMemberMemberM rtype_ name_ params_ body_ =
  let _paramsIdeclVars  ::  [String]
      (_paramsIdeclVars, params2) = params_ in
  let _paramsOenv       ::  Map String Int
      _paramsOenv       =   Map.empty in
  let _paramsIcode      ::  Code
      _paramsIcode      =   params2 _paramsOenv  in
  let _loc_params       =   zip (reverse _paramsIdeclVars) [-2,-3..] in
  let _bodyIdeclVars    ::  [String]
      (_bodyIdeclVars, body2) = body_ in
  let _loc_locs         =   zip _bodyIdeclVars [1..] in
  let _bodyOenv         ::  Map String Int
      _bodyOenv         =   Map.fromList (_loc_params ++ _loc_locs) in
  let _bodyIcode        ::  Code
      _bodyIcode        =   body2 _bodyOenv in
  let _lhsOcode         ::  Code
      _lhsOcode         =   [ LABEL name_, LINK (length _loc_locs ) ]
                            ++ _bodyIcode
                            ++ [ UNLINK, RET ]
  in  ( _lhsOcode)

semStatStatReturn :: T_Expr -> T_Stat
semStatStatReturn expr_ =
  let  _lhsOdeclVars  ::  [String]
       _lhsOdeclVars  =   []  in
  let  semStatStatReturn_1 :: T_Stat_1
       semStatStatReturn_1 _lhsIenv =
         let  _exprOenv   ::  Map String Int
              _exprOenv   =   _lhsIenv in
         let  _exprIcode  ::  [Instr]
              _exprIcode  =   expr_ _exprOenv in
         let  _lhsOcode   ::  [Instr]
              _lhsOcode   =   _exprIcode ++ [STR R3, UNLINK, RET]
         in   (_lhsOcode)
  in   (_lhsOdeclVars, semStatStatReturn_1)
