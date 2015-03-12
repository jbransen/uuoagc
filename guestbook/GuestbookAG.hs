{-# LANGUAGE GADTs, TypeFamilies, RankNTypes, ScopedTypeVariables #-}

{-# LANGUAGE CPP #-}

module Main where

import Data.Set (Set)
import qualified Data.Set as Set
import Control.Monad
import Control.DeepSeq

#if GATHER_STATS
import System.IO.Unsafe (unsafePerformIO)
import Data.IORef (newIORef, readIORef, writeIORef, modifyIORef, IORef)
#endif

#if MEASURE_TIME
import Criterion
import Criterion.Main
#endif

type Name = String

example :: Guestbook
example = Leave "Bransen" 7.6 "I liked the fast internet connection" $ Leave "Dijkstra" 8 "The atmosphere is great for taking pictures!" $ Arrive "Dijkstra" $ Leave "Swierstra" 6 "Nice hotel, but the beds are too short" $ Arrive "Bransen" $ Arrive "Swierstra" $ Empty

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
type MyPath = Int

data MyGuestbookR
  = Ref MyPath
  | EmptyR
  | ArriveR Name MyGuestbookR
  | LeaveR Name Double String MyGuestbookR
  deriving (Read, Show)

type Change = (String, Int, MyGuestbookR)

-- Parsing
parseGuestbook :: String -> Guestbook
parseGuestbook = parseEntry . lines

parseEntry :: [String] -> Guestbook
parseEntry [] = Empty
parseEntry (s:ss) = case words s of
  ["ARRIVE", n] -> Arrive n $ parseEntry ss
  ("LEAVE":n:"-":g:"-":cs) -> Leave n (read g) (unwords cs) $ parseEntry ss

parseChanges :: String -> [Change]
parseChanges = map read . lines

-- Invocation
computeGrade :: Guestbook -> (Double, TTop Top)
computeGrade g = ttop_v0 t t where
  t = semTop $ Top g

computeGradeI :: TTop Top -> (Path Top Guestbook, GuestbookR Top) -> (Double, TTop Top)
computeGradeI t (p, r) = ttop_v0 t' t' where
  t' = ttop_change t t (ttop_lookup t t) p r

-- Main
main :: IO ()
main = do
  f <- readFile "large_guestbook.txt"
  let gb = parseGuestbook f
  let (g,st) = computeGrade gb
  resetStats
  print g
  printStats
  f2 <- readFile "large_guestbook_changes.txt"
  let chs = parseChanges f2
  let chs' = map (translateChanges gb) chs
  forM_ chs' $ \ch' -> do
    let (g,st) = computeGrade gb
    deepseq g $ return ()
    resetStats
    print $ fst $ computeGradeI st ch'
    printStats
  -- Insert + delete
  let (g,st) = computeGrade gb
  deepseq g $ return ()
  resetStats
  print $ fst $ computeGradeI (snd $ computeGradeI st (chs' !! 0)) (chs' !! 1)
  printStats
#if MEASURE_TIME
  let bi = nf (fst . computeGrade) gb
--  benchmark bi -- trial run, to make sure memory is allocated and so on
  defaultMain $
    bench "initial" bi
    : [ bench name $ nf (\(gb',ch') -> let (c1,incr) = computeGrade gb'
                                       in  (c1,fst $ computeGradeI incr ch')) (gb, ch)
      | ((name,_,_), ch) <- zip chs chs'
      ]
{-
    ++ [ bench "insert + delete" $ nf (\(gb',ch1,ch2) ->
          let (c1,incr) = computeGrade gb'
          in  (c1, fst $ computeGradeI (snd $ computeGradeI incr ch1) ch2)) (gb, chs' !! 1, chs' !! 0)
       ]
-}
#endif

translateChanges :: Guestbook -> Change -> (Path Top Guestbook, GuestbookR Top)
translateChanges gb (_, p, r) = (trp p, g r) where
  g :: MyGuestbookR -> GuestbookR Top
  g (Ref p) = Guestbook_Ref (trp p)
  g (EmptyR) = GuestbookEmptyR
  g (ArriveR n t) = GuestbookArriveR n (g t)
  g (LeaveR n gr c t) = GuestbookLeaveR n gr c (g t)
  trp :: MyPath -> Path Top Guestbook
  trp mp = TopTopP_gb (f mp gb) where
    f 0 _ = End
    f n (Arrive _ g)    = GuestbookArriveP_tl $ f (n-1) g
    f n (Leave _ _ _ g) = GuestbookLeaveP_tl $ f (n-1) g

st1 = semTop (Top example)
(grade, st2) = ttop_v0 st1 st1

{-
path = Leave_tl (Leave_tl (Arrive_tl End))
repl = Ref (Leave_tl (Leave_tl (Arrive_tl (Leave_tl End))))
-}
path = TopTopP_gb (GuestbookLeaveP_tl (GuestbookLeaveP_tl (GuestbookArriveP_tl End)))
repl = Guestbook_Ref (TopTopP_gb (GuestbookLeaveP_tl (GuestbookLeaveP_tl (GuestbookArriveP_tl (GuestbookLeaveP_tl End)))))

st3 = ttop_change st2 st2 (ttop_lookup st2 st2) path repl
(grade2, st4) = ttop_v0 st3 st3
-- Data types
type DL = [ Double ]

data Guestbook
  = Empty
  | Arrive Name Guestbook
  | Leave Name Double String Guestbook
  deriving (Eq,Ord,Show)

data Top
  = Top Guestbook
  deriving (Eq,Ord,Show)

-- Path
data Path f t where
  End :: Path t t
  PathL_hd :: (Path a t) -> Path [ a ] t
  PathL_tl :: (Path [ a ] t) -> Path [ a ] t
  GuestbookArriveP_tl :: (Path Guestbook t) -> Path Guestbook t
  GuestbookLeaveP_tl :: (Path Guestbook t) -> Path Guestbook t
  TopTopP_gb :: (Path Guestbook t) -> Path Top t

-- Replacement types
data ListR a ar top
  = List_Ref (Path top [ a ])
  | ListConsR ar (ListR a ar top)
  | ListNilR

type DLR top = ListR Double Double top

data GuestbookR top
  = Guestbook_Ref (Path top Guestbook)
  | GuestbookEmptyR
  | GuestbookArriveR Name (GuestbookR top)
  | GuestbookLeaveR Name Double String (GuestbookR top)

data TopR top
  = Top_Ref (Path top Top)
  | TopTopR (GuestbookR top)

type family ReplType a b :: *
type instance ReplType DL top = DLR top
type instance ReplType Guestbook top = GuestbookR top
type instance ReplType Top top = TopR top

-- Semantic types
data TDL top
  = TDLCons {
      tdl_lookup :: forall t. (TDL top) -> (Path DL t) -> SemType t top,
      tdl_change :: forall r. (TDL top) -> (forall t. (Path top t) -> SemType t top) -> (Path DL r) -> (ReplType r top) -> TDL top,
      tdl_v0 :: (TDL top) -> ((Double, Double, Double), TDL top),
      tdl_v0_dirty :: Bool,
      tdl_tl :: TDL top
    }
  | TDLNil {
      tdl_lookup :: forall t. (TDL top) -> (Path DL t) -> SemType t top,
      tdl_change :: forall r. (TDL top) -> (forall t. (Path top t) -> SemType t top) -> (Path DL r) -> (ReplType r top) -> TDL top,
      tdl_v0 :: (TDL top) -> ((Double, Double, Double), TDL top),
      tdl_v0_dirty :: Bool
    }

data TGuestbook top
  = TGuestbookEmpty {
      tguestbook_lookup :: forall t. (TGuestbook top) -> (Path Guestbook t) -> SemType t top,
      tguestbook_change :: forall r. (TGuestbook top) -> (forall t. (Path top t) -> SemType t top) -> (Path Guestbook r) -> (ReplType r top) -> TGuestbook top,
      tguestbook_v0 :: (TGuestbook top) -> (forall t. (Path DL t) -> Path DL t) -> ((Set Name, DL, DLR DL), TGuestbook top),
      tguestbook_v0_dirty :: Bool
    }
  | TGuestbookArrive {
      tguestbook_lookup :: forall t. (TGuestbook top) -> (Path Guestbook t) -> SemType t top,
      tguestbook_change :: forall r. (TGuestbook top) -> (forall t. (Path top t) -> SemType t top) -> (Path Guestbook r) -> (ReplType r top) -> TGuestbook top,
      tguestbook_v0 :: (TGuestbook top) -> (forall t. (Path DL t) -> Path DL t) -> ((Set Name, DL, DLR DL), TGuestbook top),
      tguestbook_v0_dirty :: Bool,
      tguestbook_tl :: TGuestbook top
    }
  | TGuestbookLeave {
      tguestbook_lookup :: forall t. (TGuestbook top) -> (Path Guestbook t) -> SemType t top,
      tguestbook_change :: forall r. (TGuestbook top) -> (forall t. (Path top t) -> SemType t top) -> (Path Guestbook r) -> (ReplType r top) -> TGuestbook top,
      tguestbook_v0 :: (TGuestbook top) -> (forall t. (Path DL t) -> Path DL t) -> ((Set Name, DL, DLR DL), TGuestbook top),
      tguestbook_v0_dirty :: Bool,
      tguestbook_tl :: TGuestbook top
    }

data TTop top
  = TTopTop {
      ttop_lookup :: forall t. (TTop top) -> (Path Top t) -> SemType t top,
      ttop_change :: forall r. (TTop top) -> (forall t. (Path top t) -> SemType t top) -> (Path Top r) -> (ReplType r top) -> TTop top,
      ttop_v0 :: (TTop top) -> (Double, TTop top),
      ttop_v0_dirty :: Bool,
      ttop_gb :: TGuestbook top,
      ttop_revs :: Maybe (TDL DL)
    }

type family SemType a :: * -> *
type instance SemType DL = TDL
type instance SemType Guestbook = TGuestbook
type instance SemType Top = TTop

-- Semantic functions
semDL :: DL -> TDL top
semDL = foldr semDL_Cons semDL_Nil

semGuestbook :: Guestbook -> TGuestbook top
semGuestbook (Empty) = semGuestbook_Empty
semGuestbook (Arrive name tl) = semGuestbook_Arrive name (semGuestbook tl)
semGuestbook (Leave name grade review tl) = semGuestbook_Leave name grade review (semGuestbook tl)

semTop :: Top -> TTop top
semTop (Top gb) = semTop_Top (semGuestbook gb)

semDLR :: (forall t. (Path top t) -> SemType t top) -> (DLR top) -> TDL top
semDLR lu (List_Ref p) = lu p
semDLR lu (ListConsR hd tl) = semDL_Cons hd (semDLR lu tl)
semDLR lu (ListNilR) = semDL_Nil

semGuestbookR :: (forall t. (Path top t) -> SemType t top) -> (GuestbookR top) -> TGuestbook top
semGuestbookR lu (Guestbook_Ref p) = lu p
semGuestbookR lu (GuestbookEmptyR) = semGuestbook_Empty
semGuestbookR lu (GuestbookArriveR name tl) = semGuestbook_Arrive name (semGuestbookR lu tl)
semGuestbookR lu (GuestbookLeaveR name grade review tl) = semGuestbook_Leave name grade review (semGuestbookR lu tl)

semTopR :: (forall t. (Path top t) -> SemType t top) -> (TopR top) -> TTop top
semTopR lu (Top_Ref p) = lu p
semTopR lu (TopTopR gb) = semTop_Top (semGuestbookR lu gb)

-- Production semantic functions
semDL_Cons :: forall top. Double -> (TDL top) -> TDL top
semDL_Cons _hd _tl = TDLCons {
                       tdl_lookup = lookup,
                       tdl_change = change,
                       tdl_v0 = v0,
                       tdl_v0_dirty = True,
                       tdl_tl = _tl
                     } where
  lookup :: forall t. (TDL top) -> (Path DL t) -> SemType t top
  lookup cur End = tickAG cur
  lookup cur (PathL_tl ps) = tickAG (tdl_lookup (tdl_tl cur) (tdl_tl cur) ps)
  change :: forall r. (TDL top) -> (forall t. (Path top t) -> SemType t top) -> (Path DL r) -> (ReplType r top) -> TDL top
  change cur lu End repl = tickAG (semDLR lu repl)
  change cur lu (PathL_tl ps) repl = tickAG (update_tl ps (cur {
                                                             tdl_tl = tdl_change (tdl_tl cur) (tdl_tl cur) lu ps repl
                                                           }))
  update :: (TDL top) -> TDL top
  update cur = tickAG (cur {
                         tdl_v0_dirty = tdl_v0_dirty cur || tdl_v0_dirty (tdl_tl cur)
                       })
  update_tl :: (Path f t) -> (TDL top) -> TDL top
  update_tl End cur = tickAG (cur {
                                tdl_v0_dirty = True
                              })
  update_tl _ cur = tickAG (update cur)
  v0 :: (TDL top) -> ((Double, Double, Double), TDL top)
  v0 cur = tickAG ((_lhsOaverage, _lhsOlength, _lhsOsum), res) where
    ((_lhsOaverage, _lhsOlength, _lhsOsum), tl) = tickAG (realv0 (tdl_tl cur))
    res = tickAG (update (cur {
                            tdl_v0 = memv0,
                            tdl_v0_dirty = False,
                            tdl_tl = tl
                          }))
    memv0 :: (TDL top) -> ((Double, Double, Double), TDL top)
    memv0 cur' = tickAG (if not (tdl_v0_dirty cur')
                         then ((_lhsOaverage, _lhsOlength, _lhsOsum), cur')
                         else v0 cur')
  realv0 :: (TDL top) -> ((Double, Double, Double), TDL top)
  realv0 tl0 = ((_lhsOaverage, _lhsOlength, _lhsOsum), tl1) where
    ((_tlIaverage, _tlIlength, _tlIsum), tl1) = tdl_v0 tl0 tl0
    _loc_length = tickSem (_tlIlength + 1)
    _loc_sum = tickSem (_tlIsum + _hd)
    _lhsOaverage = tickSem (_loc_sum / _loc_length)
    _lhsOlength = tickSem _loc_length
    _lhsOsum = tickSem _loc_sum

semDL_Nil :: forall top. TDL top
semDL_Nil = TDLNil {
              tdl_lookup = lookup,
              tdl_change = change,
              tdl_v0 = v0,
              tdl_v0_dirty = True
            } where
  lookup :: forall t. (TDL top) -> (Path DL t) -> SemType t top
  lookup cur End = tickAG cur
  change :: forall r. (TDL top) -> (forall t. (Path top t) -> SemType t top) -> (Path DL r) -> (ReplType r top) -> TDL top
  change cur lu End repl = tickAG (semDLR lu repl)
  update :: (TDL top) -> TDL top
  update cur = tickAG cur
  v0 :: (TDL top) -> ((Double, Double, Double), TDL top)
  v0 cur = tickAG ((_lhsOaverage, _lhsOlength, _lhsOsum), res) where
    (_lhsOaverage, _lhsOlength, _lhsOsum) = tickAG (realv0 ())
    res = tickAG (update (cur {
                            tdl_v0 = memv0,
                            tdl_v0_dirty = False
                          }))
    memv0 :: (TDL top) -> ((Double, Double, Double), TDL top)
    memv0 cur' = tickAG (if not (tdl_v0_dirty cur')
                         then ((_lhsOaverage, _lhsOlength, _lhsOsum), cur')
                         else v0 cur')
  realv0 :: () -> (Double, Double, Double)
  realv0 () = (_lhsOaverage, _lhsOlength, _lhsOsum) where
    _lhsOlength = tickSem 0
    _lhsOsum = tickSem 0
    _lhsOaverage = tickSem 0

semGuestbook_Empty :: forall top. TGuestbook top
semGuestbook_Empty = TGuestbookEmpty {
                       tguestbook_lookup = lookup,
                       tguestbook_change = change,
                       tguestbook_v0 = v0,
                       tguestbook_v0_dirty = True
                     } where
  lookup :: forall t. (TGuestbook top) -> (Path Guestbook t) -> SemType t top
  lookup cur End = tickAG cur
  change :: forall r. (TGuestbook top) -> (forall t. (Path top t) -> SemType t top) -> (Path Guestbook r) -> (ReplType r top) -> TGuestbook top
  change cur lu End repl = tickAG (semGuestbookR lu repl)
  update :: (TGuestbook top) -> TGuestbook top
  update cur = tickAG cur
  v0 :: (TGuestbook top) -> (forall t. (Path DL t) -> Path DL t) -> ((Set Name, DL, DLR DL), TGuestbook top)
  v0 cur pDL_trueReviews = tickAG ((_lhsOsignedIn, _lhsOtrueReviews, _lhsOtrueReviewsRDL), res) where
    (_lhsOsignedIn, _lhsOtrueReviews, _lhsOtrueReviewsRDL) = tickAG (realv0 () pDL_trueReviews)
    res = tickAG (update (cur {
                            tguestbook_v0 = memv0,
                            tguestbook_v0_dirty = False
                          }))
    memv0 :: (TGuestbook top) -> (forall t. (Path DL t) -> Path DL t) -> ((Set Name, DL, DLR DL), TGuestbook top)
    memv0 cur' pDL_trueReviews' = tickAG (if not (tguestbook_v0_dirty cur')
                                          then ((_lhsOsignedIn, _lhsOtrueReviews, List_Ref (pDL_trueReviews End)), cur')
                                          else v0 cur' pDL_trueReviews')
  realv0 :: () -> (forall t. (Path DL t) -> Path DL t) -> (Set Name, DL, DLR DL)
  realv0 () pDL_trueReviews = (_lhsOsignedIn, _lhsOtrueReviews, _lhsOtrueReviewsRDL) where
    _lhsOsignedIn = tickSem Set.empty
    _loc_trueReviews = tickSem []
    _loc_trueReviewsRDL = ListNilR
    _lhsOtrueReviews = tickSem _loc_trueReviews
    _lhsOtrueReviewsRDL = _loc_trueReviewsRDL

semGuestbook_Arrive :: forall top. Name -> (TGuestbook top) -> TGuestbook top
semGuestbook_Arrive _name _tl = TGuestbookArrive {
                                  tguestbook_lookup = lookup,
                                  tguestbook_change = change,
                                  tguestbook_v0 = v0,
                                  tguestbook_v0_dirty = True,
                                  tguestbook_tl = _tl
                                } where
  lookup :: forall t. (TGuestbook top) -> (Path Guestbook t) -> SemType t top
  lookup cur End = tickAG cur
  lookup cur (GuestbookArriveP_tl ps) = tickAG (tguestbook_lookup (tguestbook_tl cur) (tguestbook_tl cur) ps)
  change :: forall r. (TGuestbook top) -> (forall t. (Path top t) -> SemType t top) -> (Path Guestbook r) -> (ReplType r top) -> TGuestbook top
  change cur lu End repl = tickAG (semGuestbookR lu repl)
  change cur lu (GuestbookArriveP_tl ps) repl = tickAG (update_tl ps (cur {
                                                                        tguestbook_tl = tguestbook_change (tguestbook_tl cur) (tguestbook_tl cur) lu ps repl
                                                                      }))
  update :: (TGuestbook top) -> TGuestbook top
  update cur = tickAG (cur {
                         tguestbook_v0_dirty = tguestbook_v0_dirty cur || tguestbook_v0_dirty (tguestbook_tl cur)
                       })
  update_tl :: (Path f t) -> (TGuestbook top) -> TGuestbook top
  update_tl End cur = tickAG (cur {
                                tguestbook_v0_dirty = True
                              })
  update_tl _ cur = tickAG (update cur)
  v0 :: (TGuestbook top) -> (forall t. (Path DL t) -> Path DL t) -> ((Set Name, DL, DLR DL), TGuestbook top)
  v0 cur pDL_trueReviews = tickAG ((_lhsOsignedIn, _lhsOtrueReviews, _lhsOtrueReviewsRDL), res) where
    ((_lhsOsignedIn, _lhsOtrueReviews, _lhsOtrueReviewsRDL), tl) = tickAG (realv0 (tguestbook_tl cur) pDL_trueReviews)
    res = tickAG (update (cur {
                            tguestbook_v0 = memv0,
                            tguestbook_v0_dirty = False,
                            tguestbook_tl = tl
                          }))
    memv0 :: (TGuestbook top) -> (forall t. (Path DL t) -> Path DL t) -> ((Set Name, DL, DLR DL), TGuestbook top)
    memv0 cur' pDL_trueReviews' = tickAG (if not (tguestbook_v0_dirty cur')
                                          then ((_lhsOsignedIn, _lhsOtrueReviews, List_Ref (pDL_trueReviews End)), cur')
                                          else v0 cur' pDL_trueReviews')
  realv0 :: (TGuestbook top) -> (forall t. (Path DL t) -> Path DL t) -> ((Set Name, DL, DLR DL), TGuestbook top)
  realv0 tl0 pDL_trueReviews = ((_lhsOsignedIn, _lhsOtrueReviews, _lhsOtrueReviewsRDL), tl1) where
    ((_tlIsignedIn, _tlItrueReviews, _tlItrueReviewsRDL), tl1) = tguestbook_v0 tl0 tl0 (pDL_trueReviews . id)
    _lhsOsignedIn = tickSem (Set.insert _name _tlIsignedIn)
    _loc_trueReviews = tickSem _tlItrueReviews
    _loc_trueReviewsRDL = _tlItrueReviewsRDL
    _lhsOtrueReviews = tickSem _loc_trueReviews
    _lhsOtrueReviewsRDL = _loc_trueReviewsRDL

semGuestbook_Leave :: forall top. Name -> Double -> String -> (TGuestbook top) -> TGuestbook top
semGuestbook_Leave _name _grade _review _tl = TGuestbookLeave {
                                                tguestbook_lookup = lookup,
                                                tguestbook_change = change,
                                                tguestbook_v0 = v0,
                                                tguestbook_v0_dirty = True,
                                                tguestbook_tl = _tl
                                              } where
  lookup :: forall t. (TGuestbook top) -> (Path Guestbook t) -> SemType t top
  lookup cur End = tickAG cur
  lookup cur (GuestbookLeaveP_tl ps) = tickAG (tguestbook_lookup (tguestbook_tl cur) (tguestbook_tl cur) ps)
  change :: forall r. (TGuestbook top) -> (forall t. (Path top t) -> SemType t top) -> (Path Guestbook r) -> (ReplType r top) -> TGuestbook top
  change cur lu End repl = tickAG (semGuestbookR lu repl)
  change cur lu (GuestbookLeaveP_tl ps) repl = tickAG (update_tl ps (cur {
                                                                       tguestbook_tl = tguestbook_change (tguestbook_tl cur) (tguestbook_tl cur) lu ps repl
                                                                     }))
  update :: (TGuestbook top) -> TGuestbook top
  update cur = tickAG (cur {
                         tguestbook_v0_dirty = tguestbook_v0_dirty cur || tguestbook_v0_dirty (tguestbook_tl cur)
                       })
  update_tl :: (Path f t) -> (TGuestbook top) -> TGuestbook top
  update_tl End cur = tickAG (cur {
                                tguestbook_v0_dirty = True
                              })
  update_tl _ cur = tickAG (update cur)
  v0 :: (TGuestbook top) -> (forall t. (Path DL t) -> Path DL t) -> ((Set Name, DL, DLR DL), TGuestbook top)
  v0 cur pDL_trueReviews = tickAG ((_lhsOsignedIn, _lhsOtrueReviews, _lhsOtrueReviewsRDL), res) where
    ((_lhsOsignedIn, _lhsOtrueReviews, _lhsOtrueReviewsRDL), tl) = tickAG (realv0 (tguestbook_tl cur) pDL_trueReviews)
    res = tickAG (update (cur {
                            tguestbook_v0 = memv0,
                            tguestbook_v0_dirty = False,
                            tguestbook_tl = tl
                          }))
    memv0 :: (TGuestbook top) -> (forall t. (Path DL t) -> Path DL t) -> ((Set Name, DL, DLR DL), TGuestbook top)
    memv0 cur' pDL_trueReviews' = tickAG (if not (tguestbook_v0_dirty cur')
                                          then ((_lhsOsignedIn, _lhsOtrueReviews, List_Ref (pDL_trueReviews End)), cur')
                                          else v0 cur' pDL_trueReviews')
  realv0 :: (TGuestbook top) -> (forall t. (Path DL t) -> Path DL t) -> ((Set Name, DL, DLR DL), TGuestbook top)
  realv0 tl0 pDL_trueReviews = ((_lhsOsignedIn, _lhsOtrueReviews, _lhsOtrueReviewsRDL), tl1) where
    ((_tlIsignedIn, _tlItrueReviews, _tlItrueReviewsRDL), tl1) = tguestbook_v0 tl0 tl0 (pDL_trueReviews . if Set.member _name _tlIsignedIn
                                                                                                          then PathL_tl . id
                                                                                                          else id)
    _lhsOsignedIn = tickSem (Set.delete _name _tlIsignedIn)
    _loc_trueReviews = tickSem (if Set.member _name _tlIsignedIn then (:) _grade _tlItrueReviews else _tlItrueReviews)
    _loc_trueReviewsRDL = if Set.member _name _tlIsignedIn
                          then ListConsR _grade _tlItrueReviewsRDL
                          else _tlItrueReviewsRDL
    _lhsOtrueReviews = tickSem _loc_trueReviews
    _lhsOtrueReviewsRDL = _loc_trueReviewsRDL

semTop_Top :: forall top. (TGuestbook top) -> TTop top
semTop_Top _gb = TTopTop {
                   ttop_lookup = lookup,
                   ttop_change = change,
                   ttop_v0 = v0,
                   ttop_v0_dirty = True,
                   ttop_gb = _gb,
                   ttop_revs = Nothing
                 } where
  lookup :: forall t. (TTop top) -> (Path Top t) -> SemType t top
  lookup cur End = tickAG cur
  lookup cur (TopTopP_gb ps) = tickAG (tguestbook_lookup (ttop_gb cur) (ttop_gb cur) ps)
  change :: forall r. (TTop top) -> (forall t. (Path top t) -> SemType t top) -> (Path Top r) -> (ReplType r top) -> TTop top
  change cur lu End repl = tickAG (semTopR lu repl)
  change cur lu (TopTopP_gb ps) repl = tickAG (update_gb ps (cur {
                                                               ttop_gb = tguestbook_change (ttop_gb cur) (ttop_gb cur) lu ps repl
                                                             }))
  update :: (TTop top) -> TTop top
  update cur = tickAG (cur {
                         ttop_v0_dirty = ttop_v0_dirty cur || tguestbook_v0_dirty (ttop_gb cur)
                       })
  update_gb :: (Path f t) -> (TTop top) -> TTop top
  update_gb End cur = tickAG (cur {
                                ttop_v0_dirty = True
                              })
  update_gb _ cur = tickAG (update cur)
  v0 :: (TTop top) -> (Double, TTop top)
  v0 cur = tickAG (_lhsOaverage, res) where
    (_lhsOaverage, revs, gb) = tickAG (realv0 (ttop_revs cur, ttop_gb cur))
    res = tickAG (update (cur {
                            ttop_v0 = memv0,
                            ttop_v0_dirty = False,
                            ttop_revs = Just revs,
                            ttop_gb = gb
                          }))
    memv0 :: (TTop top) -> (Double, TTop top)
    memv0 cur' = tickAG (if not (ttop_v0_dirty cur')
                         then (_lhsOaverage, cur')
                         else v0 cur')
  realv0 :: (Maybe (TDL DL), TGuestbook top) -> (Double, TDL DL, TGuestbook top)
  realv0 (_revs, gb0) = (_lhsOaverage, revs1, gb1) where
    ((_gbIsignedIn, _gbItrueReviews, _gbItrueReviewsRDL), gb1) = tguestbook_v0 gb0 gb0 id
    _loc_inst_revs = tickSem _gbItrueReviews
    _loc_inst_revsRDL = _gbItrueReviewsRDL
    revs0 = case _revs of
              (Nothing) -> semDL _loc_inst_revs
              (Just v) -> tdl_change v v (tdl_lookup v v) End _loc_inst_revsRDL
    ((_revsIaverage, _revsIlength, _revsIsum), revs1) = tdl_v0 revs0 revs0
    _lhsOaverage = tickSem _revsIaverage

