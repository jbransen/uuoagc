{-# LANGUAGE CPP #-}

-- UUAGC 0.9.51.1 (GuestbookAG.ag)
module Main where

import Data.Set (Set)
import qualified Data.Set as Set
#if MEASURE_TIME
import Criterion
import Criterion.Main
#endif

type Name = String

example1 :: Guestbook
example1 = Leave "Bransen" 7.6 "I liked the fast internet connection" $ Leave "Dijkstra" 8 "The atmosphere is great for taking pictures!" $ Arrive "Dijkstra" $ Leave "Swierstra" 6 "Nice hotel, but the beds are too short" $ Arrive "Bransen" $ Arrive "Swierstra" Empty

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
computeGrade :: Guestbook -> Double
computeGrade g = average_Syn_Top $ wrap_Top (semTop $ Top g) Inh_Top

-- Changes
applyChange :: Guestbook -> Change -> Guestbook
applyChange gb ch = f ch gb where
  f (_, 0, r) _ = g r
  f (s, m, r) (Arrive n t) = Arrive n (f (s, m - 1, r) t)
  f (s, m, r) (Leave n g c t) = Leave n g c (f (s, m - 1, r) t)
  g (Ref p) = lookup gb p
  g (EmptyR) = Empty
  g (ArriveR n r) = Arrive n (g r)
  g (LeaveR n gr c r) = Leave n gr c (g r)
  lookup gb 0 = gb
  lookup (Arrive _ t) n = lookup t (n - 1)
  lookup (Leave _ _ _ t) n = lookup t (n - 1)

-- Main
main :: IO ()
main = do
  f <- readFile "large_guestbook.txt"
  let gb = parseGuestbook f
  print $ computeGrade gb -- force evaluation
  f2 <- readFile "large_guestbook_changes.txt"
  let ch = parseChanges f2
  let gbs' = map (applyChange gb) ch
  mapM_ (print . computeGrade) gbs' -- force evaluation
#if MEASURE_TIME
  let bi = nf computeGrade gb
--  benchmark bi -- trial run, to make sure memory is allocated and so on
  defaultMain $
    bench "initial" bi
    : [ bench name $ nf (\(gb,gb') -> (computeGrade gb, computeGrade gb')) (gb, gb')
      | ((name,_,_), gb') <- zip ch gbs'
      ]
#endif

-- DL ----------------------------------------------------------
type DL = [(Double)]
-- cata
sem_DL :: DL ->
          T_DL
sem_DL list =
    (Prelude.foldr sem_DL_Cons sem_DL_Nil list)
-- semantic domain
type T_DL = ( Double,Double,Double)
data Inh_DL = Inh_DL {}
data Syn_DL = Syn_DL {average_Syn_DL :: Double,length_Syn_DL :: Double,sum_Syn_DL :: Double}
wrap_DL :: T_DL ->
           Inh_DL ->
           Syn_DL
wrap_DL sem (Inh_DL) =
    (let ( _lhsOaverage,_lhsOlength,_lhsOsum) = sem
     in  (Syn_DL _lhsOaverage _lhsOlength _lhsOsum))
sem_DL_Cons :: Double ->
               T_DL ->
               T_DL
sem_DL_Cons hd_ tl_ =
    (let _lhsOaverage :: Double
         _lhsOlength :: Double
         _lhsOsum :: Double
         _tlIaverage :: Double
         _tlIlength :: Double
         _tlIsum :: Double
         _length =
             (
              _tlIlength + 1
              
              )
         _sum =
             (
              _tlIsum + hd_
              
              )
         _lhsOaverage =
             (
              _sum     / _length
              
              )
         _lhsOlength =
             (
              _length
              
              )
         _lhsOsum =
             (
              _sum
              
              )
         ( _tlIaverage,_tlIlength,_tlIsum) =
             tl_
     in  ( _lhsOaverage,_lhsOlength,_lhsOsum))
sem_DL_Nil :: T_DL
sem_DL_Nil =
    (let _lhsOlength :: Double
         _lhsOsum :: Double
         _lhsOaverage :: Double
         _lhsOlength =
             (
              0
              
              )
         _lhsOsum =
             (
              0
              
              )
         _lhsOaverage =
             (
              0
              
              )
     in  ( _lhsOaverage,_lhsOlength,_lhsOsum))
-- Guestbook ---------------------------------------------------
data Guestbook = Empty
               | Arrive (Name) (Guestbook)
               | Leave (Name) (Double) (String) (Guestbook)
               deriving Show
-- cata
semGuestbook :: Guestbook -> T_Guestbook
semGuestbook Empty = semGuestbookEmpty
semGuestbook (Arrive _name _tl) = semGuestbookArrive _name (semGuestbook _tl)
semGuestbook (Leave _name _grade _review _tl) = semGuestbookLeave _name _grade _review (semGuestbook _tl)

-- semantic domain
type T_Guestbook = (Set Name, [Double])
data Inh_Guestbook = Inh_Guestbook {}
data Syn_Guestbook = Syn_Guestbook {signedIn_Syn_Guestbook :: (Set Name),trueReviews_Syn_Guestbook :: ([Double])}
wrap_Guestbook :: T_Guestbook ->
                  Inh_Guestbook ->
                  Syn_Guestbook
wrap_Guestbook sem (Inh_Guestbook) =
    (let ( _lhsOsignedIn,_lhsOtrueReviews) = sem
     in  (Syn_Guestbook _lhsOsignedIn _lhsOtrueReviews))
semGuestbookEmpty :: T_Guestbook
semGuestbookEmpty =
    (let _lhsOsignedIn :: (Set Name)
         _lhsOtrueReviews :: ([Double])
         _lhsOsignedIn =
             (
              Set.empty
              
              )
         _trueReviews =
             (
              []
              
              )
         _lhsOtrueReviews =
             (
              _trueReviews
              
              )
     in  ( _lhsOsignedIn,_lhsOtrueReviews))

semGuestbookArrive :: Name -> T_Guestbook -> T_Guestbook
semGuestbookArrive name_ tl_ =
     let _lhsOsignedIn :: Set Name
         _lhsOsignedIn = name_ `Set.insert` _tlIsignedIn
         _trueReviews = _tlItrueReviews
         _lhsOtrueReviews :: [Double]
         _lhsOtrueReviews = _trueReviews
         _tlIsignedIn :: Set Name
         _tlItrueReviews :: [Double]
         ( _tlIsignedIn,_tlItrueReviews) = tl_
     in  ( _lhsOsignedIn,_lhsOtrueReviews)

semGuestbookLeave :: Name ->
                       Double ->
                       String ->
                       T_Guestbook ->
                       T_Guestbook
semGuestbookLeave name_ grade_ review_ tl_ =
    (let _lhsOsignedIn :: (Set Name)
         _lhsOtrueReviews :: ([Double])
         _tlIsignedIn :: (Set Name)
         _tlItrueReviews :: ([Double])
         _lhsOsignedIn =
             (
              name_ `Set.delete` _tlIsignedIn
              
              )
         _trueReviews =
             (
              if   name_ `Set.member` _tlIsignedIn
              then grade_ : _tlItrueReviews
              else          _tlItrueReviews
              
              )
         _lhsOtrueReviews =
             (
              _trueReviews
              
              )
         ( _tlIsignedIn,_tlItrueReviews) =
             tl_
     in  ( _lhsOsignedIn,_lhsOtrueReviews))
-- Top ---------------------------------------------------------
data Top = Top (Guestbook)
-- cata
semTop :: Top ->
           T_Top
semTop (Top _gb) =
    (semTopTop (semGuestbook _gb))
-- semantic domain
type T_Top = ( Double)
data Inh_Top = Inh_Top {}
data Syn_Top = Syn_Top {average_Syn_Top :: Double}
wrap_Top :: T_Top ->
            Inh_Top ->
            Syn_Top
wrap_Top sem (Inh_Top) =
    (let ( _lhsOaverage) = sem
     in  (Syn_Top _lhsOaverage))

semTopTop :: T_Guestbook -> T_Top
semTopTop gb_ =
     let _gbIsignedIn :: (Set Name)
         _gbItrueReviews :: ([Double])
         ( _gbIsignedIn,_gbItrueReviews) = gb_
         revs_val_ :: DL
         revs_val_ = _gbItrueReviews
         _lhsOaverage :: Double
         _lhsOaverage = _revsIaverage
         _revsIaverage :: Double
         _revsIlength :: Double
         _revsIsum :: Double
         ( _revsIaverage,_revsIlength,_revsIsum) = sem_DL revs_val_
     in  ( _lhsOaverage)
