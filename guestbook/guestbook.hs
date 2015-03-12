import Data.List
import Data.Set (Set)
import qualified Data.Set as Set

type Name = String

data Entry = Arrive Name
           | Leave Name Double String
           deriving (Show)

type Guestbook = [Entry]

example1 :: Guestbook
example1 = reverse [ Arrive "Swierstra", Arrive "Bransen", Leave "Swierstra" 6 "Nice hotel, but the beds are too short", Arrive "Dijkstra", Leave "Dijkstra" 8 "The atmosphere is great for taking pictures!", Leave "Bransen" 7.6 "I liked the fast internet connection"]

-- Approach 1
average :: [Double] -> Double
average nums = sum nums / genericLength nums

avgGrade1 :: Guestbook -> Double
avgGrade1 gb = average [ g | Leave _ g _ <- gb ] 

-- Approach 2
avgGrade2 :: Guestbook -> Double
avgGrade2 = average . trueReviews

trueReviews :: Guestbook -> [Double]
trueReviews [] = []
trueReviews (Arrive _ : xs) = trueReviews xs
trueReviews (Leave n g _ : xs) = if   n `Set.member` signedIn xs
                                 then g : trueReviews xs
                                 else     trueReviews xs

signedIn :: Guestbook -> Set Name
signedIn [] = Set.empty
signedIn (Arrive n    : xs) = n `Set.insert` signedIn xs
signedIn (Leave n _ _ : xs) = n `Set.delete` signedIn xs

-- Approach 3
avgGrade3 :: Guestbook -> Double
avgGrade3 = average . snd . tupled where
  tupled :: Guestbook -> (Set Name, [Double])
  tupled [] = (Set.empty, [])
  tupled (Arrive n    : xs) = let (signedIn, trueReviews) = tupled xs
                              in  ( n `Set.insert` signedIn
                                  , trueReviews)
  tupled (Leave n g _ : xs) = let (signedIn, trueReviews) = tupled xs
                              in  ( n `Set.delete` signedIn
                                  , if   n `Set.member` signedIn
                                    then g : trueReviews
                                    else     trueReviews )

-- Approach 4
type State4 = (Set Name, [Double])

avgGradeI4 :: State4 -> Double
avgGradeI4 = average . snd

avgGradeU4 :: Entry -> State4 -> State4
avgGradeU4 (Arrive n) (signedIn, trueReviews)
  = (n `Set.insert` signedIn, trueReviews)
avgGradeU4 (Leave n g _) (signedIn, trueReviews)
  = ( n `Set.delete` signedIn
    , if   n `Set.member` signedIn
      then g : trueReviews
      else     trueReviews )

avgGrade4 :: Guestbook -> Double
avgGrade4 = avgGradeI4 . foldr avgGradeU4 (Set.empty, [])


-- Approach 5
type StateAvg = (Double, Double)

averageI5 :: StateAvg -> Double
averageI5 (sum, len) = sum / len

averageU5 :: Double -> StateAvg -> StateAvg
averageU5 x (sum, len) = (sum + x, len + 1)


type State5 = (Set Name, StateAvg)

avgGradeI5 :: State5 -> Double
avgGradeI5 = averageI5 . snd

avgGradeU5 :: Entry -> State5 -> State5
avgGradeU5 (Arrive n) (signedIn, avgState)
  = (n `Set.insert` signedIn, avgState)
avgGradeU5 (Leave n g _) (signedIn, avgState)
  = ( n `Set.delete` signedIn
    , if   n `Set.member` signedIn
      then averageU5 g avgState
      else             avgState )

avgGrade5 :: Guestbook -> Double
avgGrade5 = avgGradeI5 . foldr avgGradeU5 (Set.empty, (0, 0))


{-
-- This is actually maybe nicer, but doesn't illustrate the problem so well
avgGrade5 :: Guestbook -> Double
avgGrade5 gb = sum / len where
  (_, (sum, len)) = tupled gb
  tupled :: Guestbook -> (Set Name, (Double, Double))
  tupled [] = (Set.empty, (0, 0))
  tupled (Arrive n    : xs) = let (signedIn, (sum, len)) = tupled xs
                              in  ( n `Set.insert` signedIn
                                  , (sum, len))
  tupled (Leave n g _ : xs) = let (signedIn, (sum, len)) = tupled xs
                              in  ( n `Set.delete` signedIn
                                  , if   n `Set.member` signedIn
                                    then (sum + g, len + 1)
                                    else (sum, len) )

-- Higher order version
avgGrade5 :: Guestbook -> Double
avgGrade5 gb = sum / len where
  grades = snd $ tupled gb
  (sum,len) = sumLen grades
  sumLen :: [Double] -> (Double, Double)
  sumLen [] = (0, 0)
  sumLen (x : xs) = let (sum,len) = sumLen xs
                    in  (sum + x, len + 1)
  tupled :: Guestbook -> (Set Name, [Double])
  tupled [] = (Set.empty, [])
  tupled (Arrive n    : xs) = let (signedIn, trueReviews) = tupled xs
                              in  ( n `Set.insert` signedIn
                                  , trueReviews)
  tupled (Leave n g _ : xs) = let (signedIn, trueReviews) = tupled xs
                              in  ( n `Set.delete` signedIn
                                  , if   n `Set.member` signedIn
                                    then g : trueReviews
                                    else     trueReviews )
-}
