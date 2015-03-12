{-# LANGUAGE GADTs #-}
module Main where

import Data.Set (Set)
import qualified Data.Set as Set
import Test.QuickCheck.Gen
import System.IO.Unsafe (unsafePerformIO)
import Control.Monad

-- Data types
type Name = String

data Entry = Arrive Name
           | Leave Name Double String

type Guestbook = [Entry]


signedIn :: Guestbook -> Set Name
signedIn [] = Set.empty
signedIn (Arrive n    : xs) = n `Set.insert` signedIn xs
signedIn (Leave n _ _ : xs) = n `Set.delete` signedIn xs


-- Showing
instance Show Entry where
  show (Arrive n) = "ARRIVE " ++ n
  show (Leave n g c) = "LEAVE " ++ n ++ " - " ++ show g ++ " - " ++ c

-- Parsing
parseGuestbook :: String -> Guestbook
parseGuestbook = map parseEntry . lines

parseEntry :: String -> Entry
parseEntry s = case words s of
  ["ARRIVE", n] -> Arrive n
  ("LEAVE":n:"-":g:"-":cs) -> Leave n (read g) (unwords cs)

-- Generation
maxGuests :: Int
maxGuests = 50

genGB :: Int -> Gen (Set Name, Guestbook)
genGB 0 = return (Set.empty, [])
genGB n = do
  (si,g) <- genGB (n - 1)
  let guests = Set.toList si
  arr <- if length guests < maxGuests
         then do n <- genName
                 return $ (:) $ (15, return (n `Set.insert` si, Arrive n))
         else return id
  lea <- if not (null guests)
         then do n <- elements guests
                 g <- genGrade
                 c <- genComment
                 return $ (:) $ (10, return (n `Set.delete` si, Leave n g c))
         else return id
  -- Wrong leave
  let wl = (1, do n <- genName
                  g <- genGrade
                  c <- return "This is an invalid leave"
                  return (n `Set.delete` si, Leave n g c))
  (si', e) <- frequency $ arr $ lea $ [wl]
  return (si', e : g)

genName :: Gen String
genName = elements allNames

-- The 1000 most popular surnames in the US from
-- http://www.census.gov/topics/population/genealogy/data/2000_surnames.html
allNames :: [String]
allNames = unsafePerformIO $ do
  f <- readFile "top1000_names.txt"
  return $ lines f

genComment :: Gen String
genComment = return "No comment"

genGrade :: Gen Double
genGrade = elements $ map (/10) [0..100]

-- Changes to the guestbook
type MyPath = Int

data MyGuestbookR
  = Ref MyPath
  | EmptyR
  | ArriveR Name MyGuestbookR
  | LeaveR Name Double String MyGuestbookR
  deriving (Read, Show)

type Change = (String, Int, MyGuestbookR)

changeRange :: (Int,Int)
changeRange = (10,20)

genDelete :: Guestbook -> Gen Change
genDelete gb = do
  pos <- choose changeRange
  return ("delete", pos, Ref (pos + 1))

genInsertA :: Guestbook -> Gen Change
genInsertA gb = do
  pos <- choose changeRange
  n <- genName
  return ("insert arrive", pos, ArriveR n (Ref pos))

genInsertL :: Guestbook -> Gen Change
genInsertL gb = do
  pos <- choose changeRange
  let guests = Set.toList $ signedIn gb
  n <- elements guests
  g <- genGrade
  c <- genComment
  return ("insert leave", pos, LeaveR n g c (Ref pos))

genChanges :: Guestbook -> Gen [Change]
genChanges gb = sequence [genDelete gb, genInsertL gb, genInsertA gb]

-- Main generate function
main :: IO ()
main = do
  g <- generate $ genGB 50000
  writeFile "large_guestbook.txt" $ unlines $ map show $ snd g
  c <- generate $ genChanges $ snd g
  writeFile "large_guestbook_changes.txt" $ unlines $ map show $ c
