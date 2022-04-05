-----------------------------------------------------------------------------
-- |
-- Module      :  Examples
-- Copyright   :  (c) Ricardo Peña, December 2016               
-- License     :  LGPL
--
-- Maintainer  :  ricardo@sip.ucm.es
-- Stability   :  provisional
-- Portability :  portable
--
-- Liquid Haskell examples in the paper "An Introduction to Liquid Haskell"
-- PROLE 2016, selected papers published in EPTCS

-----------------------------------------------------------------------------
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--short-names"    @-}

 
module Lists where
import Prelude hiding (head, max)


--
-- Some liquid types
--

{-@ type Nat     = {v:Int | 0 <= v} @-}
{-@ type Pos     = {v:Int | 0 <  v} @-}
{-@ type NonZero = {v:Int | 0 /= v} @-}



--
-- Sorted lists
--

data IncList a =
    Emp
  | (:<) { hd :: a, tl :: IncList a }

infixr 9 :<

{-@ data IncList a = Emp
                     | (:<) { hd::a, tl::IncList {v:a | hd <= v}} @-}

okList  = 1 :< 2 :< 3 :< Emp      -- accepted by LH

--badList = 2 :< 1 :< 3 :< Emp       -- rejected by LH

                     
-- *** Illegal definition: replace '>' by '<='

{-@ insert :: (Ord a) => a -> IncList a -> IncList a @-}
insert y Emp                   = y :< Emp
insert y (x :< xs) | y <=  x   = y :< x :< xs 
                   | otherwise = x :< insert y xs


{-@ insertSort :: (Ord a) => [a] -> IncList a @-}
insertSort []     = Emp 
insertSort (x:xs) = insert x (insertSort xs)
 

{-@ merge :: (Ord a) => IncList a -> IncList a -> IncList a @-}
merge Emp       ys        = ys
merge xs@(_ :< _)       Emp       = xs 
merge (x :< xs) (y :< ys)
  | x <= y                = x :< merge xs (y :< ys)
  | otherwise             = y :< merge (x :< xs) ys


{-@ mergeSort :: (Ord a) => [a] -> IncList a @-}
mergeSort []     = Emp
mergeSort [x]    = x :< Emp
mergeSort xs     = merge (mergeSort ys) (mergeSort zs)
  where (ys, zs) = split xs
        split (x:y:zs)  = (x:xs, y:ys) 
            where (xs,ys) = split zs
        split xs        = (xs, [])



{-@ quickSort :: (Ord a) => [a] -> IncList a @-}
quickSort []     = Emp
quickSort (x:xs) = join x lessers greaters
  where lessers  = quickSort [y | y <- xs, y < x ]
        greaters = quickSort [z | z <- xs, z >= x]


-- Exercise: The signature is wrong. Refine it

{-@ join :: x:a ->l1:IncList { v:a | x > v } -> l2:IncList { v':a | x <= v' } -> IncList a @-}
join z Emp       ys = z :< ys 
join z (x :< xs) ys = x :< join z xs ys 


--
-- Totality
--

{-@ measure notEmpty @-}
notEmpty :: [a] -> Bool
notEmpty []    = False
notEmpty (_:_) = True

{-@ type NEList a = {v:[a] | notEmpty v} @-}

{-@ head :: NEList a -> a  @-}
head :: [a] -> a
head (x:_) = x

-- *** Illegal use of head
--h = head []







