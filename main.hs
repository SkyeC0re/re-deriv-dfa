{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE MultiWayIf #-}

import Prelude
import Data.Sort as Sort
import Data.HashSet as HashSet
import Data.HashMap.Strict as HashMap
import Data.Map as Map
import Language.HaLex.Dfa as Dfa
import Data.Hashable as Hashable
import GHC.Generics (Generic)

data Regex  = Empty
            | Eps
            | CharSet (HashSet Char)
            | Not Regex
            | Star Regex
            | Intersect Regex Regex
            | Union Regex Regex
            | Dot Regex Regex
            deriving (Show, Generic)

data DfaVars = DfaVars ([Char]) (HashMap Regex (HashMap Char Regex))

instance Eq Regex where
    (==) Empty Empty = True
    (==) Eps Eps = True
    (==) (CharSet c1) (CharSet c2) = c1 == c2
    (==) (Not r1) (Not r2) = r1 == r2
    (==) (Star r1) (Star r2) = r1 == r2
    (==) (Intersect r1 r2) (Intersect s1 s2) = (r1 == s1) && (r2 == s2)  
    (==) (Union r1 r2) (Union s1 s2) = (r1 == s1) && (r2 == s2)
    (==) (Dot r1 r2) (Dot s1 s2) = (r1 == s1) && (r2 == s2)
    (==) _ _ = False

termValue:: Regex -> Int
termValue Empty = 0
termValue Eps = 1
termValue (CharSet _) = 2
termValue (Not _) = 3
termValue (Star _) = 4
termValue (Intersect _ _) = 5
termValue (Union _ _) = 6
termValue (Dot _ _) = 7

instance Ord Regex where
    (<=) (CharSet c1) (CharSet c2) = c1 <= c2
    (<=) (Not r) (Not s) = r <= s
    (<=) (Star r) (Star s) = r <= s
    (<=) (Intersect r1 r2) (Intersect s1 s2)
        | r1 == s1 = r2 <= s2
        | otherwise = r1 <= s1
    (<=) (Union r1 r2) (Union s1 s2)
        | r1 == s1 = r2 <= s2
        | otherwise = r1 <= s1
    (<=) (Dot r1 r2) (Dot s1 s2)
        | r1 == s1 = r2 <= s2
        | otherwise = r1 <= s1
    (<=) r s = (termValue r) <= (termValue s)

instance Hashable Regex

invertNull:: Regex -> Regex
invertNull Empty = Eps
invertNull Eps = Empty

nullable::Regex -> Regex
nullable Empty = Empty
nullable Eps = Eps
nullable (CharSet _) = Empty
nullable (Star _) = Eps
nullable (Not r) = invertNull (nullable r)
nullable (Dot r1 r2) =  Intersect (nullable r1) (nullable r2)
nullable (Union r1 r2) = Union (nullable r1) (nullable r2)
nullable (Intersect r1 r2) = Intersect (nullable r1) (nullable r2)

deriv:: Regex -> Char -> Regex
deriv (CharSet cs) sy
    | HashSet.member sy cs = Eps
    | otherwise = Empty
deriv (Dot r1 r2) sy = Union (Dot (deriv r1 sy) r2) (Dot (nullable r1) (deriv r2 sy))
deriv (Star r) sy = Dot (deriv r sy) (Star r)
deriv (Union r1 r2) sy = Union (deriv r1 sy) (deriv r2 sy)
deriv (Intersect r1 r2) sy = Intersect (deriv r1 sy) (deriv r2 sy)
deriv (Not r) sy = Not (deriv r sy)
deriv _ _ = Empty

simplifyUnion:: Regex -> Regex
simplifyUnion union = unpackUnionList (Sort.uniqueSort (simplifiedUnionList union))

simplifiedUnionList:: Regex -> [Regex]
simplifiedUnionList (Union r1 r2) = mergeUnionList (simplifiedUnionList r1) (simplifiedUnionList r2)
simplifiedUnionList r  = [simplify r]

mergeUnionList:: [Regex] -> [Regex] -> [Regex]
mergeUnionList [Not Empty] _ = [Not Empty]
mergeUnionList _ [Not Empty] = [Not Empty]
mergeUnionList [Empty] lst = lst
mergeUnionList lst [Empty] = lst
mergeUnionList l1 l2 = l1 ++ l2

unpackUnionList:: [Regex] -> Regex
unpackUnionList [r] = r
unpackUnionList (r:rs) = Union r (unpackUnionList rs)

simplifyIntersect:: Regex -> Regex
simplifyIntersect intersect = unpackIntersectList (Sort.uniqueSort (simplifiedIntersectList intersect))

simplifiedIntersectList:: Regex -> [Regex]
simplifiedIntersectList (Intersect r1 r2) = mergeIntersectList (simplifiedIntersectList r1) (simplifiedIntersectList r2)
simplifiedIntersectList r = [r]

mergeIntersectList:: [Regex] -> [Regex] -> [Regex]
mergeIntersectList [Empty] _ = [Empty]
mergeIntersectList _ [Empty] = [Empty]
mergeIntersectList [Not Empty] lst = lst
mergeIntersectList lst [Not Empty] = lst
mergeIntersectList l1 l2 = l1 ++ l2

unpackIntersectList:: [Regex] -> Regex
unpackIntersectList [r] = r
unpackIntersectList (r:rs) = Intersect r (unpackIntersectList rs)

simplifyDot:: Regex -> Regex
simplifyDot dot = unpackDotList $ simplifiedDotList dot

simplifiedDotList:: Regex -> [Regex]
simplifiedDotList (Dot r1 r2) = mergeDotList (simplifiedDotList r1) (simplifiedDotList r2)
simplifiedDotList r = [r]

mergeDotList:: [Regex] -> [Regex] -> [Regex]
mergeDotList [Empty] _ = [Empty]
mergeDotList _ [Empty] = [Empty]
mergeDotList [Eps] lst = lst 
mergeDotList lst [Eps] = lst
mergeDotList l1 l2 = l1 ++ l2

unpackDotList:: [Regex] -> Regex
unpackDotList [r] = r
unpackDotList (r:rs) = Dot r (unpackDotList rs)

simplify:: Regex -> Regex
simplify (Union r1 r2) = simplifyUnion (Union (simplify r1)  (simplify r2))
simplify (Intersect r1 r2) = simplifyIntersect (Intersect (simplify r1) (simplify r2))
simplify (Dot r1 r2) = simplifyDot (Dot (simplify r1) (simplify r2))
simplify (Not (Not r)) = simplify r
simplify (Star (Star r)) = simplify (Star r)
simplify (Star Eps) = Eps
simplify (Star Empty) = Eps
simplify r = r

findTransition:: (HashMap Regex (HashMap Char Regex)) -> Regex -> Regex -> Char -> Regex
findTransition tt def inst sy = case (HashMap.lookup inst tt) of
    Nothing -> def
    Just trans -> case (HashMap.lookup sy trans) of
                    Nothing -> def
                    Just outst -> outst 

constructDfa:: [Char] -> Regex -> (Dfa Regex Char)
constructDfa alph r = 
    let sr = simplify r
        tt = HashMap.singleton sr (HashMap.empty)
        fs = if
            | HashMap.member Eps tt -> [Eps]
            | otherwise -> []
        sts = HashMap.keys tt
    in Dfa alph sts sr fs (findTransition tt Empty)
        


ttConstruct:: (HashMap Regex (HashMap Char Regex)) -> [Char] -> [Char] -> Regex -> (HashMap Regex (HashMap Char Regex))
ttConstruct tt alph [] r = tt
ttConstruct tt alph (x:xs) r =
    let sdr = simplify (deriv r x)
        tt = case (HashMap.lookup sdr tt) of
                Nothing -> ttConstruct (HashMap.insert r (HashMap.singleton x sdr) tt) alph alph sdr
                Just st -> HashMap.insert r (HashMap.insert x sdr st) tt
    in ttConstruct tt alph xs r       

          

main = do
    let x = Union Empty Eps
    let y = Union (CharSet $ HashSet.singleton 'c') (Dot Eps Eps)
    let dfa = constructDfa ['a', 'b'] y
    print (y)
