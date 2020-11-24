{-
    Module for creating, transforming, vizualizing and simplifying Regular Expressions (REs)
    and Deterministic Finite Automata (DFAs) using the notions and principles described in the paper:
    'Regular-expression derivatives re-examined' by Scott Owens, John Reppy and Aaron Turon.

    -- Creator: Christoff van Zyl
    -- Email: Stoffel1997@Gmail.com | 20072015@sun.ac.za
-}

{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE MultiWayIf #-}

module ReDfa
    ( Regex (..)
    , sizeRe
    , Dfa.sizeDfa
    , simplify
    , simplified
    , nullable
    , regexNullable
    , growDissimilarListSerialAB
    , growValidStringsAB
    , constructDfa
    , dfa2Dot2File
    , dfa2Dot
    , isMinimalDfa
    , isMinimalRe
    , parse
    , parseNF
    ) where

import Prelude
import Data.Sort as Sort
import Data.HashSet as HashSet
import Data.HashMap.Strict as HashMap
import Language.HaLex.Dfa as Dfa
import Data.Hashable as Hashable
import GHC.Generics (Generic)
import Language.HaLex.Minimize as Min
import Test.QuickCheck.Arbitrary
import Test.QuickCheck.Gen (elements)
import Test.QuickCheck.Gen as Gen
import Control.Applicative

{-|
    A Recursive Data Structure to represent REs. 
-}
data Regex  = CharSet (HashSet Char)        -- A character set. Matches any character in the set.
            | Empty                         -- The empty RE.
            | Eps                           -- The empty string. 
            | Not Regex                     -- Compliment (~)
            | Star Regex                    -- Kleene Star (*)
            | Intersect Regex Regex         -- Intersection (&)
            | Union Regex Regex             -- Union (+)
            | Dot Regex Regex               -- Concatenation (.)
            deriving (Generic, Ord, Eq)

data RegexSerial = EndSerial
                 | SEmpty RegexSerial
                 | SEps RegexSerial
                 | SCharSet (HashSet Char) RegexSerial
                 | SNot RegexSerial
                 | SStar RegexSerial
                 | SIntersect RegexSerial
                 | SUnion RegexSerial
                 | SDot RegexSerial
                 deriving (Show, Ord, Eq)

data ConsumedInfo = ConsumedInfo (Maybe Regex) RegexSerial

-- | Hashability is reguired to store unique states in a set
instance Hashable Regex

-- | A show instance which is the reverse of 'parse'.
instance Show Regex where
    show (Union r s) = "+" ++ (show r) ++ (show s)
    show (Intersect r s) = "&" ++ (show r) ++ (show s)
    show (Dot r s) = "." ++ (show r) ++ (show s)
    show (Not r) = "~" ++ (show r)
    show (Star r) = "*" ++ (show r)
    show (CharSet hs) = "[" ++ (HashSet.toList hs) ++ "]"
    show Empty = "0"
    show Eps = "e"

-- | Required to create arbitrary REs for QuickCheck.
instance Arbitrary Regex where
    arbitrary = genRegex

{-|
    INTERNAL. A generator for REs between size 1 and 30 with the alphabet {a, b}
-}
genRegex :: Gen Regex
genRegex = choose (1,30) >>= genSzdRegex

{-|
    INTERNAL. A generator for a RE of the specified size.
-}
genSzdRegex:: Int -> (Gen Regex)
genSzdRegex 0 = elements [Empty]
genSzdRegex 1 = generateRandomElem
genSzdRegex 2 = generateRandomUnOp <*> generateRandomElem
genSzdRegex d = 
    let dm1 = d - 1
    in frequency [(1, genUnOpOuter dm1), (5, choose (1, dm1 - 1) >>= (genBinOpOuter dm1))]

{-|
    INTERNAL. Helper function for 'genSzdRegex'
-}
genBinOpOuter:: Int -> Int -> (Gen Regex)
genBinOpOuter d ld = (generateRandomBinOp <*> (genSzdRegex ld)) <*> (genSzdRegex (d - ld))

{-|
    INTERNAL. Helper function for 'genSzdRegex'
-}
genUnOpOuter:: Int -> (Gen Regex)
genUnOpOuter d = generateRandomUnOp <*> (genSzdRegex d)

{-|
    INTERNAL. Helper function for 'genSzdRegex'
-}
generateRandomElem:: Gen Regex
generateRandomElem = elements [Empty, Eps, CharSet (HashSet.singleton 'a'), CharSet (HashSet.singleton 'b'), CharSet (HashSet.fromList "ab")]

{-|
    INTERNAL. Helper function for 'genSzdRegex'
-}
generateRandomUnOp:: (Gen (Regex -> Regex))
generateRandomUnOp = elements [Not, Star]

{-|
    INTERNAL. Helper function for 'genSzdRegex'
-}
generateRandomBinOp:: (Gen (Regex -> Regex -> Regex))
generateRandomBinOp = elements [Union, Intersect, Dot]

{-|
    Returns the size of a Regular expression. The empty expression (Empty), the empty string (Eps) and
    any character set {x1, x2, ..., xn} is considered size 1. All operators contribute 1 to the size in
    addition to their operands.
-}
sizeRe:: Regex -> Int
sizeRe Empty = 1
sizeRe Eps = 1
sizeRe (CharSet _) = 1
sizeRe (Not r) = 1 + (sizeRe r)
sizeRe (Star r) = 1 + (sizeRe r)
sizeRe (Intersect r1 r2) = 1 + (sizeRe r1) + (sizeRe r2)
sizeRe (Union r1 r2) = 1 + (sizeRe r1) + (sizeRe r2)
sizeRe (Dot r1 r2) =  1 + (sizeRe r1) + (sizeRe r2)

{-|
    Returns 'Eps' if the expression is nullable, 'Empty' otherwise.
-}
regexNullable:: Regex -> Regex
regexNullable r
    | (nullable r) == True = Eps
    | otherwise = Empty

{-|
    Returns 'True' if the expression nullable, 'False' otherwise.
-}
nullable:: Regex -> Bool
nullable Empty = False
nullable Eps = True
nullable (CharSet _) = False
nullable (Star _) = True
nullable (Not r) = not (nullable r)
nullable (Dot r1 r2) = (nullable r1) && (nullable r2)
nullable (Union r1 r2) = (nullable r1) || (nullable r2)
nullable (Intersect r1 r2) = (nullable r1) && (nullable r2)


{-|
    Computes the derivative of a RE with respect to a given character.
-}
deriv:: Regex -> Char -> Regex
deriv (CharSet cs) sy
    | HashSet.member sy cs = Eps
    | otherwise = Empty
deriv (Dot r1 r2) sy = {-Dot (deriv r1 sy) r2-} Union (Dot (deriv r1 sy) r2) (Dot (regexNullable r1) (deriv r2 sy))
deriv (Star r) sy = Dot (deriv r sy) (Star r)
deriv (Union r1 r2) sy = Union (deriv r1 sy) (deriv r2 sy)
deriv (Intersect r1 r2) sy = Intersect (deriv r1 sy) (deriv r2 sy)
deriv (Not r) sy = Not (deriv r sy)
deriv Empty _ = Empty
deriv Eps _ = Empty

{-|
    INTERNAL. Simplifies a RE with an outer 'Union' operator.
-}
simplifyUnion:: Regex -> Regex
simplifyUnion union = (unpackUnionList . mergeUnionCharSets . Sort.uniqueSort . simplifiedUnionList) union

{-|
    INTERNAL. Merges the first CharSets in a sorted list. They are guaranteed to be first from the derived order of the constructor.
-}
mergeUnionCharSets:: [Regex] -> [Regex]
mergeUnionCharSets ((CharSet sa):(CharSet sb):lst) = mergeUnionCharSets ((CharSet (HashSet.union sa sb)):lst)
mergeUnionCharSets lst = lst

{-|
    INTERNAL. Creates a list from the operands of nested 'Union' operators.
-}
simplifiedUnionList:: Regex -> [Regex]
simplifiedUnionList (Union r1 r2) = mergeUnionList (simplifiedUnionList r1) (simplifiedUnionList r2)
simplifiedUnionList r  =
    let sr = simplify r
    in if sr == r then [r] else simplifiedUnionList sr

{-|
    INTERNAL. Simplies and merges two lists of nested 'Union' operands.
-}
mergeUnionList:: [Regex] -> [Regex] -> [Regex]
mergeUnionList [Not Empty] _ = [Not Empty]
mergeUnionList _ [Not Empty] = [Not Empty]
mergeUnionList [Empty] lst = lst
mergeUnionList lst [Empty] = lst
mergeUnionList l1 l2 = l1 ++ l2

{-|
    INTERNAL. Recompiles a simplified 'Union' list back to a regular expression with a standard format.
-}
unpackUnionList:: [Regex] -> Regex
unpackUnionList [r] = r
unpackUnionList (r:rs) = Union r (unpackUnionList rs)

{-|
    INTERNAL. Simplifies a RE with an outer 'Intersect' operator.
-}
simplifyIntersect:: Regex -> Regex
simplifyIntersect intersect = unpackIntersectList (Sort.uniqueSort (simplifiedIntersectList intersect))

{-|
    INTERNAL. Creates a list from the operands of nested 'Intersect' operators.
-}
simplifiedIntersectList:: Regex -> [Regex]
simplifiedIntersectList (Intersect r1 r2) = mergeIntersectList (simplifiedIntersectList r1) (simplifiedIntersectList r2)
simplifiedIntersectList r = 
    let sr = simplify r
    in if sr == r then [r] else simplifiedIntersectList sr

{-|
    Simplies and merges two lists of nested 'Intersect' operands.
-}
mergeIntersectList:: [Regex] -> [Regex] -> [Regex]
mergeIntersectList [Empty] _ = [Empty]
mergeIntersectList _ [Empty] = [Empty]
mergeIntersectList [Not Empty] lst = lst
mergeIntersectList lst [Not Empty] = lst
mergeIntersectList l1 l2 = l1 ++ l2

{-|
    Recompiles a simplified 'Intersect' list back to a regular expression with a standard format.
-}
unpackIntersectList:: [Regex] -> Regex
unpackIntersectList [r] = r
unpackIntersectList (r:rs) = Intersect r (unpackIntersectList rs)

{-|
    Simplifies a RE with an outer 'Dot' operator.
-}
simplifyDot:: Regex -> Regex
simplifyDot dot = unpackDotList $ simplifiedDotList dot

{-|
    Creates a list from the operands of nested 'Dot' operators.
-}
simplifiedDotList:: Regex -> [Regex]
simplifiedDotList (Dot r1 r2) = mergeDotList (simplifiedDotList r1) (simplifiedDotList r2)
simplifiedDotList r =
    let sr = simplify r
    in if sr == r then [r] else simplifiedDotList sr

{-|
    INTERNAL. Simplies and merges two lists of nested 'Dot' operands.
-}
mergeDotList:: [Regex] -> [Regex] -> [Regex]
mergeDotList [Empty] _ = [Empty]
mergeDotList _ [Empty] = [Empty]
mergeDotList [Eps] lst = lst 
mergeDotList lst [Eps] = lst
mergeDotList l1 l2 = l1 ++ l2

{-|
    INTERNAL. Recompiles a simplified 'Dot' list back to a regular expression with a standard format.
-}
unpackDotList:: [Regex] -> Regex
unpackDotList [r] = r
unpackDotList (r:rs) = Dot r (unpackDotList rs)

{-|
    Simplifies a regular expression. Specifically it uses the notions of dissimilarity described in the paper listed
    at the start. By combining these dissimilarity principles, excluding the incorrect notion for ~S for the
    character set S, as well as a required format, all similar REs can be reduced to a single 'simplified' RE.

    The format here is that if smaller operands precede larger operands for Union and Intersection, and
    given a set of nested operators which are all either Union or Intersection, the following format describes the
    simplified RE:
    O1(r1 (O2 r2 (O3 ...))) where Ox refers to the operator and r1, r2, ... refers to operators of increasing order, based
    on some ordering method.

    For example Union(Union(r1 r2) r3) is considered not simplified, but Union(r1 Union(r2 r3)) is as long as r1<r2<r3.   
-}
simplify:: Regex -> Regex
simplify (Union r1 r2) = simplifyUnion (Union r1 r2)
simplify (Intersect r1 r2) = simplifyIntersect (Intersect r1 r2)
simplify (Dot r1 r2) = simplifyDot (Dot r1 r2)
simplify (Star r) = case simplify r of
    (Star s) -> s
    Eps -> Eps
    Empty -> Eps
    s -> Star s
simplify (Not r) = case simplify r of
    (Not s) -> s
    s -> Not s
simplify r = r

{-|
    INTERNAL. Check if a regex with an outer 'Union' operator is simplified.
-}
simplifiedUnion:: Regex -> Regex -> Bool
simplifiedUnion (Union _ _) _ = False
simplifiedUnion Empty _ = False
simplifiedUnion _ Empty = False
simplifiedUnion (Not Empty) _ = False
simplifiedUnion _ (Not Empty) = False
simplifiedUnion (CharSet _) (Union (CharSet _) _) = False
simplifiedUnion (CharSet _) (CharSet _) = False
simplifiedUnion r (Union s1 s2)
    | r < s1 = simplifiedUnion s1 s2
    | otherwise = False
simplifiedUnion r s
    | r < s = (simplified r) && (simplified s)
    | otherwise = False

{-|
    INTERNAL. Check if a regex with an outer 'Intersect' operator is simplified.
-}
simplifiedIntersect:: Regex -> Regex -> Bool
simplifiedIntersect (Intersect _ _) _ = False
simplifiedIntersect Empty _ = False
simplifiedIntersect _ Empty = False
simplifiedIntersect (Not Empty) _ = False
simplifiedIntersect _ (Not Empty) = False
simplifiedIntersect r (Intersect s1 s2)
    | r < s1 = simplifiedIntersect s1 s2
    | otherwise = False
simplifiedIntersect r s
    | r < s = (simplified r) && (simplified s)
    | otherwise = False

{-|
    INTERNAL. Check if a regex with an outer 'Dot' operator is simplified.
-}
simplifiedDot:: Regex -> Regex -> Bool
simplifiedDot (Dot _ _) _ = False
simplifiedDot Empty _ = False
simplifiedDot _ Empty = False
simplifiedDot Eps _ = False
simplifiedDot _ Eps = False
simplifiedDot r s = (simplified r) && (simplified s)

{-|
    Checks if a regular expression is simplified and in standard format. See
    'simplify' for details.
-}
simplified:: Regex -> Bool
simplified (Union r s) = simplifiedUnion r s
simplified (Intersect r s) = simplifiedIntersect r s
simplified (Dot r s) = simplifiedDot r s
simplified (Star (Star r)) = False
simplified (Not (Not r)) = False
simplified (Star Empty) = False
simplified (Star Eps) = False
simplified (Not r) = simplified r
simplified (Star r) = simplified r
simplified _ = True
                                    
{-|
    A constructor for a complete delta transition function using an underlying transition table and a 
    default 'Regex' to return in case a transition is absent in the table.
-}
findTransition:: (HashMap Regex (HashMap Char Regex)) -> Regex -> Regex -> Char -> Regex
findTransition tt def inst sy = case (HashMap.lookup inst tt) of
    Nothing -> def
    Just trans -> case (HashMap.lookup sy trans) of
                    Nothing -> def
                    Just outst -> outst


{-| 
    Constructs a DFA from a RE assuming some character alphabet.
-}
constructDfa:: [Char] -> Regex -> (Dfa Regex Char)
constructDfa alph r = 
    let sr = simplify r
        tt = ttConstruct (HashMap.singleton sr (HashMap.empty)) alph alph sr
        sts = HashMap.keys tt
        fs = Prelude.filter (nullable) sts
    in Dfa alph sts sr fs (findTransition tt Empty)

{-| 
    INTERNAL. Constructs the transition function of DFA states and actions (delta) as a transposition table.
-}
ttConstruct:: (HashMap Regex (HashMap Char Regex)) -> [Char] -> [Char] -> Regex -> (HashMap Regex (HashMap Char Regex))
ttConstruct tt alph [] r = tt
ttConstruct tt alph (x:xs) r =
    let sdr = simplify (deriv r x)
        tt1 = case (HashMap.lookup sdr tt) of
                Nothing -> ttConstruct (HashMap.insert sdr (HashMap.empty) (HashMap.adjust (HashMap.insert x sdr) r  tt)) alph alph sdr
                Just st -> HashMap.adjust (HashMap.insert x sdr) r  tt
    in ttConstruct tt1 alph xs r

{-|
    Checks if a DFA is minimal. Specifically checks that the number of states of a DFA
    and the number of states in the minimalized DFA is equal.
-} 
isMinimalDfa::(Ord st, Eq sy) => Dfa st sy -> Bool
isMinimalDfa  dfa = Dfa.sizeDfa (Min.minimizeDfa dfa) == Dfa.sizeDfa dfa

-- | Slow check to see if a RE is simplified. The function does this by computing the simplified regex and comparing them.
isMinimalRe:: Regex -> Bool
isMinimalRe r = r == (simplify r)

{-|
    Parses a RE from a string. Never fails, but gives 'Empty' if the string
    did not represent a valid RE.
    (See 'parse' for details)
-}
parseNF :: [Char] -> Regex
parseNF cs = case parse cs of
    Nothing -> Empty
    (Just r) -> r

{-|
    Parses a RE from a string. The operators are given in prefix form,
    such that brackets are not required. The format is:
    - [..] : A character range which matches all characters inside the brackets.
    - e : Epsilon. The empty string.
    - 0 : The empty RE.
    - ~ : Compliment.
    - * : Kleene Star.
    - + : Union (match either).
    - & : Intersect (match both).
    - . : Concatenation.

    The regex is constructing by traversing the string from left to right. Any operator will attempt to consume
    part of the string to create a valid RE. If anything is left in the string afterwards or if the end of string is reached
    before all operators have operhands, the string is considered invalid and 'Nothing' is returned.

    Examples:
    ".[a][b]"   Valid       [a].[b]
    "+~[a]"     Invalid     (~[a])+ ???
    "+[a]e0"    Invalid     [a]+e but "0" remains.
    "+.Oe[b]"   Valid       (0.e)+[b]

-}
parse:: [Char] -> (Maybe Regex)
parse cs = case parse' cs of
    (mr, []) -> mr
    _ -> Nothing

{-|
    INTERNAL. Helper function for 'parse'.
-}
parse':: [Char] -> ((Maybe Regex), [Char])
parse' [] = (Nothing, [])
parse' (c:cs) = case c of
    '0' -> ((Just Empty), cs)
    'e' -> ((Just Eps), cs)
    '[' -> parseCset HashSet.empty cs
    '~' -> case parse' cs of
            (Nothing, _) -> (Nothing, [])
            ((Just r), cs2) -> (Just (Not r), cs2)
    '*' -> case parse' cs of
            (Nothing, _) -> (Nothing, [])
            ((Just r), cs2) -> (Just (Star r), cs2)
    '+' -> case parse' cs of
            (Nothing, _) -> (Nothing, [])
            ((Just r), cs2) -> case parse' cs2 of
                (Nothing, _) -> (Nothing, [])
                ((Just s), cs3) -> (Just (Union r s), cs3)
    '&' -> case parse' cs of
            (Nothing, _) -> (Nothing, [])
            ((Just r), cs2) -> case parse' cs2 of
                (Nothing, _) -> (Nothing, [])
                ((Just s), cs3) -> (Just (Intersect r s), cs3)
    '.' -> case parse' cs of
            (Nothing, _) -> (Nothing, [])
            ((Just r), cs2) -> case parse' cs2 of
                (Nothing, _) -> (Nothing, [])
                ((Just s), cs3) -> (Just (Dot r s), cs3)
    _ -> (Nothing, [])

{-|
    INTERNAL. Helper function for 'parse' that parses a character set.
-}
parseCset :: (HashSet Char) -> [Char] -> ((Maybe Regex), [Char])
parseCset hs [] = (Nothing, [])
parseCset hs (']':cs) = ((Just $ CharSet hs), cs)
parseCset hs (c:cs) = parseCset (HashSet.insert c hs) cs

{-|
    Checks if a string represents a valid RE. See 'parse' for details.
-}
isValidStr :: [Char] -> Bool
isValidStr str = case parse str of
    Nothing -> False
    _       -> True

{-|
    INTERNAL. Helper function for 'growValidStrings'.
-}
splitGrow :: [[Char]] -> [[Char]] -> Int -> Int -> [Char] -> ([[Char]] -> [[Char]])
splitGrow csets clft d rophs pstr = case clft of 
    [] ->       (growValidStrings' csets (d - 1) (rophs - 1) ('0':pstr))
                . (growValidStrings' csets (d - 1) (rophs - 1) ('e':pstr))
                . (growValidStrings' csets (d - 1) rophs ('~':pstr))
                . (growValidStrings' csets (d - 1) rophs ('*':pstr))
                . (growValidStrings' csets (d - 1) (rophs + 1) ('+':pstr))
                . (growValidStrings' csets (d - 1) (rophs + 1) ('&':pstr))
                . (growValidStrings' csets (d - 1) (rophs + 1) ('.':pstr))
    (c:cs) ->   (growValidStrings' csets (d - 1) (rophs - 1) ((reverse ("[" ++ c ++ "]")) ++ pstr))
                . splitGrow csets cs d rophs pstr

{-|
    INTERNAL. Helper function for 'growValidStrings'.
-}
growValidStrings' :: [[Char]] -> Int -> Int -> [Char] -> ([[Char]] -> [[Char]])
growValidStrings' csets d rophs pstr = if
    | rophs > d -> ([] ++)
    | rophs == 0 -> ((reverse pstr):)
    | otherwise -> splitGrow csets csets d rophs pstr
        
{-|
    Grows all valid RE strings up to some size with a given set of usable
    characted sets.
-}
growValidStrings :: [[Char]] -> Int -> [[Char]]
growValidStrings csets d = (growValidStrings' csets d 1 "") []

{-|
     Grows all valid RE strings up to some size with the alphabet {a, b}
-}
growValidStringsAB :: Int -> [[Char]]
growValidStringsAB d = growValidStrings ["a", "b", "ab"] d


-- | INTERNAL. Helper function for 'serialToRegex'
consumeRegexSerial:: RegexSerial -> ConsumedInfo
consumeRegexSerial (SEmpty ser) = ConsumedInfo (Just Empty) ser
consumeRegexSerial (SEps ser) = ConsumedInfo (Just Eps) ser
consumeRegexSerial (SCharSet hs ser) = ConsumedInfo (Just (CharSet hs)) ser
consumeRegexSerial EndSerial = ConsumedInfo Nothing EndSerial
consumeRegexSerial (SNot ser) = 
    case (consumeRegexSerial ser) of
        ConsumedInfo Nothing _ -> ConsumedInfo Nothing EndSerial
        ConsumedInfo (Just nr) ser1 -> ConsumedInfo (Just (Not nr)) ser1
consumeRegexSerial (SStar ser) = 
    case (consumeRegexSerial ser) of
        ConsumedInfo Nothing _ -> ConsumedInfo Nothing EndSerial
        ConsumedInfo (Just nr) ser1 -> ConsumedInfo (Just (Star nr)) ser1
consumeRegexSerial (SUnion ser) = 
    case (consumeRegexSerial ser) of
        ConsumedInfo Nothing _ -> ConsumedInfo Nothing EndSerial
        ConsumedInfo (Just nr1) ser1 -> 
            case (consumeRegexSerial ser1) of 
                ConsumedInfo Nothing _ -> ConsumedInfo Nothing EndSerial
                ConsumedInfo (Just nr2) ser2 -> ConsumedInfo (Just (Union nr1 nr2)) ser2
consumeRegexSerial (SIntersect ser) = 
    case (consumeRegexSerial ser) of
        ConsumedInfo Nothing _ -> ConsumedInfo Nothing EndSerial
        ConsumedInfo (Just nr1) ser1 -> 
            case (consumeRegexSerial ser1) of 
                ConsumedInfo Nothing _ -> ConsumedInfo Nothing EndSerial
                ConsumedInfo (Just nr2) ser2 -> ConsumedInfo (Just (Intersect nr1 nr2)) ser2
consumeRegexSerial (SDot ser) = 
    case (consumeRegexSerial ser) of
        ConsumedInfo Nothing _ -> ConsumedInfo Nothing EndSerial
        ConsumedInfo (Just nr1) ser1 -> 
            case (consumeRegexSerial ser1) of 
                ConsumedInfo Nothing _ -> ConsumedInfo Nothing EndSerial
                ConsumedInfo (Just nr2) ser2 -> ConsumedInfo (Just (Dot nr1 nr2)) ser2

-- | Turns a serialized RE into an RE, uses Maybe to accomodate invalid serial REs. 
serialToRegex:: RegexSerial -> (Maybe Regex)
serialToRegex ser =
    case (consumeRegexSerial ser) of
        ConsumedInfo (Just r) EndSerial -> (Just r)
        ConsumedInfo _ _ -> Nothing

-- | INTERNAL: Helper function for 'growDisimilarListSerial'
growDissimilarListSerial':: Int -> [HashSet Char] -> [HashSet Char] -> RegexSerial -> ([Regex] -> [Regex])
growDissimilarListSerial' 0 _ _ ser = case serialToRegex ser of
    Just r -> if simplified r then ([r] ++) else ([] ++)
    Nothing -> ([] ++)
growDissimilarListSerial' d alph [] ser =
    let lst = case serialToRegex ser of
                Just r -> if simplified r then ([r] ++) else ([] ++)
                Nothing -> ([] ++)
        dm1 = d - 1
        out = lst
            . growDissimilarListSerial' dm1 alph alph (SEmpty ser)
            . growDissimilarListSerial' dm1 alph alph (SEps ser)
            . growDissimilarListSerial' dm1 alph alph (SNot ser)
            . growDissimilarListSerial' dm1 alph alph (SStar ser)
            . growDissimilarListSerial' dm1 alph alph (SUnion ser)
            . growDissimilarListSerial' dm1 alph alph (SIntersect ser)
            . growDissimilarListSerial' dm1 alph alph (SDot ser)
    in out
growDissimilarListSerial' d alph (c:cs) ser = (growDissimilarListSerial' (d - 1) alph alph (SCharSet c ser)) 
                                            . growDissimilarListSerial' d alph cs ser

-- | Grows a list of dissimlar REs using a serial RE construction method. Faster than 'growDisimilarList'.
growDissimilarListSerial :: Int -> [HashSet Char] -> [Regex]
growDissimilarListSerial d alph = (growDissimilarListSerial' d alph alph EndSerial) []

-- | Grows the same list as 'growDissimilarList' but faster, using the serial RE method.
growDissimilarListSerialAB :: Int -> [Regex]
growDissimilarListSerialAB d = growDissimilarListSerial d [HashSet.singleton 'a', HashSet.singleton 'b', HashSet.fromList "ab"]

{-|
    INTERNAL. Converts the DFA transitions to a graphViz format.
-}
dfaLnks2Dot:: [Regex] -> [Char] -> (Regex -> Char -> Regex) -> [Char] -> String
dfaLnks2Dot [] _ _ _   = []
dfaLnks2Dot (r:rs) alph hs [] = dfaLnks2Dot rs alph hs alph
dfaLnks2Dot (r:rs) alph hs (c:cs) = "\"" ++ (show r) ++ "\" -> \"" ++ (show (hs r c))  ++ "\"[label=\"" ++ [c] ++ "\"]\n" ++ (dfaLnks2Dot (r:rs) alph hs cs)

{-|
    INTERNAL. Converts the DFA states to a graphViz format.
-}
dfaFsts2Dot:: [Regex] -> String
dfaFsts2Dot []  = []
dfaFsts2Dot (r:rs) = "\"" ++ (show r) ++ "\"[shape=\"doublecircle\"]\n" ++ (dfaFsts2Dot rs)

{-|
    Computes a string dot representation for graphViz for a DFA.
    Nullable (final) states are drawn as double circles.
-}
dfa2Dot:: (Dfa Regex Char) -> String -> String
dfa2Dot (Dfa alph sts strt fsts tf) name = "digraph " 
                                            ++ name 
                                            ++ "{\n rankdir = LR ;\n{\n"
                                            ++ "\"startS\"[style=\"invis\"]\n"
                                            ++ (dfaFsts2Dot fsts)
                                            ++  "}\n"
                                            ++ "\"startS\" -> \"" ++ (show strt) ++ "\"[color=\"green\"]"
                                            ++ (dfaLnks2Dot sts alph tf alph)  
                                            ++ "\n}"

{-|
    Creates a .dot file for graphViz representing the DFA. 
-}
dfa2Dot2File:: (Dfa Regex Char) -> String -> IO()
dfa2Dot2File dfa name = do
    writeFile (name ++ ".dot") (dfa2Dot dfa name)