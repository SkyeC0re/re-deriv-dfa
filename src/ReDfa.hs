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

-- | A Recursive Data Structure to represent the regular expression 
data Regex  = CharSet (HashSet Char)
            | Empty
            | Eps
            | Not Regex
            | Star Regex
            | Intersect Regex Regex
            | Union Regex Regex
            | Dot Regex Regex
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

data Attributes = Attributes Integer Integer Int
                | Default
                deriving (Show)

-- | Hashability is reguired to store unique states in a set
instance Hashable Regex

-- | Pretty print regex
instance Show Regex where
    show (Union r s) = "+" ++ (show r) ++ (show s)
    show (Intersect r s) = "&" ++ (show r) ++ (show s)
    show (Dot r s) = "." ++ (show r) ++ (show s)
    show (Not r) = "~" ++ (show r)
    show (Star r) = "*" ++ (show r)
    show (CharSet hs) = "[" ++ (HashSet.toList hs) ++ "]"
    show Empty = "0"
    show Eps = "e"

instance Arbitrary Regex where
    arbitrary = genRegex


genRegex :: Gen Regex
genRegex = choose (1,5) >>= genSzdRegex

-- | INTERNAL. Generates a random RE of the specified size
genSzdRegex:: Int -> (Gen Regex)
genSzdRegex 0 = elements [Empty]
genSzdRegex 1 = generateRandomElem
genSzdRegex 2 = generateRandomUnOp <*> generateRandomElem
genSzdRegex d = 
    let dm1 = d - 1
    in frequency [(1, genUnOpOuter dm1), (5, choose (1, dm1 - 1) >>= (genBinOpOuter dm1))]

-- | INTERNAL. Helper function for 'genSzdRegex'
genBinOpOuter:: Int -> Int -> (Gen Regex)
genBinOpOuter d ld = (generateRandomBinOp <*> (genSzdRegex ld)) <*> (genSzdRegex (d - ld))

-- | INTERNAL. Helper function for 'genSzdRegex'
genUnOpOuter:: Int -> (Gen Regex)
genUnOpOuter d = generateRandomUnOp <*> (genSzdRegex d)

-- | INTERNAL. Helper function for 'genSzdRegex'
generateRandomElem:: Gen Regex
generateRandomElem = elements [Empty, Eps, CharSet (HashSet.singleton 'a'), CharSet (HashSet.singleton 'b'), CharSet (HashSet.fromList "ab")]

-- | INTERNAL. Helper function for 'genSzdRegex'
generateRandomUnOp:: (Gen (Regex -> Regex))
generateRandomUnOp = elements [Not, Star]

-- | INTERNAL. Helper function for 'genSzdRegex'
generateRandomBinOp:: (Gen (Regex -> Regex -> Regex))
generateRandomBinOp = elements [Union, Intersect, Dot]

-- | Returns the size of a Regular expression. The empty expression (Empty), the empty string (Eps) and
-- any character set {x1, x2, ..., xn} is considered length 1. All operators contribute 1 to the length.
sizeRe:: Regex -> Int
sizeRe Empty = 1
sizeRe Eps = 1
sizeRe (CharSet _) = 1
sizeRe (Not r) = 1 + (sizeRe r)
sizeRe (Star r) = 1 + (sizeRe r)
sizeRe (Intersect r1 r2) = 1 + (sizeRe r1) + (sizeRe r2)
sizeRe (Union r1 r2) = 1 + (sizeRe r1) + (sizeRe r2)
sizeRe (Dot r1 r2) =  1 + (sizeRe r1) + (sizeRe r2)

-- | Returns 'Eps' if the expression is nullable, 'Empty' otherwise.
regexNullable:: Regex -> Regex
regexNullable r
    | (nullable r) == True = Eps
    | otherwise = Empty

-- | Returns 'True' if the expression nullable, 'False' otherwise.
nullable:: Regex -> Bool
nullable Empty = False
nullable Eps = True
nullable (CharSet _) = False
nullable (Star _) = True
nullable (Not r) = not (nullable r)
nullable (Dot r1 r2) = (nullable r1) && (nullable r2)
nullable (Union r1 r2) = (nullable r1) || (nullable r2)
nullable (Intersect r1 r2) = (nullable r1) && (nullable r2)


-- | Computes the derivative of an expression with respect to a symbol.
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

-- | Simplifies a regex with an outer 'Union' operator.
simplifyUnion:: Regex -> Regex
simplifyUnion union = (unpackUnionList . mergeUnionCharSets . Sort.uniqueSort . simplifiedUnionList) union

-- | Merges the first CharSets in a sorted list. They are guaranteed to be first from the derived order of the constructor.
mergeUnionCharSets:: [Regex] -> [Regex]
mergeUnionCharSets ((CharSet sa):(CharSet sb):lst) = mergeUnionCharSets ((CharSet (HashSet.union sa sb)):lst)
mergeUnionCharSets lst = lst

-- | Creates a list from the operands of nested 'Union' operators.
simplifiedUnionList:: Regex -> [Regex]
simplifiedUnionList (Union r1 r2) = mergeUnionList (simplifiedUnionList r1) (simplifiedUnionList r2)
simplifiedUnionList r  =
    let sr = simplify r
    in if sr == r then [r] else simplifiedUnionList sr

-- | Simplies and merges two lists of nested 'Union' operands.
mergeUnionList:: [Regex] -> [Regex] -> [Regex]
mergeUnionList [Not Empty] _ = [Not Empty]
mergeUnionList _ [Not Empty] = [Not Empty]
mergeUnionList [Empty] lst = lst
mergeUnionList lst [Empty] = lst
mergeUnionList l1 l2 = l1 ++ l2

-- | Recompiles a simplified 'Union' list back to a regular expression with a standard format.
unpackUnionList:: [Regex] -> Regex
unpackUnionList [r] = r
unpackUnionList (r:rs) = Union r (unpackUnionList rs)

-- | Simplifies a regex with an outer 'Intersect' operator.
simplifyIntersect:: Regex -> Regex
simplifyIntersect intersect = unpackIntersectList (Sort.uniqueSort (simplifiedIntersectList intersect))

-- | Creates a list from the operands of nested 'Intersect' operators.
simplifiedIntersectList:: Regex -> [Regex]
simplifiedIntersectList (Intersect r1 r2) = mergeIntersectList (simplifiedIntersectList r1) (simplifiedIntersectList r2)
simplifiedIntersectList r = 
    let sr = simplify r
    in if sr == r then [r] else simplifiedIntersectList sr

-- | Simplies and merges two lists of nested 'Intersect' operands.
mergeIntersectList:: [Regex] -> [Regex] -> [Regex]
mergeIntersectList [Empty] _ = [Empty]
mergeIntersectList _ [Empty] = [Empty]
mergeIntersectList [Not Empty] lst = lst
mergeIntersectList lst [Not Empty] = lst
mergeIntersectList l1 l2 = l1 ++ l2

-- | Recompiles a simplified 'Intersect' list back to a regular expression with a standard format.
unpackIntersectList:: [Regex] -> Regex
unpackIntersectList [r] = r
unpackIntersectList (r:rs) = Intersect r (unpackIntersectList rs)

-- | Simplifies a regex with an outer 'Dot' operator.
simplifyDot:: Regex -> Regex
simplifyDot dot = unpackDotList $ simplifiedDotList dot

-- | Creates a list from the operands of nested 'Dot' operators.
simplifiedDotList:: Regex -> [Regex]
simplifiedDotList (Dot r1 r2) = mergeDotList (simplifiedDotList r1) (simplifiedDotList r2)
simplifiedDotList r =
    let sr = simplify r
    in if sr == r then [r] else simplifiedDotList sr

-- | Simplies and merges two lists of nested 'Dot' operands.
mergeDotList:: [Regex] -> [Regex] -> [Regex]
mergeDotList [Empty] _ = [Empty]
mergeDotList _ [Empty] = [Empty]
mergeDotList [Eps] lst = lst 
mergeDotList lst [Eps] = lst
mergeDotList l1 l2 = l1 ++ l2

-- | Recompiles a simplified 'Dot' list back to a regular expression with a standard format.
unpackDotList:: [Regex] -> Regex
unpackDotList [r] = r
unpackDotList (r:rs) = Dot r (unpackDotList rs)

-- | Simplifies a regular expression.
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

-- | Check if a regex with an outer 'Union' operator is simplified
simplifiedUnion:: Regex -> Bool
simplifiedUnion (Union (Union _ _) _) = False
simplifiedUnion (Union Empty _) = False
simplifiedUnion (Union _ Empty) = False
simplifiedUnion (Union (Not Empty) _) = False
simplifiedUnion (Union _ (Not Empty)) = False
simplifiedUnion (Union (CharSet _) (Union (CharSet _) _)) = False
simplifiedUnion (Union (CharSet _) (CharSet _)) = False
simplifiedUnion (Union r (Union s1 s2))
    | r < s1 = simplifiedUnion (Union s1 s2)
    | otherwise = False
simplifiedUnion (Union r s)
    | r < s = (simplified r) && (simplified s)
    | otherwise = False
simplifiedUnion r = simplified r

-- | Check if a regex with an outer 'Intersect' operator is simplified
simplifiedIntersect:: Regex -> Bool
simplifiedIntersect (Intersect (Intersect _ _) _) = False
simplifiedIntersect (Intersect Empty _) = False
simplifiedIntersect (Intersect _ Empty) = False
simplifiedIntersect (Intersect (Not Empty) _) = False
simplifiedIntersect (Intersect _ (Not Empty)) = False
simplifiedIntersect (Intersect r (Intersect s1 s2))
    | r < s1 = simplifiedIntersect (Intersect s1 s2)
    | otherwise = False
simplifiedIntersect (Intersect r s)
    | r < s = (simplified r) && (simplified s)
    | otherwise = False
simplifiedIntersect r = simplified r

-- | Check if a regex with an outer 'Dot' operator is simplified
simplifiedDot:: Regex -> Bool
simplifiedDot (Dot (Dot _ _) _) = False
simplifiedDot (Dot Empty _) = False
simplifiedDot (Dot _ Empty) = False
simplifiedDot (Dot Eps _) = False
simplifiedDot (Dot _ Eps) = False
simplifiedDot (Dot r s) = (simplified r) && (simplified s)
simplifiedDot r = simplified r

-- | Checks if a regular expression is simplified and in standard format
simplified:: Regex -> Bool
simplified (Union r s) = simplifiedUnion (Union r s)
simplified (Intersect r s) = simplifiedIntersect (Intersect r s)
simplified (Dot r s) = simplifiedDot (Dot r s)
simplified (Star (Star r)) = False
simplified (Not (Not r)) = False
simplified (Star Empty) = False
simplified (Star Eps) = False
simplified (Not r) = simplified r
simplified (Star r) = simplified r
simplified _ = True
                                    

-- A constructor for delta transition function using an underlying transition table and a 
-- default 'Regex' return in case a transition is absent in the table.
findTransition:: (HashMap Regex (HashMap Char Regex)) -> Regex -> Regex -> Char -> Regex
findTransition tt def inst sy = case (HashMap.lookup inst tt) of
    Nothing -> def
    Just trans -> case (HashMap.lookup sy trans) of
                    Nothing -> def
                    Just outst -> outst


-- | Constructs a DFA from a RE
constructDfa:: [Char] -> Regex -> (Dfa Regex Char)
constructDfa alph r = 
    let sr = simplify r
        tt = ttConstruct (HashMap.singleton sr (HashMap.empty)) alph alph sr
        sts = HashMap.keys tt
        fs = Prelude.filter (nullable) sts
    in Dfa alph sts sr fs (findTransition tt Empty)

-- | Constructs delta as a transposition table.
ttConstruct:: (HashMap Regex (HashMap Char Regex)) -> [Char] -> [Char] -> Regex -> (HashMap Regex (HashMap Char Regex))
ttConstruct tt alph [] r = tt
ttConstruct tt alph (x:xs) r =
    let sdr = simplify (deriv r x)
        tt1 = case (HashMap.lookup sdr tt) of
                Nothing -> ttConstruct (HashMap.insert sdr (HashMap.empty) (HashMap.adjust (HashMap.insert x sdr) r  tt)) alph alph sdr
                Just st -> HashMap.adjust (HashMap.insert x sdr) r  tt
    in ttConstruct tt1 alph xs r

-- | Returns true if a Dfa is minimal
isMinimalDfa::(Ord st, Eq sy) => Dfa st sy -> Bool
isMinimalDfa  dfa = Dfa.sizeDfa (Min.minimizeDfa dfa) == Dfa.sizeDfa dfa

-- | Slow check to see if a RE is simplified. The function does this by computing the simplified regex and comparing them.
isMinimalRe:: Regex -> Bool
isMinimalRe r = r == (simplify r)

-- | Counts the amount of minimal DFAs constructed from a RE list, given some alphabet.
countMinimalDfas:: [Char] -> [Regex] -> Int
countMinimalDfas alph [] = 0
countMinimalDfas alph (r:rs)
    | isMinimalDfa (constructDfa alph r) = 1 + (countMinimalDfas alph rs)
    | otherwise = countMinimalDfas alph rs

-- | Prints all elements in list in their own line.
printElements:: (Show a) => [a] -> IO()
printElements = mapM_ print

parseNF :: [Char] -> Regex
parseNF cs = case parse cs of
    Nothing -> Empty
    (Just r) -> r

parse:: [Char] -> (Maybe Regex)
parse cs = case parse' cs of
    (mr, []) -> mr
    _ -> Nothing

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

parseCset :: (HashSet Char) -> [Char] -> ((Maybe Regex), [Char])
parseCset hs [] = (Nothing, [])
parseCset hs (']':cs) = ((Just $ CharSet hs), cs)
parseCset hs (c:cs) = parseCset (HashSet.insert c hs) cs

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

growValidStrings' :: [[Char]] -> Int -> Int -> [Char] -> ([[Char]] -> [[Char]])
growValidStrings' csets d rophs pstr = if
    | rophs > d -> ([] ++)
    | rophs == 0 -> ((reverse pstr):)
    | otherwise -> splitGrow csets csets d rophs pstr
        

growValidStrings :: [[Char]] -> Int -> [[Char]]
growValidStrings csets d = (growValidStrings' csets d 1 "") []

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

-- | Ignore : Not Used 
countAttribute':: Int -> [HashSet Char] -> a -> (Regex -> a) -> (a -> a -> a) -> RegexSerial -> [HashSet Char] -> a
countAttribute' 0 _ idElem f g ser _ = case serialToRegex ser of
                Just r -> f r
                Nothing -> idElem
countAttribute' d alph idElem f g ser [] = 
    let a1 = case serialToRegex ser of
                Just r -> f r
                Nothing -> idElem
        dm1 = d - 1
        out =  ((g (countAttribute' dm1 alph idElem f g (SEmpty ser) alph))
            .  (g (countAttribute' dm1 alph idElem f g (SEps ser) alph))
            .  (g (countAttribute' dm1 alph idElem f g (SNot ser) alph))
            .  (g (countAttribute' dm1 alph idElem f g (SStar ser) alph))
            .  (g (countAttribute' dm1 alph idElem f g (SUnion ser) alph))
            .  (g (countAttribute' dm1 alph idElem f g (SIntersect ser) alph))
            .  (g (countAttribute' dm1 alph idElem f g (SDot ser) alph))) a1
    in out
countAttribute' d alph idElem f g ser (c:cs) = g (countAttribute' (d-1) alph idElem f g (SCharSet c ser) alph) (countAttribute' d alph idElem f g ser cs)

-- | Ignore: Not Used
countAttribute:: Int -> [HashSet Char] -> a -> (Regex -> a) -> (a -> a -> a) -> a
countAttribute d alph idElem f g = countAttribute' d alph idElem f g EndSerial alph

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

-- | Ignore: Unused
getRegexAttributes:: Regex -> Attributes
getRegexAttributes r
    | simplified r = if
        | isMinimalDfa dfa -> Attributes 1 1 (sizeDfa dfa)
        | otherwise -> Attributes 1 0 0  
    | otherwise = Attributes 0 0 0
    where dfa = constructDfa "ab" r

-- | Ignore: Unused
mergeAttr:: Attributes -> Attributes -> Attributes
mergeAttr Default att = att
mergeAttr att Default = att
mergeAttr (Attributes dis1 min1 maxC1) (Attributes dis2 min2 maxC2) = Attributes (dis1 + dis2) (min1 + min2) (max maxC1 maxC2)

-- | INTERNAL: Converts the Dfa transitions to a dot format
dfaLnks2Dot:: [Regex] -> [Char] -> (Regex -> Char -> Regex) -> [Char] -> String
dfaLnks2Dot [] _ _ _   = []
dfaLnks2Dot (r:rs) alph hs [] = dfaLnks2Dot rs alph hs alph
dfaLnks2Dot (r:rs) alph hs (c:cs) = "\"" ++ (show r) ++ "\" -> \"" ++ (show (hs r c))  ++ "\"[label=\"" ++ [c] ++ "\"]\n" ++ (dfaLnks2Dot (r:rs) alph hs cs)

-- | INTERNAL: Converts the Dfa transitions to a dot format
dfaFsts2Dot:: [Regex] -> String
dfaFsts2Dot []  = []
dfaFsts2Dot (r:rs) = "\"" ++ (show r) ++ "\"[shape=\"doublecircle\"]\n" ++ (dfaFsts2Dot rs)

-- | Computes a string dot representation for graphViz for a DFA.
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

-- | Creates a .dot file representing the DFA
dfa2Dot2File:: (Dfa Regex Char) -> String -> IO()
dfa2Dot2File dfa name = do
    writeFile (name ++ ".dot") (dfa2Dot dfa name)
