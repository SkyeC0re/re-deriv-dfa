import ReDfa
import Test.Hspec
import Test.QuickCheck
import ReDfa (Regex)
import Test.Hspec.Core.QuickCheck (modifyMaxSuccess)
import Data.HashSet as HashSet
import Data.List
import Test.QuickCheck.Gen
import Control.Applicative
import Test.QuickCheck.Arbitrary
import Data.Sort

data Rgx1StrMny = Rgx1StrMny Regex [[Char]]

data Rgx1c1 = Rgx1c1 Regex Char

instance Arbitrary Rgx1StrMny where
    arbitrary = liftA2 Rgx1StrMny genRegex (vectorOf 400 genABWord)

instance Arbitrary Rgx1c1 where
    arbitrary = liftA2 Rgx1c1 genRegex (elements "ab")

instance Show Rgx1StrMny where
    show (Rgx1StrMny r _) = show r

instance Show Rgx1c1 where
    show (Rgx1c1 r c) = "d_{" ++ [c] ++ "} " ++ (show r)

-- | Generates a word of between length 1 and 20 from the alphabet {a,b}.
genABWord:: Gen [Char]
genABWord = choose (1, 20) >>= (flip vectorOf) (elements "ab")

-- | Checks if a RE and a DFA either both accepts or both rejects a word.
sameMatchReDfa:: Regex -> (Dfa Regex Char) -> [Char] -> Bool
sameMatchReDfa r dfa str = match r str == dfaaccept dfa str

-- | All the dissimilar REs up to size 1
disList1:: [Regex]
disList1 = [Empty, Eps, CharSet (HashSet.singleton 'a'), CharSet (HashSet.singleton 'b'), CharSet (HashSet.fromList "ab")]

-- | All the dissimilar REs up to size 2
disList2:: [Regex]
disList2 = [Empty, Eps, CharSet (HashSet.singleton 'a'), CharSet (HashSet.singleton 'b'), CharSet (HashSet.fromList "ab"),
            Not Empty, Not Eps, Not (CharSet (HashSet.singleton 'a')), Not (CharSet (HashSet.singleton 'b')), Not (CharSet (HashSet.fromList  "ab")),
            Star (CharSet (HashSet.singleton 'a')), Star (CharSet (HashSet.singleton 'b')), Star (CharSet (HashSet.fromList  "ab"))]

disList3:: [Regex]
disList3 = [Empty,
            Eps, 
            CharSet (HashSet.singleton 'a'), 
            CharSet (HashSet.singleton 'b'), 
            CharSet (HashSet.fromList "ab"),
            Not Empty, 
            Not Eps, 
            Not (CharSet (HashSet.singleton 'a')), 
            Not (CharSet (HashSet.singleton 'b')), 
            Not (CharSet (HashSet.fromList  "ab")),
            Star (CharSet (HashSet.singleton 'a')), 
            Star (CharSet (HashSet.singleton 'b')), 
            Star (CharSet (HashSet.fromList  "ab")),
            Star (Not Eps), 
            Star (Not Empty), 
            Star (Not (CharSet (HashSet.singleton 'a'))), 
            Star (Not (CharSet (HashSet.singleton 'b'))), 
            Star (Not (CharSet (HashSet.fromList  "ab"))),
            Not (Star (CharSet (HashSet.singleton 'a'))),
            Not (Star (CharSet (HashSet.singleton 'b'))),
            Not (Star (CharSet (HashSet.fromList "ab"))),
            Union (CharSet (HashSet.singleton 'a')) Eps, 
            Union (CharSet (HashSet.singleton 'b')) Eps, 
            Union (CharSet (HashSet.fromList "ab")) Eps,
            Intersect (CharSet (HashSet.singleton 'a')) Eps, 
            Intersect (CharSet (HashSet.singleton 'b')) Eps, 
            Intersect (CharSet (HashSet.fromList "ab")) Eps,
            Intersect (CharSet (HashSet.singleton 'a')) (CharSet (HashSet.singleton 'b')),
            Intersect (CharSet (HashSet.fromList "ab")) (CharSet (HashSet.singleton 'b')),
            Intersect (CharSet (HashSet.singleton 'a')) (CharSet (HashSet.fromList "ab")),
            Dot (CharSet (HashSet.singleton 'a')) (CharSet (HashSet.singleton 'a')),
            Dot (CharSet (HashSet.singleton 'a')) (CharSet (HashSet.singleton 'b')), 
            Dot (CharSet (HashSet.singleton 'a')) (CharSet (HashSet.fromList "ab")),
            Dot (CharSet (HashSet.singleton 'b')) (CharSet (HashSet.singleton 'a')),
            Dot (CharSet (HashSet.singleton 'b')) (CharSet (HashSet.singleton 'b')), 
            Dot (CharSet (HashSet.singleton 'b')) (CharSet (HashSet.fromList "ab")),
            Dot (CharSet (HashSet.fromList "ab")) (CharSet (HashSet.singleton 'a')),
            Dot (CharSet (HashSet.fromList "ab")) (CharSet (HashSet.singleton 'b')), 
            Dot (CharSet (HashSet.fromList "ab")) (CharSet (HashSet.fromList "ab"))]

prop_RE_equiv_DFA:: Rgx1StrMny -> Bool
prop_RE_equiv_DFA (Rgx1StrMny r lst) = 
    let dfa = constructDfa "ab" r
    in foldl (\b str -> b && (sameMatchReDfa r dfa str)) True lst

prop_RE_equiv_simplified_RE:: Rgx1StrMny -> Bool
prop_RE_equiv_simplified_RE (Rgx1StrMny r lst) =
    let sr = simplify r
    in foldl (\b str -> b && (match r str == match sr str)) True lst

prop_simplify_deriv_not_affect_l:: Rgx1StrMny -> Bool
prop_simplify_deriv_not_affect_l (Rgx1StrMny r lst) =
    let sr = simplify r
        dr = simplify (deriv r 'a')
        dsr = simplify (deriv sr 'a')
    in foldl (\b str -> b && (match dr str == match dsr str)) True lst

prop_indemp_simplify :: Regex -> Bool
prop_indemp_simplify r = (simplify (simplify r)) == simplify r


prop_simplified_sanity :: Regex -> Bool
prop_simplified_sanity r = (simplified (simplify r)) == True

prop_isMinimalRe_eq_simplified :: Regex -> Bool
prop_isMinimalRe_eq_simplified r = isMinimalRe r == simplified r

prop_valid_parse_match :: Regex -> Bool
prop_valid_parse_match r = case parse (show r) of
    Just r1 -> if r == r1 then True else False
    _ -> False

prop_grows_unique_list :: Int -> Bool
prop_grows_unique_list d =  
    let lst = growValidREAB d
    in Data.List.sort lst == Data.Sort.uniqueSort lst

prop_deriv_not_affect_similarity:: Rgx1c1 -> Bool
prop_deriv_not_affect_similarity (Rgx1c1 r c) = simplify (deriv r c) == simplify (deriv (simplify r) c)

testNullable :: Spec
testNullable = do
    describe "Testing nullable base cases" $ do
        it "Base case: nullable Empty" $
            nullable Empty `shouldBe` False
        it "Base case: nullable Eps" $
            nullable Eps `shouldBe` True
        it "Base case: nullable 'a'" $
            nullable (CharSet (HashSet.fromList "a" )) `shouldBe` False
        it "Base case: nullable Star 'a'" $
            nullable (Star (CharSet (HashSet.fromList "a" ))) `shouldBe` True
        it "Base case: nullable (Not 'a')" $
            nullable (Not (CharSet (HashSet.fromList "a" ))) `shouldBe` not (nullable (CharSet (HashSet.fromList "a" )))
        it "Base case: nullable (Dot 'a' 'b')" $
            nullable (Dot (CharSet (HashSet.fromList "a" )) (CharSet (HashSet.fromList "b" ))) `shouldBe` (nullable (CharSet (HashSet.fromList "a" ))) && (nullable (CharSet (HashSet.fromList "b" )))
        it "Base case: nullable (Union 'a' 'b')" $
            nullable (Union (CharSet (HashSet.fromList "a" )) (CharSet (HashSet.fromList "b" ))) `shouldBe` (nullable (CharSet (HashSet.fromList "a" ))) || (nullable (CharSet (HashSet.fromList "b" )))
        it "Base case: nullable (Intersect 'a' 'b')" $
            nullable (Intersect (CharSet (HashSet.fromList "a" )) (CharSet (HashSet.fromList "b" ))) `shouldBe` (nullable (CharSet (HashSet.fromList "a" ))) && (nullable (CharSet (HashSet.fromList "b" )))


testSimplified :: Spec
testSimplified = do
    describe "Testing simplified base cases" $ do
        it "Base case: simplified Star (Star 'a')" $
            simplified (Star (Star (CharSet (HashSet.fromList "a" )))) `shouldBe` False
        it "Base case: simplified Not (Not 'a')" $
            simplified (Not (Not (CharSet (HashSet.fromList "a" )))) `shouldBe` False
        it "Base case: simplified Star Empty" $
            simplified (Star Empty) `shouldBe` False
        it "Base case: simplified Star Eps" $ 
            simplified (Star Eps) `shouldBe` False

testSimplify :: Spec
testSimplify = do
    describe "Testing simplify base cases" $ do
        it "Base case: simplify Empty" $
            simplified (simplify Empty) `shouldBe` True
        it "Base case: simplify Eps" $
            simplified (simplify Eps) `shouldBe` True
        it "Base case: simplify 'a'" $
            simplified (simplify (CharSet (HashSet.fromList "a" ))) `shouldBe` True
        it "Base case: simplify Star 'a" $
            simplified (simplify (Star (CharSet (HashSet.fromList "a" )))) `shouldBe` True
        it "Base case: simplify (Not 'a')" $
            simplified (simplify (Dot (CharSet (HashSet.fromList "a" )) (CharSet (HashSet.fromList "b" )))) `shouldBe` True
        it "Base case: simplify (Union 'a' 'b')" $
            simplified (simplify (Union (CharSet (HashSet.fromList "a" )) (CharSet (HashSet.fromList "b" )))) `shouldBe` True
        it "Base case: simplify (Intersect 'a' 'b')" $
            simplified (simplify (Intersect (CharSet (HashSet.fromList "a" )) (CharSet (HashSet.fromList "b" )))) `shouldBe` True


testParse :: Spec
testParse = do
    describe "ReDfa.parse" $ do
        it "parses the dissimilar list for REs of size 1 correctly" $
            foldl (&&) True (Data.List.map prop_valid_parse_match disList1) `shouldBe` True
        it "parses the dissimilar list for REs of size 2 correctly" $
            foldl (&&) True (Data.List.map prop_valid_parse_match disList2) `shouldBe` True
        it "parses the dissimilar list for REs of size 3 correctly" $
            foldl (&&) True (Data.List.map prop_valid_parse_match disList3) `shouldBe` True
        modifyMaxSuccess (const 1000) $ it "creates an equal valid RE when given a valid string generated by 'show' of Dfa.Regex" $ property $
            prop_valid_parse_match


testGrowRegex :: Spec
testGrowRegex = do
    describe "ReDfa.growValidStringsAB" $ do
        it "grows a valid, unique list of REs up to size 1" $
            prop_grows_unique_list 1 `shouldBe` True
        it "grows a valid, unique list of REs up to size 2" $
            prop_grows_unique_list 2 `shouldBe` True
        it "grows a valid, unique list of REs up to size 3" $
            prop_grows_unique_list 3 `shouldBe` True
        it "grows a valid, unique list of REs up to size 4" $
            prop_grows_unique_list 4 `shouldBe` True
        it "grows a valid, unique list of REs up to size 5" $
            prop_grows_unique_list 5 `shouldBe` True
        it "grows a valid, unique list of REs up to size 6" $
            prop_grows_unique_list 6 `shouldBe` True

main :: IO ()
main = hspec $ do
  testNullable
  testSimplified
  testSimplify
  testGrowRegex
  testParse

  describe "ReDfa.simplify" $ do
    it "simplifies the list of all REs of size 1 to the expected list" $
      Data.List.sort (Data.List.filter simplified $ growValidREAB 1) == Data.List.sort disList1  `shouldBe` True
    it "simplifies the list of all REs of size 2 to the expected list" $
      Data.List.sort (Data.List.filter simplified $ growValidREAB 2) == Data.List.sort disList2  `shouldBe` True
    it "simplifies the list of all REs of size 3 to the expected list" $
      Data.List.sort (Data.List.filter simplified $ growValidREAB 3) == Data.List.sort disList3  `shouldBe` True
    modifyMaxSuccess (const 10000) $ it "is indempotent" $ property $
      prop_indemp_simplify
    modifyMaxSuccess (const 1000) $ it "does not affect the language" $ property $
      prop_RE_equiv_simplified_RE
    modifyMaxSuccess (const 1000) $ it "does not affect the language when applied before a derivative" $ property $
      prop_simplify_deriv_not_affect_l
  describe "ReDfa.simplified" $ do
    modifyMaxSuccess (const 10000) $ it "returns true only when simplify does not change the RE" $ property $
      prop_isMinimalRe_eq_simplified
  describe "ReDfa.constructDfa" $ do
    modifyMaxSuccess (const 1000) $ it "creates equivalent DFAs" $ property $
      prop_RE_equiv_DFA
  


