import ReDfa
import Test.Hspec
import Test.QuickCheck
import ReDfa (Regex)
import Test.Hspec.Core.QuickCheck (modifyMaxSuccess)
import Data.HashSet as HashSet
import Test.QuickCheck.Gen
import Control.Applicative
import Test.QuickCheck.Arbitrary

data Rgx1StrMny = Rgx1StrMny Regex [[Char]]

instance Arbitrary Rgx1StrMny where
    arbitrary = liftA2 Rgx1StrMny genRegex (vectorOf 200 genABWord)

instance Show Rgx1StrMny where
    show (Rgx1StrMny r _) = show r

genABWord:: Gen [Char]
genABWord = choose (1, 20) >>= (flip vectorOf) (elements "ab")

sameMatchReDfa:: Regex -> (Dfa Regex Char) -> [Char] -> Bool
sameMatchReDfa r dfa str = match r str == dfaaccept dfa str

prop_RE_equiv_DFA:: Rgx1StrMny -> Bool
prop_RE_equiv_DFA (Rgx1StrMny r lst) = 
    let dfa = constructDfa "ab" r
    in foldl (\b str -> b && (sameMatchReDfa r dfa str)) True lst

prop_indemp_simplify :: Regex -> Bool
prop_indemp_simplify r = (simplify (simplify r)) == simplify r


prop_simplified_sanity :: Regex -> Bool
prop_simplified_sanity r = (simplified (simplify r)) == True

prop_simplify_deriv_transitivity :: Regex -> Bool
prop_simplify_deriv_transitivity r = simplify (deriv r 'a') == simplify (deriv (simplify r) 'a')

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
            simplified (simplify (Not (CharSet (HashSet.fromList "a" )))) `shouldBe` True
        it "Base case: simplify (Dot 'a' 'b')" $
            simplified (simplify (Dot (CharSet (HashSet.fromList "a" )) (CharSet (HashSet.fromList "b" )))) `shouldBe` True
        it "Base case: simplify (Union 'a' 'b')" $
            simplified (simplify (Union (CharSet (HashSet.fromList "a" )) (CharSet (HashSet.fromList "b" )))) `shouldBe` True
        it "Base case: simplify (Intersect 'a' 'b')" $
            simplified (simplify (Intersect (CharSet (HashSet.fromList "a" )) (CharSet (HashSet.fromList "b" )))) `shouldBe` True
            


main :: IO ()
main = hspec $ do
    testNullable
    testSimplified
    testSimplify

    describe "ReDfa.simplify" $ do
        modifyMaxSuccess (const 1000) $ it "is indempotent" $ property $
            prop_indemp_simplify
    describe "ReDfa.simplified" $ do
        modifyMaxSuccess (const 1000) $ it "is indempotent" $ property $
            prop_simplified_sanity
    describe "ReDfa.constructDfa" $ do
        modifyMaxSuccess (const 1000) $ it "creates equivalent DFAs" $ property $
            prop_RE_equiv_DFA
    describe "ReDfa.deriv" $ do
        modifyMaxSuccess (const 1000) $ it "does not affect similarity" $ property $
            prop_RE_equiv_DFA
