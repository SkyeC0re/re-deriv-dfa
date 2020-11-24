import ReDfa
import Test.Hspec
import Test.QuickCheck
import ReDfa (Regex)
import Test.Hspec.Core.QuickCheck (modifyMaxSuccess)

prop_indemp_simplify :: Regex -> Bool
prop_indemp_simplify r = (simplify (simplify r)) == simplify r

main :: IO ()
main = hspec $ do
  describe "ReDfa.simplify" $ do
    modifyMaxSuccess (const 1000) $ it "is indempotent" $ property $
      prop_indemp_simplify

    {-it "returns the first element of an *arbitrary* list" $
      property $ \x xs -> head (x:xs) == (x :: Int)

    it "throws an exception if used with an empty list" $ do
      evaluate (head []) `shouldThrow` anyException-}
