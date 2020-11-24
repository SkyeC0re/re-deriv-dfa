{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE MultiWayIf #-}

module Main where
import ReDfa
import Test.QuickCheck (quickCheck)
import ReDfa (Regex)
import Data.Foldable (traverse_)

printComputation:: Int -> IO()
printComputation l = do
    let valStrs = growValidStringsAB l
    let disRegex = ((filter simplified) . (map parseNF)) valStrs
    let dsRmDfa = ((filter isMinimalDfa) . (map (constructDfa "ab"))) disRegex
    let mx = foldl max 0 (map sizeDfa dsRmDfa) 
    putStrLn ("Computation for size: " ++ (show l))
    putStrLn (" Dissimilar REs (dREs): " ++ (show (length disRegex)))
    putStrLn (" dREs with Minimal DFAs (dmDFAs): " ++ (show (length dsRmDfa)))
    putStrLn (" dmDFAs maximum size: " ++ (show mx) ++ "\n\n")

main = do
    traverse_ (printComputation) [1..8]