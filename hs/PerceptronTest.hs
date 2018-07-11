{-# LANGUAGE StandaloneDeriving #-}

module Main where

import System.Random

import Perceptron

deriving instance (Show a, Show b) => Show (Prod a b)

fromInt 0 = O
fromInt n | n > 0 = S (fromInt $ n - 1)

fromNat O = 0
fromNat (S n) = 1 + fromNat n

n = fromInt 100
m = fromInt 1000
epochs = fromInt 10

hypers = MkHypers 1.0 (fromIntegral (fromNat m) / 2.0)

dist _ = -1.0 --not used in sampler below

init_weights :: Weights
init_weights = take (fromNat n) $ repeat 0.0

init_bias :: Bias
init_bias = 0.0

sampler _ f = training_set n m >>= f

training_example O = return []
training_example (S n) =
  do { r <- randomRIO (-1.0,1.0)
     ; e <- training_example n
     ; return $ r : e }
training_row n = 
  do { example <- training_example n
     ; label <- randomRIO (0,1)
     ; return $ Pair example (int2bool label) }
  where int2bool :: Int -> Bool
        int2bool 0 = False
        int2bool 1 = True

training_set _ O = return []
training_set n (S m)
  = do { r <- training_row n
       ; t <- training_set n m
       ; return $ r : t }
  
show_test_err (Pair model examples_labels) =
  let corrects = 
        map (\(Pair example label) ->
                if predict n (theta hypers) model example == label
                then 1 :: Int
                else 0) examples_labels
  in putStrLn
     $ show
     $ fromIntegral (sum corrects) / fromIntegral (fromNat m)

main =
  perceptron n m epochs hypers sampler dist
    (Pair init_weights init_bias) show_test_err


