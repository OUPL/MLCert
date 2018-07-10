{-# LANGUAGE StandaloneDeriving #-}

module Main where

import System.Random

import Perceptron

deriving instance (Show a, Show b) => Show (Prod a b)

n = S (S O)
m = S (S (S O))

hypers = MkHypers 1.0 1.5

training_set = 
  [Pair [1.0, -1.0] False,
   Pair [1.0, 0.5] True,
   Pair [-0.5, 0.5] True]

sampler _ f = f training_set

dist _ = 0.5

init_weights :: Weights
init_weights = [0.5, 4.0]

init_bias :: Bias
init_bias = 0.0

main =
  putStrLn
  $ show
  $ perceptron n m hypers sampler dist (Pair init_weights init_bias) id
