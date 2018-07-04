module Main where

import System.Random

import Perceptron

type Sampler_state = StdGen

type Training_set = [(Prod A B)]

sampler :: State (Sampler_state,Training_set) (Prod A B)
sampler (g, t) = 
  let (r, g') = randomR (0, length t - 1) g
  in Pair (g', t) (t !! r)

training_set :: Training_set
training_set =
  [Pair [0.0, -1.0] False,
   Pair [1.0, 0.0] True]

init_weights :: Weights
init_weights = [0.0, 0.0]

init_bias :: Bias
init_bias = 0.0

init_sampler_state :: Sampler_state
init_sampler_state = mkStdGen 42

perceptron_test epochs =
  case result of
    Pair (Pair (g, t) (Pair w b)) u -> (w, b)
  where
    result = perceptron epochs sampler
              (Pair (init_sampler_state, training_set)
                    (Pair init_weights init_bias))

main = putStrLn $ show $ perceptron_test (S (S (S (S (S (S (S (S (S (S O))))))))))
