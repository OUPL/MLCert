{-# LANGUAGE StandaloneDeriving #-}

module Main where

import System.Random

import Perceptron

fromInt 0 = O
fromInt n | n > 0 = S (fromInt $ n - 1)

fromNat O = 0
fromNat (S n) = 1 + fromNat n

n = fromInt 2 --the number of dimensions
--m = fromInt 7500 --the number of samples
-- The following m is better for plotting:
m = fromInt 20 -- 7500 --the number of samples
epochs = fromInt 5

--hypers = MkHypers 1.0 (fromIntegral (fromNat m) / 2.0)
-- The following theta is better for plotting:
hypers = MkHypers 1.0 0.0

dist _ = -1.0 --not used in sampler below

init_weights :: Weights
init_weights = take (fromNat n) $ repeat 0.0

init_bias :: Bias
init_bias = 0.0

print_training_set [] = return ()
print_training_set ((xs,y) : t) =
  let print_xs [] = return ()
      print_xs (x : xs) = putStr (show x) >> putStr "," >> print_xs xs
  in
  do { print_xs xs
     ; putStrLn (show y)
     ; print_training_set t }

sampler hyperplane _ f =
  do { t <- training_set hyperplane n m
     ; putStrLn "Training Set:"
     ; print_training_set t
     ; f t }

training_example O = return []
training_example (S n) =
  do { r <- randomRIO (-1.0,1.0)
     ; e <- training_example n
     ; return $ r : e }
training_row hyperplane n = 
  do { example <- training_example n
     ; let label = predict n 0.0 (hyperplane, init_bias) example
     ; return (example, label) }
  where int2bool :: Int -> Bool
        int2bool 0 = False
        int2bool 1 = True

training_set _ _ O = return []
training_set hyperplane n (S m)
  = do { r <- training_row hyperplane n
       ; t <- training_set hyperplane n m
       ; return $ r : t }

test_set = training_set
  
print_generalization_err test (model, training) =
  let corrects dataset = 
        map (\(example, label) ->
                if predict n (theta hypers) model example == label
                then 1 :: Int
                else 0) dataset
      percent_correct_training
        = fromIntegral (sum $ corrects training) / fromIntegral (fromNat m)
      percent_correct_test
        = fromIntegral (sum $ corrects test) / fromIntegral (fromNat m)
  in putStrLn
     $ "Model: " ++ show model ++ "\n"
       ++ "Training: " ++ show percent_correct_training ++ "\n"
       ++ "Test: " ++ show percent_correct_test ++ "\n"
       ++ "Generalization Error: "
       ++ show (percent_correct_training - percent_correct_test)

main =
  do { hyperplane <- training_example n
     ; test <- test_set hyperplane n m 
     ; perceptron n epochs hypers (sampler hyperplane) dist
         (init_weights, init_bias) (print_generalization_err test) }

-- NOTES:
-- inputs:
-- n = 2
-- m = 7500
-- eps = 0.05
-- should yield probability: 4.45e-7
