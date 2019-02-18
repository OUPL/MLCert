{-# LANGUAGE StandaloneDeriving #-}

module Main where

import System.Random

import KPerceptron

fromInt 0 = O
fromInt n | n > 0 = S (fromInt $ n - 1)

fromNat O = 0
fromNat (S n) = 1 + fromNat n

n = fromInt 20 --the number of dimensions
--m = fromInt 7500 --the number of samples
-- The following m is better for plotting:
m = fromInt 2000 -- 7500 --the number of samples
epochs = fromInt 5

dist _ = -1.0 --not used in sampler below

init_weights :: KernelParams
init_weights = take (fromNat m) $ repeat 0.0

print_training_set [] = return ()
print_training_set (((i,xs),y) : t) =
  let print_xs [] = return ()
      print_xs (x : xs) = putStr (show x) >> putStr "," >> print_xs xs
  in
  do { putStrLn (show $ fromNat i)
     ; print_xs xs
     ; putStrLn (show y)
     ; print_training_set t }

sampler data_set _ f =
  do { putStrLn "Training Set:"
     ; print_training_set data_set
     ; f data_set }

kernel_predict_specialized examples hyperplane ak =
  kernel_predict n m list_Foldable examples hyperplane ak

training_example O = return []
training_example (S n) =
  do { r <- randomRIO (-1.0,1.0)
     ; e <- training_example n
     ; return $ r : e }
training_row i n = 
  do { example <- training_example n
     ; label <- randomRIO (False,True)
     ; return ((i, example), label) }

data_set :: Nat -> Nat -> IO [(Ak, Bk)]
data_set _ O = return []
data_set n (S m)
  = do { r <- training_row m n
       ; t <- data_set n m
       ; return $ r : t }

print_generalization_err test (model, training) =
  let corrects dataset = 
        map (\(example, label) ->
                if kernel_predict_specialized training model example == label
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
       ++ show (abs (percent_correct_training - percent_correct_test))

main =
  do { test <- data_set n m
     ; train <- data_set n m 
     ; kperceptron n m epochs list_Foldable train (sampler train) dist
         init_weights (print_generalization_err test) }


{-main =
  do { hyperplane <- training_example n
     ; test <- test_set hyperplane n m 
     ; kperceptron n m epochs list_Foldable (sampler hyperplane) dist
         init_weights (print_generalization_err test) }-}

-- NOTES:
-- inputs:
-- n = 2
-- m = 7500
-- eps = 0.05
-- should yield probability: 4.45e-7

