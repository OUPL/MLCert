-- Budget Kernel Perceptron Driver for Running a Dataset
{-# LANGUAGE StandaloneDeriving #-}

module Main where

import System.IO
import Data.List.Split
import Data.Bool

import KPerceptronBudget

fromInt 0 = O
fromInt n | n > 0 = S (fromInt $ n - 1)

fromNat O = 0
fromNat (S n) = 1 + fromNat n

n = fromInt 3 --the number of dimensions
m = fromInt 1000 --the number of samples
sv = fromInt 100 --the number of support vectors
epochs = fromInt 5

dist _ = -1.0 --not used in sampler below

init_weights :: Float32_arr
init_weights = take (fromNat n) $ repeat 0.0

makeBudgetParamhelper :: Nat -> Params
makeBudgetParamhelper O = []
makeBudgetParamhelper (S sv) = (0.0, (init_weights, False)) : (makeBudgetParamhelper sv)

makeBudgetParams dataset = makeBudgetParamhelper (S sv)

kernel_predict_specialized ::
  Params ->
  Akb ->
  Bkb
kernel_predict_specialized kparams ak =
  kernel_predict_budget n sv (KPerceptronBudget.linear_kernel n) list_Foldable kparams ak
       
sampler hyperplane _ f =
  do { f hyperplane }

print_generalization_err test (model, train) =
  let corrects dataset = 
        map (\(example, label) ->
                if kernel_predict_specialized model example == label
                then 1 :: Int
                else 0) dataset
      percent_correct_training
        = fromIntegral (sum $ corrects train) / fromIntegral (fromNat m)
      percent_correct_test
        = fromIntegral (sum $ corrects test) / fromIntegral (fromNat m)
  in putStrLn
     $ "Model: " ++ show model ++ "\n" ++
       "Training: " ++ show percent_correct_training ++ "\n"
       ++ "Test: " ++ show percent_correct_test ++ "\n"
       ++ "Generalization Error: "
       ++ show (abs (percent_correct_training - percent_correct_test))

format_line :: [[Char]] -> [Float32]
format_line [] = []
format_line (x : t) = 
    [(read x :: Float32)] ++ (format_line t)

format_label :: [Char] -> Bool
format_label y = 
    if y == "True" then True else False

format_lines :: [[Char]] -> [([Float32],Bool)]
format_lines [] = []
format_lines (x : t) = 
    let y = (splitOn "," x) in
        [(format_line (init (tail y)), format_label (last y))] ++ (format_lines t)
       
main = 
  do { train_file <- readFile "data/out1train.dat";
        test_file <- readFile "data/out1test.dat";
        let train = format_lines (lines train_file) in
        let test = format_lines (lines test_file) in
        kperceptronbudget n sv epochs (KPerceptronBudget.linear_kernel n) (budget_update n sv list_Foldable) list_Foldable (sampler train) dist
     makeBudgetParams (print_generalization_err test) }
         
