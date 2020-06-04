-- Description Kernel Perceptron Timing Driver: Synthetic Trials
{-# LANGUAGE StandaloneDeriving #-}

module Main where

import System.Random
import System.IO
import Data.List.Split
import Data.Bool
import System.CPUTime
import Text.Printf

import KPerceptronDes

fromInt 0 = O
fromInt n | n > 0 = S (fromInt $ n - 1)

fromNat O = 0
fromNat (S n) = 1 + fromNat n

n = fromInt 3 --the number of dimensions
m = fromInt 1000 --the number of samples
des = fromInt 99 --the number of support vectors
epochs = fromInt 5

dist _ = -1.0 --not used in sampler below

init_weights :: Float32_arr
init_weights = take (fromNat n) $ repeat 0.0

makeDesParamhelper O = []
makeDesParamhelper (S des) = (init_weights, False) : (makeDesParamhelper des)

makeDesParams dataset = (0.0, makeDesParamhelper (S des))

kernel_predict_specialized ::
  Params ->
  Akd ->
  Bkd
kernel_predict_specialized kparams ak =
  kernel_predict_des n des (KPerceptronDes.linear_kernel n) list_Foldable kparams ak
       
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
     $ "Training: " ++ show percent_correct_training ++ "\n"
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
        
setupEnv trainfile testfile = do { train_file <- readFile trainfile;
        test_file <- readFile testfile;
        let train = format_lines (lines train_file) in
        let test = format_lines (lines test_file) in
        return (test, train)
}
    
trials trainfile testfile = do {
    putStrLn trainfile;
    (test, train) <- setupEnv trainfile testfile;
    start <- getCPUTime;
    kperceptrondes n des epochs 100.0 (KPerceptronDes.linear_kernel n) list_Foldable (sampler train) dist
    makeDesParams (print_generalization_err test);
    end <- getCPUTime;
    let diff = (fromIntegral (end - start)) / (10^12) in
    printf "Training and Testing Time: %0.3f sec\n" (diff :: Double);
    start <- getCPUTime;
    kperceptrondes n des epochs 100.0 (KPerceptronDes.linear_kernel n) list_Foldable (sampler train) dist
    makeDesParams (print_generalization_err test);
    end <- getCPUTime;
    let diff = (fromIntegral (end - start)) / (10^12) in
    printf "Training and Testing Time: %0.3f sec\n" (diff :: Double);
    start <- getCPUTime;
    kperceptrondes n des epochs 100.0 (KPerceptronDes.linear_kernel n) list_Foldable (sampler train) dist
    makeDesParams (print_generalization_err test);
    end <- getCPUTime;
    let diff = (fromIntegral (end - start)) / (10^12) in
    printf "Training and Testing Time: %0.3f sec\n" (diff :: Double);
    start <- getCPUTime;
    kperceptrondes n des epochs 100.0 (KPerceptronDes.linear_kernel n) list_Foldable (sampler train) dist
    makeDesParams (print_generalization_err test);
    end <- getCPUTime;
    let diff = (fromIntegral (end - start)) / (10^12) in
    printf "Training and Testing Time: %0.3f sec\n" (diff :: Double);
    start <- getCPUTime;
    kperceptrondes n des epochs 100.0 (KPerceptronDes.linear_kernel n) list_Foldable (sampler train) dist
    makeDesParams (print_generalization_err test);
    end <- getCPUTime;
    let diff = (fromIntegral (end - start)) / (10^12) in
    printf "Training and Testing Time: %0.3f sec\n" (diff :: Double);
    putStrLn "\n"
}
       
main = do {
    trials "../data/out1train.dat" "../data/out1test.dat";
    trials "../data/out2train.dat" "../data/out2test.dat";
    trials "../data/out3train.dat" "../data/out3test.dat";
    trials "../data/out4train.dat" "../data/out4test.dat";
    trials "../data/out5train.dat" "../data/out5test.dat";
    trials "../data/out6train.dat" "../data/out6test.dat";
    trials "../data/out7train.dat" "../data/out7test.dat";
    trials "../data/out8train.dat" "../data/out8test.dat";
    trials "../data/out9train.dat" "../data/out9test.dat";
    trials "../data/out10train.dat" "../data/out10test.dat";
    trials "../data/out11train.dat" "../data/out11test.dat";
    trials "../data/out12train.dat" "../data/out12test.dat";
    trials "../data/out13train.dat" "../data/out13test.dat";
    trials "../data/out14train.dat" "../data/out14test.dat";
    trials "../data/out15train.dat" "../data/out15test.dat";
    trials "../data/out16train.dat" "../data/out16test.dat";
    trials "../data/out17train.dat" "../data/out17test.dat";
    trials "../data/out18train.dat" "../data/out18test.dat";
    trials "../data/out19train.dat" "../data/out19test.dat";
    trials "../data/out20train.dat" "../data/out20test.dat"
}
         
