-- Kernel Perceptron Timing Driver
{-# LANGUAGE StandaloneDeriving #-}

module Main where

import System.Random
import System.IO
import Data.List.Split
import Data.Bool
import System.CPUTime
import Text.Printf

import KPerceptron

fromInt 0 = O
fromInt n | n > 0 = S (fromInt $ n - 1)

fromNat O = 0
fromNat (S n) = 1 + fromNat n

dist _ = -1.0 --not used in sampler below

init_weights :: Nat -> Float32_arr
init_weights m = take (fromNat m) $ repeat 0.0

makeKernelParams m dataset = (dataset, (init_weights m))

kernel_predict_specialized n m kparams ak =
  kernel_predict n m list_Foldable (KPerceptron.linear_kernel n) kparams ak
       
sampler hyperplane _ f =
  do { f hyperplane }

print_generalization_err n m mt test (model, training) =
  let (train, params) = model in
  let corrects dataset = 
        map (\(example, label) ->
                if kernel_predict_specialized n m model example == label
                then 1 :: Int
                else 0) dataset
      percent_correct_training
        = fromIntegral (sum $ corrects train) / fromIntegral (fromNat m)
      percent_correct_test
        = fromIntegral (sum $ corrects test) / fromIntegral (fromNat mt)
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

format_lines [] = []
format_lines (x : t) = 
    let y = (splitOn "," x) in
        [((fromInt (read (head y) :: Int ),format_line (init (tail y))), format_label (last y))] ++ (format_lines t)

setupEnv trainfile testfile = 
  do { train_file <- readFile trainfile;
       test_file <- readFile testfile;
       let train = format_lines (lines train_file) in
       let test = format_lines (lines test_file) in
       return (test, train)}

trials trainfile testfile n m mt epochs = do {
    putStrLn trainfile;
    (test, train) <- setupEnv trainfile testfile;
    start <- getCPUTime;
    kperceptron n m epochs (KPerceptron.linear_kernel n) (sampler train) dist (makeKernelParams m) (print_generalization_err n m mt test);
    end <- getCPUTime;
    let diff = (fromIntegral (end - start)) / (10^12) in
    printf "Training and Testing Time: %0.3f sec\n" (diff :: Double);
    start <- getCPUTime;
    kperceptron n m epochs (KPerceptron.linear_kernel n) (sampler train) dist (makeKernelParams m) (print_generalization_err n m mt test);
    end <- getCPUTime;
    let diff = (fromIntegral (end - start)) / (10^12) in
    printf "Training and Testing Time: %0.3f sec\n" (diff :: Double);
    start <- getCPUTime;
    kperceptron n m epochs (KPerceptron.linear_kernel n) (sampler train) dist (makeKernelParams m) (print_generalization_err n m mt test);
    end <- getCPUTime;
    let diff = (fromIntegral (end - start)) / (10^12) in
    printf "Training and Testing Time: %0.3f sec\n" (diff :: Double);
    start <- getCPUTime;
    kperceptron n m epochs (KPerceptron.linear_kernel n) (sampler train) dist (makeKernelParams m) (print_generalization_err n m mt test);
    end <- getCPUTime;
    let diff = (fromIntegral (end - start)) / (10^12) in
    printf "Training and Testing Time: %0.3f sec\n" (diff :: Double);
    start <- getCPUTime;
    kperceptron n m epochs (KPerceptron.linear_kernel n) (sampler train) dist (makeKernelParams m) (print_generalization_err n m mt test);
    end <- getCPUTime;
    let diff = (fromIntegral (end - start)) / (10^12) in
    printf "Training and Testing Time: %0.3f sec\n" (diff :: Double);
    putStrLn "\n"
}
       
main = do {
    trials "../data/out1train.dat" "../data/out1test.dat" (fromInt 3) (fromInt 1000) (fromInt 1000) (fromInt 5);
    trials "../data/out2train.dat" "../data/out2test.dat" (fromInt 3) (fromInt 1000) (fromInt 1000) (fromInt 5);
    trials "../data/out3train.dat" "../data/out3test.dat" (fromInt 3) (fromInt 1000) (fromInt 1000) (fromInt 5);
    trials "../data/out4train.dat" "../data/out4test.dat" (fromInt 3) (fromInt 1000) (fromInt 1000) (fromInt 5);
    trials "../data/out5train.dat" "../data/out5test.dat" (fromInt 3) (fromInt 1000) (fromInt 1000) (fromInt 5);
    trials "../data/out6train.dat" "../data/out6test.dat" (fromInt 3) (fromInt 1000) (fromInt 1000) (fromInt 5);
    trials "../data/out7train.dat" "../data/out7test.dat" (fromInt 3) (fromInt 1000) (fromInt 1000) (fromInt 5);
    trials "../data/out8train.dat" "../data/out8test.dat" (fromInt 3) (fromInt 1000) (fromInt 1000) (fromInt 5);
    trials "../data/out9train.dat" "../data/out9test.dat" (fromInt 3) (fromInt 1000) (fromInt 1000) (fromInt 5);
    trials "../data/out10train.dat" "../data/out10test.dat" (fromInt 3) (fromInt 1000) (fromInt 1000) (fromInt 5);
    trials "../data/out11train.dat" "../data/out11test.dat" (fromInt 3) (fromInt 1000) (fromInt 1000) (fromInt 5);
    trials "../data/out12train.dat" "../data/out12test.dat" (fromInt 3) (fromInt 1000) (fromInt 1000) (fromInt 5);
    trials "../data/out13train.dat" "../data/out13test.dat" (fromInt 3) (fromInt 1000) (fromInt 1000) (fromInt 5);
    trials "../data/out14train.dat" "../data/out14test.dat" (fromInt 3) (fromInt 1000) (fromInt 1000) (fromInt 5);
    trials "../data/out15train.dat" "../data/out15test.dat" (fromInt 3) (fromInt 1000) (fromInt 1000) (fromInt 5);
    trials "../data/out16train.dat" "../data/out16test.dat" (fromInt 3) (fromInt 1000) (fromInt 1000) (fromInt 5);
    trials "../data/out17train.dat" "../data/out17test.dat" (fromInt 3) (fromInt 1000) (fromInt 1000) (fromInt 5);
    trials "../data/out18train.dat" "../data/out18test.dat" (fromInt 3) (fromInt 1000) (fromInt 1000) (fromInt 5);
    trials "../data/out19train.dat" "../data/out19test.dat" (fromInt 3) (fromInt 1000) (fromInt 1000) (fromInt 5);
    trials "../data/out20train.dat" "../data/out20test.dat" (fromInt 3) (fromInt 1000) (fromInt 1000) (fromInt 5);
    trials "../data/iris50train.dat" "../data/iris50test.dat" (fromInt 4) (fromInt 77) (fromInt 73) (fromInt 5);
    trials "../data/iris75train.dat" "../data/iris25test.dat" (fromInt 4) (fromInt 113) (fromInt 37) (fromInt 5);
    trials "../data/sonar50normtrain.dat" "../data/sonar50normtest.dat" (fromInt 60) (fromInt 116) (fromInt 92) (fromInt 10000);
    trials "../data/sonar75normtrain.dat" "../data/sonar25normtest.dat" (fromInt 60) (fromInt 157) (fromInt 51) (fromInt 10000);
}
         
