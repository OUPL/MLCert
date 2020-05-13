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

n = fromInt 4 --the number of dimensions
m = fromInt 113 --the number of samples
epochs = fromInt 5

dist _ = -1.0 --not used in sampler below

init_weights :: Float32_arr
init_weights = take (fromNat m) $ repeat 0.0

makeKernelParams :: [(Ak, Bk)] -> KernelParams [(Ak, Bk)]
makeKernelParams dataset = (dataset, init_weights)

kernel_predict_specialized ::
  KernelParams [(Ak, Bk)] ->
  Ak ->
  Bk
kernel_predict_specialized kparams ak =
  kernel_predict n m list_Foldable (KPerceptron.linear_kernel n) kparams ak
       
sampler hyperplane _ f =
  do { f hyperplane }

print_generalization_err ::
  [(Ak, Bk)] ->
  (KernelParams [(Ak, Bk)], [(Ak, Bk)]) ->
  IO ()
print_generalization_err test (model, training) =
  let (train, params) = model in
  let corrects dataset = 
        map (\(example, label) ->
                if kernel_predict_specialized model example == label
                then 1 :: Int
                else 0) dataset
      percent_correct_training
        = fromIntegral (sum $ corrects train) / fromIntegral (fromNat m)
      percent_correct_test
        = fromIntegral (sum $ corrects test) / fromIntegral (fromNat (fromInt 37))
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
     
trials trainfile testfile = do {
    putStrLn trainfile;
    (test, train) <- setupEnv trainfile testfile;
    start <- getCPUTime;
    kperceptron n m epochs (KPerceptron.linear_kernel n) (sampler train) dist makeKernelParams (print_generalization_err test);
    end <- getCPUTime;
    let diff = (fromIntegral (end - start)) / (10^12) in
    printf "Training and Testing Time: %0.3f sec\n" (diff :: Double);
    start <- getCPUTime;
    kperceptron n m epochs (KPerceptron.linear_kernel n) (sampler train) dist makeKernelParams (print_generalization_err test);
    end <- getCPUTime;
    let diff = (fromIntegral (end - start)) / (10^12) in
    printf "Training and Testing Time: %0.3f sec\n" (diff :: Double);
    start <- getCPUTime;
    kperceptron n m epochs (KPerceptron.linear_kernel n) (sampler train) dist makeKernelParams (print_generalization_err test);
    end <- getCPUTime;
    let diff = (fromIntegral (end - start)) / (10^12) in
    printf "Training and Testing Time: %0.3f sec\n" (diff :: Double);
    start <- getCPUTime;
    kperceptron n m epochs (KPerceptron.linear_kernel n) (sampler train) dist makeKernelParams (print_generalization_err test);
    end <- getCPUTime;
    let diff = (fromIntegral (end - start)) / (10^12) in
    printf "Training and Testing Time: %0.3f sec\n" (diff :: Double);
    start <- getCPUTime;
    kperceptron n m epochs (KPerceptron.linear_kernel n) (sampler train) dist makeKernelParams (print_generalization_err test);
    end <- getCPUTime;
    let diff = (fromIntegral (end - start)) / (10^12) in
    printf "Training and Testing Time: %0.3f sec\n" (diff :: Double);
    putStrLn "\n"
}
       
main = do {
    trials "../data/iris75train.dat" "../data/iris25test.dat"
}
