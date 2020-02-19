{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Main where

import System.Random

import KPerceptronBudget

fromInt 0 = O
fromInt n | n > 0 = S (fromInt $ n - 1)

fromNat O = 0
fromNat (S n) = 1 + fromNat n

n = fromInt 3 --the number of dimensions
m = fromInt 200 --the number of samples
sv = fromInt 20 --the number of support vectors
epochs = fromInt 5

dist _ = -1.0 --not used in sampler below

init_weights :: Float32_arr
init_weights = take (fromNat n) $ repeat 0.0

makeBudgetParamhelper :: Nat -> Params
makeBudgetParamhelper O = []
makeBudgetParamhelper (S sv) = (0.0, ((O, init_weights), False)) : (makeBudgetParamhelper sv)

makeBudgetParams :: [((Ordinal, Float32_arr), Bk)] -> Params
makeBudgetParams dataset = makeBudgetParamhelper (S sv)

categorize :: Nat -> (,) Float32_arr Float32 -> [Float32] -> Bk
categorize n p a =
  case p of {
   (,) w b -> f32_gt (f32_add (f32_dot n w a) b) f32_0}

print_training_set [] = return ()
print_training_set (((i,xs),y) : t) =
  let print_xs [] = return ()
      print_xs (x : xs) = putStr (show x) >> putStr "," >> print_xs xs
  in
  do { putStrLn (show $ fromNat i)
     ; print_xs xs
     ; putStrLn (show y)
     ; print_training_set t }

kernel_predict_specialized ::
  Params ->
  Ak ->
  Bk
kernel_predict_specialized kparams ak =
  kernel_predict_budget n m sv (KPerceptronBudget.linear_kernel n) list_Foldable kparams ak
       
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
training_row hyperplane i n = 
  do { example <- training_example n
     ; let label = categorize n (hyperplane, 0.0) example
     ; return ((i, example), label) }
  where int2bool :: Int -> Bool
        int2bool 0 = False
        int2bool 1 = True

training_set _ _ O = return []
training_set hyperplane n (S m)
  = do { r <- training_row hyperplane m n
       ; t <- training_set hyperplane n m
       ; return $ r : t }

test_set = training_set

instance Show Ordinal where
  show O = "0"
  show (S n) = 'S' : show n

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
     
main = 
  do { hyperplane <- training_example n
     ; test <- test_set hyperplane n m
     ; kperceptronbudget n m sv epochs (KPerceptronBudget.linear_kernel n) (budget_update n m sv list_Foldable) list_Foldable (sampler hyperplane) dist
     makeBudgetParams (print_generalization_err test) }
         
