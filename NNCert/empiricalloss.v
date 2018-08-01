Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
Require Import List. Import ListNotations. 
Require Import Arith.

Require Import OUVerT.dyadic.

Require Import MLCert.axioms MLCert.extraction_ocaml.

Require Import net bitnet kernel out.

(*NOTE: The code below is specialized to a 16-bit encoding of input image pixels.*)
Axiom load_batch : unit -> list (X * Y).
Extract Constant load_batch =>
"fun _ ->

let float_size = 16 in 
let num_pixels = 784 in 
let batch_size = 100 in 

let rec read_bits = function 
  | 0 -> ((*eat newline:*) let _ = input_char stdin in [])
  | n -> 
    (match input_char stdin with 
     | '0' -> false :: read_bits (n-1)
     | '1' -> true :: read_bits (n-1)
     | _ -> failwith ""Bad char in read_bits"") in 

let rec read_pixels = function 
  | 0 -> [] 
  | n -> read_bits float_size :: read_pixels (n-1) in

let read_image _ = 
  let lbl = read_int () in 
  let pixels = read_pixels num_pixels in
  (lbl, pixels) in

let rec nat_of_int = function
  | 0 -> O
  | n -> S (nat_of_int (n-1)) in

let rec read_batch = function
  | 0 -> []
  | n -> 
    let (y,x) = read_image () in 
    Pair(x,nat_of_int y) :: read_batch (n-1)
in 

read_batch batch_size".

Definition num_correct : nat := 
  let batch := load_batch tt in
  let corrects :=
      filter
        (fun y_y' => let: (Ordinal y _,Ordinal y' _) := y_y' in eq_nat_dec y y')
        (map (fun x_y => let: (x,y) := x_y in (y, predict tt kernel x)) batch) in
  size corrects.

Axiom print_nat : forall n:nat, nat.
Extract Constant print_nat =>
"fun n -> 
  let rec int_of_nat = function
    | O -> 0
    | S n' -> 1 + int_of_nat n'
  in (print_int (int_of_nat n); print_newline (); n)".

Definition result := print_nat num_correct.
Extraction "extract/batch_test.ml" result.
