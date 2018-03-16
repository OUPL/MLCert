
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
Require Import List. Import ListNotations. 
Require Import NArith.
Require Import OUVerT.dyadic.

Require Import net bitnet out.
Import out.TheNet.
Import TheNet. Import F. Import FT. Import NETEval. Import NET.

(* Eval compute in (length samples). *)
(* Definition train_set := combine samples labels. *)
(* This hangs *)
(* Eval compute in (hd_error samples). *)

(* Import DyadicFloat16. (*for bits_to_bvec*) *)
(* Definition bvec := bits_to_bvec [0%N; 1%N]. *)
(* This doesn't compute properly *)
(* Eval compute in bvec. *)


(* This simplifies the annoying conflict between list types *)
Extract Inductive list => list [ "[]" "( :: )" ].


(** Two implementations are given below.*)

(** 1) This tries to minimize the amount of handwritten OCaml code, so
  the ocaml function just loads the lines, splits them by whitespace,
  and converts everything to N.t. Coq is then responsible for parsing
  the rest of the way and building the InputEnvs (which requires
  assuming that all of the variable ids are less than InputEnv.n). *)

(* Axiom load_raw_batch : nat -> list (list N.t). *)
(* Extract Constant load_raw_batch => *)
(* "fun n -> *)
(* let rec int_of_nat = function *)
(*   | O -> 0 *)
(*   | S n -> 1 + int_of_nat n in *)

(* let rec positive_of_int (i : int) : positive = *)
(*   match i with *)
(*   | _ when i <= 0 -> failwith ""positive_of_int expects positive int"" *)
(*   | _ when i = 1 -> XH *)
(*   | _ when i mod 2 = 0 -> XO (positive_of_int (i / 2)) *)
(*   | _ -> XI (positive_of_int (i / 2)) in *)

(* let rec n_of_int (i : int) : n = *)
(*   match i with *)
(*   | _ when i < 0 -> failwith ""n_of_int expects nonnegative int"" *)
(*   | _ when i = 0 -> N0 *)
(*   | _ -> Npos (positive_of_int i) in *)

(* (* https://stackoverflow.com/a/5775024/6751010 *) *)
(* let read_file filename = *)
(*   let lines = ref [] in *)
(*   let chan = open_in filename in *)
(*   try *)
(*     while true; do *)
(*       lines := input_line chan :: !lines *)
(*     done; !lines *)
(*   with End_of_file -> *)
(*     close_in chan; *)
(*     List.rev !lines in *)

(* (* Hand-rolled alternative to split_on_char (OCaml >= 4.04.0 only)*) *)
(* let tokenize_string s = *)
(*   let rec aux s acc = *)
(*     if String.length s = 0 then [] *)
(*     else *)
(*       let c = String.get s 0 in *)
(*       if c = ' ' then *)
(*         if List.length acc > 0 then *)
(*           (String.init (List.length acc) (fun i -> List.nth acc i)) :: *)
(*             aux (String.sub s 1 (String.length s - 1)) [] *)
(*         else *)
(*           aux (String.sub s 1 (String.length s - 1)) [] *)
(*       else *)
(*         aux (String.sub s 1 (String.length s - 1)) (acc @ [c]) *)
(*   in aux s [] in *)

(* let batch = read_file (""batch_"" ^ (string_of_int (int_of_nat n))) in *)
(* List.map (fun l -> List.map (fun s -> *)
(* n_of_int (int_of_string s)) (tokenize_string l)) batch". *)

(* Notation "'mk' x" := (@InputEnv.Ix.mk x _) (at level 65). *)

(* Fixpoint parse_image (image : list N.t) *)
(*   : list (N.t * BitVec.t) := *)
(*   match image with *)
(*   | x :: n :: rest => *)
(*     let rest' := parse_image (drop (N.to_nat n) rest) in *)
(*     (x, bits_to_bvec (take (N.to_nat n) rest)) :: rest' *)
(*   | _ => [] *)
(*   end. *)

(* Fixpoint parse_sample (sample : list N.t) *)
(*   : nat * list (N.t * BitVec.t) := *)
(*   match sample with *)
(*   | lbl :: image => (N.to_nat lbl, parse_image image) *)
(*   | _ => (0, []) *)
(*   end. *)

(* Program Definition load_batch (n : nat) := *)
(*   map (fun (p : nat * list (N.t * BitVec.t)) => *)
(*          let (lbl, img) := p in *)
(*          (lbl, InputEnv.of_list *)
(*                  (map (fun p : N.t * BitVec.t => *)
(*                          let (x, b) := p in *)
(*                          (mk x, b)) img))) *)
(*       (map parse_sample (load_raw_batch n)). *)
(* Next Obligation. *)
(* (* Hmmm. I would like to assume this as an axiom, given that x came *) *)
(* (*    from load_raw_batch. *) *)
(* Admitted. *)


(** 2) Here we do everything in handwritten OCaml, returning the batch
  as a zipped list of labels and InputEnvs. *)

Axiom load_batch : nat -> list (nat * InputEnv.t).
Extract Constant load_batch =>
"fun n ->
let rec int_of_nat = function
  | O -> 0
  | S n -> 1 + int_of_nat n in

let rec positive_of_int (i : int) : positive =
  match i with
  | _ when i <= 0 -> failwith ""positive_of_int expects positive int""
  | _ when i = 1 -> XH
  | _ when i mod 2 = 0 -> XO (positive_of_int (i / 2))
  | _ -> XI (positive_of_int (i / 2)) in

let rec n_of_int (i : int) : n =
  match i with
  | _ when i < 0 -> failwith ""n_of_int expects nonnegative int""
  | _ when i = 0 -> N0
  | _ -> Npos (positive_of_int i) in

(* https://stackoverflow.com/a/5775024/6751010 *)
let read_file filename = 
  let lines = ref [] in
  let chan = open_in filename in
  try
    while true; do
      lines := input_line chan :: !lines
    done; !lines
  with End_of_file ->
    close_in chan;
    List.rev !lines in

(* Hand-rolled alternative to split_on_char (OCaml >= 4.04.0 only)*)
let tokenize_string s =
  let rec aux s acc =
    if String.length s = 0 then []
    else
      let c = String.get s 0 in
      if c = ' ' then
        if List.length acc > 0 then
          (String.init (List.length acc) (fun i -> List.nth acc i)) ::
            aux (String.sub s 1 (String.length s - 1)) []
        else
          aux (String.sub s 1 (String.length s - 1)) []
      else
        aux (String.sub s 1 (String.length s - 1)) (acc @ [c])
  in aux s [] in

let rec drop n l =
  match n with
  | _ when n <= 0 -> l
  | _ -> match l with
         | [] -> []
         | x :: xs -> drop (n-1) xs in

let rec take n l =
  match n with
  | _ when n <= 0 -> []
  | _ -> match l with
         | [] -> []
         | x :: xs -> x :: take (n-1) xs in

let rec parse_image = function
  | x :: n :: rest -> (x, take n rest) :: parse_image (drop n rest)
  | [] -> []
  | _ -> failwith ""parse_image"" in

let parse_sample = function
  | lbl :: image -> (lbl, parse_image image)
  | _ -> failwith ""parse_sample"" in

let sample_to_n (lbl, parsed_image) =
  (n_of_int lbl, List.map (fun (x, bits) ->
                     (n_of_int x, List.map n_of_int bits))
                   parsed_image) in

let construct_InputEnv (image : (n * (n list)) list) =
  (TheNet.F.FT.NETEval.NET.InputEnv.of_list
      (List.map (fun (x, bits) ->
           Pair (x, (DyadicFloat16.bits_to_bvec bits)))
         image)) in

let batch = read_file (""batch_"" ^ (string_of_int (int_of_nat n))) in
let samples = List.map (fun x ->
                  sample_to_n
                    (parse_sample
                       (List.map int_of_string (tokenize_string x))))
                batch in
List.map (fun (lbl, image) ->
    Pair (lbl, construct_InputEnv image))
  samples".


(* (* Test by loading batch 0. *) *)
(* Definition load_batch_0 := load_batch 0. *)
(* Extraction "extract/batch_test.ml" load_batch_0. *)

(* Definition compute_loss (sample : nat * InputEnv.t) := *)
(*   let (lbl, img) := sample in *)
(*   let outs := TheNet.seval theta *)
(*                            (FT.Forest.of_list *)
(*                               (combine (Forest.Ix.enumerate_t) outputs)) *)
(*                            img in *)
(*   let pred := FU.Output.argmax Dlt_bool outs in *)
(*   if N.to_nat (FU.Output.Ix.val pred) == lbl then DRed.t0 else DRed.t1. *)

(* Definition eval_batch (n : nat) := *)
(*   let batch := load_batch n in *)
(*   let losses := map compute_loss batch in *)
(*   fold_right (fun x acc => DRed.add x acc) DPayload.t0 losses. *)

(* Definition eval_batch_0 := eval_batch 0. *)

(* Extraction "extract/batch_test.ml" eval_batch_0. *)


Import DyadicFloat16. (*for bits_to_bvec*)
Definition bvec := bits_to_bvec [7%N; 8%N; 9%N; 10%N; 11%N; 12%N; 13%N].
(* Definition bvec := bits_to_bvec [13%N; 12%N; 11%N; 10%N; 9%N; 8%N; 7%N]. *)
(* Definition bvec := bits_to_bvec (rev [7%N; 8%N; 9%N; 10%N; 11%N; 12%N; 13%N]). *)
Definition d_val := to_dyadic bvec.
Extraction "extract/d_test.ml" d_val.


(* Replace d_val in the extracted program with this. *)
(*
let rec int_of_positive = function
  | XI p -> 2 * (int_of_positive p) + 1
  | XO p -> 2 * (int_of_positive p)
  | XH -> 1
let int_of_z = function
  | Z0 -> 0
  | Zpos p -> int_of_positive p
  | Zneg p -> - (int_of_positive p)
let int_of_d d =
  float_of_int (int_of_z (num d)) /. (2.0 ** float_of_int (int_of_positive (den d)))
let rec string_of_positive = function
  | XI XH -> "XI XH"
  | XI p -> "XI (" ^ string_of_positive p ^ ")"
  | XO XH -> "XO XH"
  | XO p -> "XO (" ^ string_of_positive p ^ ")"
  | XH -> "XH"
let string_of_z = function
  | Z0 -> "Z0"
  | Zpos XH -> "Zpos XH"
  | Zpos p -> "Zpos (" ^ string_of_positive p ^ ")"
  | Zneg XH -> "Zneg XH"
  | Zneg p -> "Zneg (" ^ string_of_positive p ^ ")"
let d_val =
  let x = DyadicFloat16.to_dyadic bvec in
  print_endline (string_of_z (num x));
  print_endline (string_of_int (int_of_z (num x)));
  print_endline (string_of_positive (den x));
  print_endline (string_of_int (int_of_positive (den x)));
  print_endline (string_of_float (int_of_d x));
  x
*)