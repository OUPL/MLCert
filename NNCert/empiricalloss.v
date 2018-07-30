Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
Require Import List. Import ListNotations. 
Require Import NArith.
Require Import OUVerT.dyadic.

Require Import MLCert.axioms MLCert.extraction_ocaml.

Require Import net bitnet out kernel.

Import out.KTranslate. Import TheNet.
Import TheNet.F. Import NETEval. Import NET.

(* Number of data batches *)
Definition num_batches := 2400.

(* Returns the batch as a zipped list of labels and InputEnvs. *)
Axiom load_batch : nat -> list (N * InputEnv.t).
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
  (KTranslate.TheNet.F.NETEval.NET.InputEnv.of_list
      (List.map (fun (x, bits) ->
           Pair (x, DyadicFloat16.to_dyadic (DyadicFloat16.bits_to_bvec bits)))
         image)) in

let batch = read_file (""batches/batch_"" ^ (string_of_int (int_of_nat n))) in
let samples = List.map (fun x ->
                  sample_to_n
                    (parse_sample
                       (List.map int_of_string (tokenize_string x))))
                batch in
List.map (fun (lbl, image) ->
    Pair (lbl, construct_InputEnv image))
  samples".

Definition compute_correct (sample : N * InputEnv.t) :=
  let (lbl, img) := sample in
  let outs := TheNet.F.seval theta
                      (TheNet.F.Forest.of_list
                         (combine (Forest.Ix.enumerate_t) (rev outputs)))
                      img in
  let pred := Output.argmax Dlt_bool outs in
  (lbl, pred, if Output.Ix.val pred == lbl then DRed.t1 else DRed.t0).

Axiom print_batch_info : nat -> DRed.t -> DRed.t.
Extract Constant print_batch_info =>
"fun n x ->
  let rec int_of_nat = function
    | O -> 0
    | S n -> 1 + int_of_nat n in
  let rec int_of_positive = function
    | XI p -> 2 * (int_of_positive p) + 1
    | XO p -> 2 * (int_of_positive p)
    | XH -> 1 in
  let int_of_z = function
    | Z0 -> 0
    | Zpos p -> int_of_positive p
    | Zneg p -> - (int_of_positive p) in
  let float_of_d d =
    float_of_int (int_of_z (num d)) /. (2.0 ** float_of_int (int_of_positive (den d))) in
  print_endline (""batch "" ^ string_of_int (int_of_nat (n)) ^ "" # correct: ""
                 ^ string_of_float (float_of_d x));
  x".

Definition eval_batch (n : nat) :=
  let batch := load_batch n in
  (* map compute_correct batch. *)
  let (l, correct) := List.split (map compute_correct batch) in
  let (lbls, preds) := List.split l in
  let x := fold_right (fun x acc => DRed.add x acc) DPayload.t0 correct in
  let y := print_batch_info n x in
  y.

Fixpoint range_aux n :=
  match n with
  | O => nil
  | S n' => n' :: range_aux n'
  end.
Definition range n := rev (range_aux n).

Definition eval_batches := fold_right DRed.add DRed.t0 (map eval_batch (range num_batches)).

Axiom print_DRed : DRed.t -> unit.
Extract Constant print_DRed =>
"fun x ->
let rec int_of_positive = function
  | XI p -> 2 * (int_of_positive p) + 1
  | XO p -> 2 * (int_of_positive p)
  | XH -> 1 in
let int_of_z = function
  | Z0 -> 0
  | Zpos p -> int_of_positive p
  | Zneg p -> - (int_of_positive p) in
let float_of_d d =
  float_of_int (int_of_z (num d)) /. (2.0 ** float_of_int (int_of_positive (den d))) in
print_endline (string_of_float (float_of_d x))".


Definition result := print_DRed eval_batches.
Extraction "extract/batch_test.ml" result.


(* (** Some extra stuff for testing *) *)

(* Definition weights := map snd (ParamEnv.to_dense_list theta). *)
(* Check weights. *)
(* Definition print_weights := fold_left (fun _ => print_DRed) weights tt. *)
(* Check print_weights. *)
(* Extraction "extract/batch_test.ml" print_weights. *)

(* Definition load_batch_0 := load_batch 0. *)
(* Check load_batch_0. *)

(* Definition image := map snd (hd [] (map InputEnv.to_list (map snd load_batch_0))). *)
(* Definition print_image := fold_left (fun _ => print_DRed) image tt. *)
(* Check print_image. *)
(* Extraction "extract/batch_test.ml" print_image. *)

(* Definition image := hd (InputEnv.of_list []) (map snd load_batch_0). *)
(* Check image. *)
(* Definition logits := *)
(*   F.seval theta *)
(*           (F.Forest.of_list *)
(*              (combine (F.Forest.Ix.enumerate_t) (rev outputs))) *)
(*           image. *)
(* Definition print_logits := fold_left (fun _ => print_DRed) *)
(*                                      (map snd (Output.to_list logits)) *)
(*                                      tt. *)
(* Extraction "extract/batch_test.ml" print_logits. *)
