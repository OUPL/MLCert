
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
Require Import List. Import ListNotations. 
Require Import NArith.
Require Import OUVerT.dyadic.

Require Import net bitnet out.
Import out.TheNet.
Import TheNet. Import F. Import FT. Import NETEval. Import NET.

(* This simplifies the annoying conflict between list types *)
Extract Inductive list => list [ "[]" "( :: )" ].

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


(************************)
(** Print batch of data *)

(* Definition load_batch_0 := load_batch 0. *)
(* Definition d_batch := map (fun sample : nat * InputEnv.t => *)
(*                              let (lbl, img) := sample in *)
(*                              map (fun p => to_dyadic (snd p)) *)
(*                                  (InputEnv.to_list img)) *)
(*                           (load_batch_0). *)
(* Extraction "extract/batch_test.ml" d_batch. *)


(**************************)
(** Print network outputs *)

Definition predict_batch (n : nat) :=
  let batch := load_batch n in
  map (fun sample : (nat * InputEnv.t) =>
         let (_, img) := sample in
         TheNet.seval theta (FT.Forest.of_list
                               (combine (Forest.Ix.enumerate_t) outputs))
                      img) batch.
Definition predict_batch_0 := map (fun outputs =>
                                     map snd (FU.Output.to_list outputs))
                                  (predict_batch 0).
Check predict_batch_0.
Extraction "extract/predict_test.ml" predict_batch_0.

(*
Replace predict_batch_0 in extracted program with this:

let rec int_of_positive = function
  | XI p -> 2 * (int_of_positive p) + 1
  | XO p -> 2 * (int_of_positive p)
  | XH -> 1
let int_of_z = function
  | Z0 -> 0
  | Zpos p -> int_of_positive p
  | Zneg p -> - (int_of_positive p)
let float_of_d d =
  float_of_int (int_of_z (num d)) /. (2.0 ** float_of_int (int_of_positive (den d)))
let string_of_d d = string_of_float (float_of_d d)
let predict_batch_0 =
  let l = map (fun v -> map snd (TheNet.F.FU.Output.to_list v)) (predict_batch O) in
  List.iter (fun l' ->
      print_endline (String.concat ", "
                       (List.map (fun x ->
                            string_of_d x) l'))) l;
  l

*)


(******************)
(** Print weights *)

(* Definition theta_list := map (fun (p : ParamEnv.Ix.t * BitVec16Payload.t) => *)
(*                                 let (_, b) := p in *)
(*                                 to_dyadic b) *)
(*                              (ParamEnv.to_list theta). *)
(* Extraction "extract/params.ml" theta_list. *)

(*
Add this code to extracted program:

let rec int_of_positive = function
  | XI p -> 2 * (int_of_positive p) + 1
  | XO p -> 2 * (int_of_positive p)
  | XH -> 1
let int_of_z = function
  | Z0 -> 0
  | Zpos p -> int_of_positive p
  | Zneg p -> - (int_of_positive p)
let float_of_d d =
  float_of_int (int_of_z (num d)) /. (2.0 ** float_of_int (int_of_positive (den d)))
let () =
  let l = List.map float_of_d theta_list in
  List.iteri (fun i x -> print_endline (string_of_int i ^ ": " ^ string_of_float x)) l

*)