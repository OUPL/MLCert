Require Import Ascii String.
Require Import List. Import ListNotations. 
Require Import Coq.Program.Basics.
Require Import Extraction.

Require Import OUVerT.dyadic.
Require Import MLCert.axioms.

Open Scope program_scope.

Definition print_nat : nat -> nat := id.
Extract Constant print_nat =>
"fun n -> 
  let rec int_of_nat = function
    | O -> 0
    | S n' -> 1 + int_of_nat n'
  in (print_int (int_of_nat n); n)".

Definition print_D : D -> D := id.
Extract Constant print_D =>
"fun d ->
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
(print_float (float_of_d d); d)".

Definition print_DRed : DRed.t -> DRed.t := id.
Extract Constant print_DRed =>
"fun d ->
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
(print_float (float_of_d d); d)".

Definition print_newline : forall {X}, X -> X := fun _ x => x.
Extract Constant print_newline =>
"fun x -> print_newline (); x".

Definition print_ascii_nats : forall {X}, list nat -> X -> X := fun _ _ x => x.
Extract Constant print_ascii_nats =>
"fun l x ->
  let rec int_of_nat = function
    | O -> 0
    | S n' -> 1 + int_of_nat n'
  in
  List.iter (fun n -> print_char (Char.chr (int_of_nat n))) l; x".

Fixpoint string_ascii (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String x s' => x :: string_ascii s'
  end.

Definition print_string {X} : string -> X -> X :=
  print_ascii_nats ∘ (map nat_of_ascii) ∘ string_ascii.

Definition print_space {X} : X -> X := print_string " ".

(* Force left-to-right evaluation order... *)
Definition tuple_fun : forall {A B C}, (A -> B) -> (A -> C) -> A -> B*C :=
  fun _ _ _ f g x => (f x, g x).
Extract Constant tuple_fun =>
"fun f g x -> let a = f x in let b = g x in (a, b)".


(* Print a pair in machine-readable format. *)
Definition print_pair {A B} (f : A -> A) (g : B -> B) : A*B -> A*B :=
  tuple_fun (f ∘ fst) (g ∘ print_space ∘ snd).

(* Print a vector in machine-readable format. *)
Definition print_vector {A n} (f : A -> A) : AxVec n A -> AxVec n A :=
  AxVec_map (print_space ∘ f).

(* Print a matrix in machine-readable format. *)
Definition print_matrix {A n m} (f : A -> A) : AxMat A n m -> AxMat A n m :=
  AxVec_map (print_newline ∘ print_vector f).
