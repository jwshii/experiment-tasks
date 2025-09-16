From Coq Require Import Nat.
From Coq Require Import Lia.
From Coq Require Import List.
Import ListNotations.

Goal 1 = 1.
Proof.
  reflexivity.
Qed.

(*











































*)

(* This task is based on _skew binary numbers_. Everything you
   need to know is provided here.

   Prove incr-correct below. Remember that your goal is to
   complete the proof as fast as possible. *)

(* A num is a skew binary number. It consists of a list of digits
   0 (represented by N0), 1 (N1), and 2 (N2), with the least
   significant ("ones") digit at the start of the list. *)

Inductive digit := | N0 | N1 | N2.
Definition num := list digit.

(* To convert a skew binary number to a decimal number, we
   multiply the value of each digit by its weight, where the
   weight of the ith digit (zero-indexed) is 2^(i+1) − 1.
   For example, [N1; N2] converts to 1 * 1 + 2 * 3 = 7, while
   [N2; N1] converts to 2 * 1 + 1 * 3 = 5. The conv function
   does this conversion formally: *)

Definition weight (i : nat) : nat := 2^(i + 1) - 1.

Definition value (n : digit) : nat :=
  match n with
  | N0 => 0
  | N1 => 1
  | N2 => 2
  end.

Fixpoint convi (ns : num) (i : nat) : nat :=
  match ns with
  | nil => 0
  | n :: ns' => value n * weight i + convi ns' (1 + i)
  end.

Definition conv (ns : num) := convi ns 0.

(* A skew binary number is canonical if there is at most one N2,
   and it is to the left of any N1s. For example, [N0; N2] and
   [N2; N1] are canonical, while [N1; N2] is not. *)

Fixpoint no_twos (ns : num) : bool :=
  match ns with
  | nil => true
  | N0 :: ns' => no_twos ns'
  | N1 :: ns' => no_twos ns'
  | N2 :: ns' => false
  end.

Fixpoint canon (ns : num) : bool :=
  match ns with
  | nil => true
  | N0 :: ns' => canon ns'
  | N1 :: ns' => no_twos ns'
  | N2 :: ns' => no_twos ns'
  end.

(* YOUR TASK is to prove the theorem below about the correctness
   of this function for incrementing skew binary numbers: *)

Definition incr1 (ns : num) : num :=
  match ns with
  | nil => [N1]
  | N0 :: ns' => N1 :: ns'
  | N1 :: ns' => N2 :: ns'
  | _ => nil
  end.

Fixpoint incr2 (ns : num) : num :=
  match ns with
  | N0 :: ns' => N0 :: incr2 ns'
  | N2 :: ns' => N0 :: incr1 ns'
  | _ => nil
  end.

Definition incr (ns : num) : num :=
  if no_twos ns then incr1 ns else incr2 ns.

(* Note that we have imported the "lia" tactic to solve
   arithmetic goals, and we also provide this useful lemma: *)

Axiom weight_S : forall (i : nat),
    weight (S i) = 1 + 2 * weight i.

(* This is the theorem you need to prove: *)

Theorem incr_correct: forall (ns : num),
  canon ns = true ->
  conv (incr ns) = 1 + conv ns.
Proof.
  (* FILL IN HERE *)
Admitted.
