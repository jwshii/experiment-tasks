From Coq Require Import Bool.
From Coq Require Import Setoid.

Goal 1 = 1.
Proof.
  reflexivity.
Qed.

(*











































*)

(* This task is based on reversible programming languages.
   Everything you need to know is provided here.

   Prove inv_correct below. Remember that your goal
   is to complete the proof as fast as possible. *)

(* We define expressions, statements, and states: *)

Inductive expr :=
| const : bool -> expr
| get1 : expr
| get2 : expr.

Inductive stmnt :=
| cond : expr -> stmnt -> stmnt -> expr -> stmnt
| flip : stmnt
| seq : stmnt -> stmnt -> stmnt.

Definition state := bool.

(* We define how expressions evaluate: *)

Inductive eval : state -> expr -> bool -> Prop :=
| e_const : forall st b,
    eval st (const b) b
| e_get1 : forall st,
    eval st get1 st
| e_get2 : forall st,
    eval st get2 (negb st).

(* And how statements execute: *)

Inductive exec : state -> stmnt -> state -> Prop :=
| e_cond1 : forall st st' e1 e2 s1 s2,
    eval st e1 true -> exec st s1 st' -> eval st' e2 true ->
    exec st (cond e1 s1 s2 e2) st'
| e_cond2 : forall st st' e1 e2 s1 s2,
    eval st e1 false -> exec st s2 st' -> eval st' e2 false ->
    exec st (cond e1 s1 s2 e2) st'
| e_flip : forall st,
    exec st flip (negb st)
| e_seq : forall st st' st'' s1 s2,
    exec st s1 st' -> exec st' s2 st'' ->
    exec st (seq s1 s2) st''.

(* YOUR TASK is to prove the theorem below about the correctness
   of this function for inverting statements: *)

Fixpoint inv (s : stmnt) : stmnt :=
  match s with
  | cond e1 s1 s2 e2 => cond e2 (inv s1) (inv s2) e1
  | flip => flip
  | seq s1 s2 => seq (inv s2) (inv s1)
  end.

(* This is the theorem you need to prove: *)

Theorem inv_correct : forall (s : stmnt) (st st' : state),
  exec st s st' ->
  exec st' (inv s) st.
Proof.
  (* FILL IN HERE *)
Admitted.

