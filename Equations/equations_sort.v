From Equations Require Import Equations.
Require Import List Arith.
Require Import Equations_complements.

Import ListNotations.

(***************** Defining a program **************************************)

(* A program to sort sequences of natural numbers.                         *)
Equations insert (x : nat) (l : list nat) : list nat :=
  insert x [] := [x];
  insert x (y :: tl) with inspect (x <=? y) := {
    | true eqn: eq1 := x :: y :: tl;
    | false eqn: eq1 := y :: insert x tl
  }.

Equations sort (l : list nat) : list nat :=
  sort [] := [];
  sort (x :: tl) := insert x (sort tl).

(******************** Defining a specification *****************************)

(* Testing whether a list of numbers is sorted                             *)
Equations sorted (l : list nat) : bool by wf (length l) lt:=
  sorted nil := true;
  sorted [x] := true;
  sorted (x :: y :: tl) := (x <=? y) && sorted (y :: tl).

(******************** Testing on random values *****************************)
Definition test := 
  sort [909; 297; 426; 825; 681; 695; 396; 019; 865; 911; 744; 842; 702;
   254; 971; 447; 890; 268; 378; 973; 011; 530; 967; 301; 540; 783; 544;
   620; 126; 688; 924; 959; 380; 3].

Compute test.

(* Checking that the specification is satisfied on ONE TEST.               *)
Compute sorted test.

(***************************************************************************)
(********* Proving that the specification is ALWAYS satisfied. *************)
(***************************************************************************)

(* auxiliary lemma. *)
Lemma nat_cmp_false (a b : nat) : a <=? b = false -> b <=? a = true.
Proof.
now intros cmpf; apply leb_correct, Nat.lt_le_incl; apply leb_complete_conv.
Qed.

(* Invariant proof for insert *)
Lemma insert_sorted (l : list nat) (n : nat) :
  sorted l = true -> sorted (insert n l) = true.
Proof.
funelim (sorted l).
    now auto.
  rewrite insert_equation_2.
  case (inspect (n <=? x)); intros [|] h; simpl.
    now rewrite sorted_equation_3, h; simpl; rewrite sorted_equation_2.
  rewrite insert_equation_1, sorted_equation_3.
  now rewrite nat_cmp_false; auto.
rewrite Bool.andb_true_iff; intros [cmp rec].
rewrite insert_equation_2.
case (inspect (n <=? x)); intros [|] h; simpl.
  now rewrite sorted_equation_3, h, sorted_equation_3, cmp, rec.
assert (tmp : sorted (insert n (y :: tl)) = true) by auto.
  revert tmp.
rewrite insert_equation_2.
case (inspect (n <=? y)); intros [|] h'; simpl.
  intros tmp; rewrite sorted_equation_3, nat_cmp_false; auto.
rewrite sorted_equation_3, cmp; auto.
Qed.

(* Main proof for the main function *)
Lemma sort_sorted : forall l, sorted (sort l) = true.
Proof.
intros l; funelim (sort l).
  auto.
rewrite insert_sorted; auto.
Qed.
