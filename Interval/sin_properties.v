Require Import Reals Lra.
From Coquelicot Require Import Coquelicot.
Require Import Interval.Tactic Interval.Plot.
Open Scope R_scope.

(***************************************************************************)
(****************************** Real functions *****************************)
(***************************************************************************)

Check PI.

Lemma PI_approx2 : 3.14 <= PI <= 3.15.
Proof.
interval.
Qed.

Definition psin := ltac:(plot sin 0 PI).

Plot psin.

Definition psinv := ltac:(plot (fun x => sin (1 / x)) (0.01) (0.2)).

Plot psinv.
(* By comparison, gnuplot has a strange and erroneous behavior close to 0.
   Here is the command line:

   echo "set xrange [0.01:0.2]; plot sin(1/x)" | gnuplot -p

*)

(* Decimal value of PI is 3.141592653589793238462643383279... *)
Lemma val_sin_gt0 : 
  forall x, (0 < sin 3.1415926535) /\
   (0 < x <= 3.14159265358979 -> 0 < sin x).
Proof.
intros x.
  split.
    interval.
set (y := 3.14159265358979).
assert (x_lt_pi : 0 < y < PI).
  unfold y; split. 
    interval.
  Fail interval.
  interval with (i_prec 128).
intros intx.
apply sin_gt_0.
  tauto.
apply Rle_lt_trans with y.
  tauto.
tauto.
Qed.

(* This property can be visualize using gnuplot by typing
  echo "set xrange [0:10]; plot x, sin(x)" | gnuplot -p
*)
Lemma sinx_ltx x : 0 < x -> sin x < x.
Proof.
intros xgt0.
Fail interval.
apply Rminus_gt_0_lt.
(* Cut the proof in two parts: after PI/2 and before. *)
case (Rgt_ge_dec x (PI / 2)).
  assert (sin x <= 1) by (assert (tmp := SIN_bound x); lra).
  assert (tmp := PI2_1).
  lra.
intros xsmall.
(* Show the value of the derivative. *)
assert (der : forall c, 0 <= c <= x -> 
         derivable_pt_lim (fun x => x - sin x) c
           (1 - cos c)).
  intros c _.
  auto_derive.
    auto.
  ring.
destruct (MVT_cor2 (fun x => x - sin x)
           (fun x => 1 - cos x) 0 x xgt0 der) as
  [c [feq cint]].
rewrite sin_0, !Rminus_0_r in feq; rewrite feq.
apply Rmult_lt_0_compat; cycle 1.
  auto.
enough (cos c < 1) by lra.
rewrite <- cos_0.
apply cos_decreasing_1.
        lra.
      lra.
    lra.
  lra.
lra.
Qed.
