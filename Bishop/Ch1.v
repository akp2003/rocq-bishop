From Stdlib Require Import Unicode.Utf8 BinNat Lia QArith Qabs Qcanon Qabs.

From Coq Require Import ssreflect ssrfun ssrbool.
(* From Stdlib Require Import All. *)

(* (2.1) Definition. *)
Structure R : Set := Rmake {
    seq : positive → Q;
    reg (n m : positive) : Qabs (seq m - seq n) <= Qmake 1 m + Qmake 1 n
    }.

Print R.

Print Assumptions R.

(** From [Q] to [R] *)

Definition of_Q (a:Q) : R.
  refine (Rmake (fun (n : positive) => a ) _).
  intros.
  have h : (a - a) == 0. ring.
  rewrite h.
  easy. 
Defined. (*If you write Qed instead of Defined then Compute will show weird things!*)

Print Assumptions of_Q.

Compute (fun (n : positive) => 1 ) 1%positive.

Compute seq (of_Q 2) 3.

Check reg (of_Q 2) 2 4.

Definition Req (x y : R) : Prop := ∀n, Qabs (seq x n - seq y n) <= Qmake 2 n .

Infix "=ʳ" := Req (at level 70, no associativity).

(* (2.2) Proposition. *)
(** * Properties of equality. *)

Theorem Req_refl x : x =ʳ x.
Proof.
  unfold Req.
  intro.
  have h : seq x n - seq x n == 0. ring.
  rewrite h.
  easy.
Qed.

Theorem Req_sym x y : x =ʳ y → y =ʳ x.
Proof.
  unfold Req.
  intros.
  rewrite Qabs_Qminus.
  easy.
Qed.

(* Why didn't they add this to coq??? *)
Lemma Qinv_le_contravar : forall a b : Q,
    0 < a → 0 < b → (a <= b <-> /b <= /a).
Proof.
  intros a b H H0. split.
  - intro H1. rewrite <- Qmult_1_l. apply Qle_shift_div_r.
    + apply H0.
    + rewrite <- (Qmult_inv_r a).
      * rewrite Qmult_comm.
        apply Qmult_le_l.
        -- apply Qinv_lt_0_compat.  apply H.
        -- apply H1.
      * intro abs. rewrite abs in H. apply (Qlt_irrefl 0 H).
  - intro H1. rewrite <- (Qinv_involutive b). rewrite <- (Qmult_1_l (/ / b)).
    apply Qle_shift_div_l.
    + apply Qinv_lt_0_compat. apply H0.
    + rewrite <- (Qmult_inv_r a).
      * apply Qmult_le_l.
        -- apply H.
        -- apply H1.
      * intro abs. rewrite abs in H. apply (Qlt_irrefl 0 H).
Qed.

(* (2.3) Lemma. *)
Lemma Req_iff_exists x y : x =ʳ y <-> ∀n j, ∃N, (N <= n)%positive -> Qabs (seq x n - seq y n) <= Qmake 1 j .
Proof.
  constructor.
  - intros.
    exists (2*j)%positive.
    intros.
    unfold Req in H.
    have hn : 2 # n <= 1 # j.
      refine (proj2 (Qinv_le_contravar (2 # n) (1 # j) _ _) _).
      easy. easy.
      rewrite Qinv_pos. rewrite Qinv_pos.
      (* Hint : just unfold Qle and simpl and then enjoy lia! *)
      unfold Qle.
      simpl.
      lia.
    exact (Qle_trans _ _ _ (H n) hn).
  - admit.
Admitted.

Print Assumptions Req_iff_exists.

Theorem Req_trans x y z : x =ʳ y -> y =ʳ z -> x =ʳ z.
Proof.
unfold Req; intros XY YZ.
Admitted.
