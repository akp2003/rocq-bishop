From Stdlib Require Import Unicode.Utf8 BinNat Lia Lra.
From Stdlib Require Import QArith Qabs Psatz.

From Stdlib Require Import ssreflect ssrfun ssrbool.

(* From Hammer Require Import Tactics. *)

(* From Stdlib Require Import All. 
   Search Qle. 
  *)
  
(* Why Didn't they prove this! *)
Lemma Qeq_cancel_r a : a - a == 0. Proof. ring. Qed. 
Lemma Qeq_cancel_l a : -a + a == 0. Proof. ring. Qed.
Lemma Qminus_assoc x y z : x + (- y + z) == x - y + z. Proof. ring. Qed.
(* At least COQ is constructive! |=[_](|< [_] |_34N 4 ! *)

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
  rewrite Qeq_cancel_r.
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
  rewrite Qeq_cancel_r.
  easy.
Qed.

Theorem Req_sym x y : x =ʳ y → y =ʳ x.
Proof.
  unfold Req.
  intros.
  rewrite Qabs_Qminus.
  easy.
Qed.

(* Some Extra stuff *)

Lemma Req_of_Qed a b : a = b -> of_Q a =ʳ of_Q b.
Proof.
  intros. rewrite H. exact (Req_refl (of_Q b)).
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

Lemma Qabs_triangle_3 a b c : Qabs (a + b + c) <= Qabs a + Qabs b + Qabs c.
Proof.
  pose proof Qabs_triangle (a+b) c.
  pose proof Qplus_le_compat _ _ (Qabs c) (Qabs c) (Qabs_triangle a b) (Qle_refl (Qabs c)).
  exact (Qle_trans _ _ _ H H0). 
  (* Beautiful proof!*)
Qed.
  

Lemma Qabs_triangle_3_diff a b x y : Qabs (a - b) <= Qabs (a - x) + Qabs (x - y) + Qabs (y - b). 
Proof.
  have h : (a - b) == (a - x) + (x - y) + (y - b). ring.
  rewrite h.
  exact (Qabs_triangle_3 (a - x) (x - y) (y - b)).
Qed.

(* Trying to prove nonsense in COQ (Attempt was not successful though!) *)
(* Lemma l : 1 = 2.
Proof.
  evar (hm : 1 = 2).
  exact hm.
Qed. *)

(* Lemma l0 D : (∀p N, N * p <= D)%N → False.
Proof.
  intros.
  pose proof H (D + 1)%N 1%N.
  lia.
Qed.

Lemma l1 D : (∀p N, N * p <= D)%positive → False.
Proof.
  intros.
  pose proof H (D + 1)%positive 1%positive.
  lia.
Qed. *)

Lemma Qmult_le_replace_nonneg a b c d (hd : 0 <= d) (hb : 0 <= a * b <= c) (had : d <= a) : (d * b <= c).
Proof.
  destruct (Q_dec a 0). destruct s. lra.
  - pose proof Qmult_le_compat_nonneg (a * b) c d a hb (conj hd had).
    rewrite (Qmult_comm c a) in H. rewrite <-Qmult_assoc in H.
    pose proof proj1 (Qmult_le_l (b * d) c a q) H.
    lra.
  - have h : d == 0. lra. rewrite h. lra. 
Qed.

Lemma Zmult_le_replace_nonneg a b c d : ((0 <= d) → (0 <= a * b <= c) → (d <= a) → (d * b <= c))%Z.
Proof.
  intros.
  destruct (ZArith_dec.Z_dec' a 0). destruct s. lia. 
  - pose proof Zorder.Zmult_le_compat (a * b) d c a (proj2 H0) H1 (proj1 H0) H.
    rewrite Zmult_comm in H2.
    rewrite (Zmult_comm a b) in H2. 
    rewrite Zmult_assoc in H2.
    exact (Zorder.Zmult_lt_0_le_reg_r (d * b) c a l H2).
  - have h : (d = 0)%Z. lia. rewrite h. lia. 
Qed.

Lemma forall_Qplus_inv a q n : (∀p, q <= a + (n # p)) → q <= a . 
Proof.
  intros.
  pose proof (Qlt_le_dec a q).
  destruct H0.
  - remember (q - a) as M.
    have h : ∀ p : positive, M <= (n # p). intros. specialize (H p). rewrite HeqM. lra.
    have hM : 0 < M. rewrite HeqM. lra.
    specialize (h ((Z.to_pos n) * Qden (M) + 1)%positive).
    exfalso.
    unfold Qle in h.
    unfold Qlt in hM. simpl in *.
    have hM1 : (1 <= Qnum M)%Z. lia.
    have hh : (1 * Z.pos ((Z.to_pos n) * Qden (M) + 1) <= (n * QDen M))%Z.
      refine (Zmult_le_replace_nonneg (Qnum M) (Z.pos ((Z.to_pos n) * Qden (M) + 1)) (n * QDen M) 1 _ (conj _ h) hM1).
      lia. lia.
    have hh2 : (Z.pos ((Z.to_pos n) * Qden (M) + 1) = Z.pos ((Z.to_pos n) * Qden (M)) + 1)%Z. easy. 
    destruct (ZArith_dec.Z_dec' n 0). destruct s. lia.
    have hhh : (Z.pos (Z.to_pos n * Qden M) = n * (Z.pos (Qden M)))%Z. rewrite Pos2Z.inj_mul. rewrite (Z2Pos.id n l). reflexivity.
    rewrite hh2 in h.
    rewrite hhh in h.
    lia.
    lia.
  - exact q0.
Qed. 

Print Assumptions forall_Qplus_inv.

Definition exists_of_Req_def x y : x =ʳ y -> ∀j, { N:positive | ∀n, (N <= n)%positive -> Qabs (seq x n - seq y n) <= Qmake 1 j}.
Proof. 
  intros. exists (2*j)%positive. intros. unfold Req in H.
  have hn : 2 # n <= 1 # j.
     refine (proj2 (Qinv_le_contravar (2 # n) (1 # j) _ _) _).
     easy. easy.
     rewrite Qinv_pos. rewrite Qinv_pos.
     (* Hint : just unfold Qle and simpl and then enjoy lia! *)
     unfold Qle. simpl. lia.
  exact (Qle_trans _ _ _ (H n) hn).
Defined.

(* (2.3) Lemma. *)
(* Hint : I guess (∀n j, ∃N) is different from (∀j ∃N, ∀n) *)
(* I use sig instead of ∃ *)
Lemma Req_iff_exists x y : x =ʳ y <-> ∀j, ∃N, ∀n, (N <= n)%positive -> Qabs (seq x n - seq y n) <= Qmake 1 j .
Proof.
  constructor.
  - intros. exact (ex_of_sig (exists_of_Req_def x y H j)).
  - unfold Req. intros.
    have h j : Qabs (seq x n - seq y n) <= (2 # n) + (3 # j).
      specialize (H j). destruct H as [N H].
      (* I let m = N+j so max(N,j)<=N+j *)
      remember (N+j)%positive as m. 
      pose proof Qabs_triangle_3_diff (seq x n) (seq y n) (seq x m) (seq y m).
      specialize (H m).
      have hmN : (N <= m)%positive. lia. specialize (H hmN).
      pose proof reg x m n.
      pose proof reg y n m.
      have hj : (1 # m) <= (1 # j). unfold Qle. simpl. lia.
      have hh : 2*(1 # n) + 3*(1 # j) = (2 # n) + (3 # j). easy.
      rewrite <-hh. lra.
    exact (forall_Qplus_inv (2 # n) (Qabs (seq x n - seq y n)) 3 h).
Qed.

(* It is not just a proof, it is an algorithm! *)
Compute proj1_sig (exists_of_Req_def (of_Q 2) (of_Q 2) (Req_of_Qed 2 2 eq_refl) 500).

Lemma Qeq_cancel_middle a b c : a - c + (c - b) == a - b.
Proof.
  ring.
Qed.

Theorem Req_trans x y z : x =ʳ y -> y =ʳ z -> x =ʳ z.
Proof.
  repeat rewrite Req_iff_exists. intros.
  specialize (H (2*j)%positive). destruct H.
  specialize (H0 (2*j)%positive). destruct H0.
  exists (x0 + x1)%positive. intros.
  specialize (H n). specialize (H0 n).
  epose proof Qplus_le_compat _ _ _ _ (H _) (H0 _).
  pose proof Qabs_triangle (seq x n - seq y n) (seq y n - seq z n).
  rewrite Qeq_cancel_middle in H3.
  have h : (1 # 2 * j) + (1 # 2 * j) == (1 # j). unfold Qeq. simpl. lia.
  rewrite h in H2.
  lra. Unshelve. lia. lia.
Qed.

Print Assumptions Req_trans.

(* Why don't they add this to COQ!! *)
Lemma Qle_stepl : ∀ x y z : Q, x <= y → z <= x → z <= y.
Proof.
  intros. lra.
Qed.

Declare Left Step Qle_stepl.
Declare Right Step Qle_trans.

Lemma Qlt_stepl : ∀ x y z : Q, x < y → z <= x → z < y.
Proof.
  intros. lra.
Qed.

Declare Left Step Qlt_stepl.
Declare Right Step Qlt_le_trans.

(* canonical bound *)
Compute Qround.Qceiling (331 # 20).

(* Note that this definition is a little different from Bishop's book *)
Definition K (x : R) : Z := (Qround.Qfloor (Qabs (seq x 1) + 0.5) + 2)%Z. 

(* Wrong Definition. K' isn't the least integer.
Definition K' (x : R) : Z := (Qround.Qfloor (Qabs (seq x 1)) + 3)%Z. 
Compute K (of_Q 2).
Compute K' (of_Q 2). *)

Ltac proofeq  := rewrite Qminmax.Q.OT.le_lteq;right.

Lemma K_ge x n : Qabs (seq x n) < inject_Z (K x).
Proof.
  pose proof Qround.Qlt_floor (Qabs (seq x 1) + 0.5).
  destruct (Pos.eq_dec n 1).
  - rewrite e. unfold K. stepr (inject_Z (Qround.Qfloor (Qabs (seq x 1) + 0.5) + 1) + 1).
    + lra.
    + proofeq.
      repeat rewrite inject_Z_plus. ring.
  - stepl (Qabs (seq x n - seq x 1) + Qabs (seq x 1)).
    stepl ((1 # n) + 1 + Qabs (seq x 1)).
    stepl (Qabs (seq x 1) + 0.5 + 1).
    unfold K.
    stepr (inject_Z (Qround.Qfloor (Qabs (seq x 1) + 0.5) + 1) + 1).
    + lra.
    + proofeq.
      repeat rewrite inject_Z_plus. ring.
    + have h : (1 # n) <= 0.5. unfold Qle. simpl. lia. lra.
    + pose proof reg x 1 n. lra.
    + pose proof Qabs_triangle (seq x n - seq x 1) (seq x 1).
      rewrite <-Qminus_assoc in H0.
      rewrite (Qeq_cancel_l (seq x 1)) in H0.
      rewrite Qplus_0_r in H0.
      assumption.
Qed.

Print Assumptions K_ge.

Definition Rplus (x y : R) : R.
  refine (Rmake (fun (n : positive) => (seq x (2*n)) + (seq y (2*n)) ) _).
  intros.
  stepl (Qabs ((seq x (2 * m) - seq x (2 * n)) + (seq y (2 * m) - seq y (2 * n)))).
  2: { proofeq. refine (Qabs_wd _ _ _). ring. }
  stepl (Qabs (seq x (2 * m) - seq x (2 * n)) + Qabs (seq y (2 * m) - seq y (2 * n))).
  2: { auto using Qabs_triangle. }
Admitted.

Infix "+" := Rplus : R_scope.

(* Compute seq ((of_Q 1) + (of_Q 1))%R . *)
