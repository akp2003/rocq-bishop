From Stdlib Require Import Unicode.Utf8 BinNat Lia Lra.
From Stdlib Require Import QArith Qabs Psatz Zify Qround.
From Stdlib Require Import PArith Qminmax List.

From Ltac2 Require Import Ltac2.

From Bishop Require Import Tactics.

From Stdlib Require Import CRelationClasses.

(* Why Didn't they prove this! *)
Lemma Qopp_1_num (p : positive) : (-1 # p) == - (1 # p). Proof. unfold Qeq. simpl. reflexivity. Qed.
Lemma Qeq_cancel_r a : a - a == 0. Proof. ring. Qed. 
Lemma Qeq_cancel_l a : -a + a == 0. Proof. ring. Qed.
Lemma Qopp_dist a b : - (a + b) == (-a - b). Proof. ring. Qed.
Lemma Qminus_assoc x y z : x + (- y + z) == x - y + z. Proof. ring. Qed.
Lemma Qmake_le_one p : 1 # p <= 1. Proof. unfold Qle. simpl. lia. Qed.
Lemma Qmake_1_le_iff_Posle p q : 1 # p <= 1 # q <-> (q <= p)%positive. Proof. unfold Qle. simpl. lia. Qed.
Lemma Qmake_le_iff_Posle p q z (Hz : (0 < z)%Z) : z # p <= z # q <-> (q <= p)%positive. Proof. unfold Qle. simpl. nia. Qed.
Lemma Qmax_eq_Qabs a b : Qmax a b == (a + b + Qabs (a - b)) / 2. 
Proof.
  destruct (Q.max_dec a b).
  - rewrite q.
    rewrite Q.max_l_iff, Qle_minus_iff in q.
    rewrite (Qabs_pos _ q).
    field.
  - rewrite q.
    rewrite Q.max_r_iff, Qle_minus_iff in q.
    rewrite Qabs_Qminus,(Qabs_pos _ q).
    field.
Qed.
Lemma Qmax_eq_Qabs_self a : Qmax a (-a) == Qabs a.
Proof.
  destruct (Q.max_dec a (-a)).
  - rewrite q.
    rewrite Q.max_l_iff, Qle_minus_iff in q.
    assert (0 <= a). lra.
    rewrite (Qabs_pos _ H).
    reflexivity.
  - rewrite q.
    rewrite Q.max_r_iff, Qle_minus_iff in q.
    assert (a <= 0). lra.
    rewrite (Qabs_neg _ H).
    reflexivity.
Qed.

Lemma Qabs_Qabs a : Qabs (Qabs a) == Qabs a.
Proof.
  rewrite Qabs_pos. reflexivity.
  apply Qabs_nonneg.
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
  assert _ by exact (Qabs_triangle (a+b) c).
  assert _ by exact (Qplus_le_compat _ _ (Qabs c) (Qabs c) (Qabs_triangle a b) (Qle_refl (Qabs c))).
  exact (Qle_trans _ _ _ X X0). 
  (* Beautiful proof!*)
Qed.
  
Lemma Qabs_triangle_3_diff a b x y : Qabs (a - b) <= Qabs (a - x) + Qabs (x - y) + Qabs (y - b). 
Proof.
  assert ((a - b) == (a - x) + (x - y) + (y - b)). ring.
  rewrite H.
  exact (Qabs_triangle_3 (a - x) (x - y) (y - b)).
Qed.

(* Lemma l0 D : (∀p N, N * p <= D)%N → False.
Proof.
  intros.
  assert _ by exact (H (D + 1)%N 1%N.
  lia.
Qed.

Lemma l1 D : (∀p N, N * p <= D)%positive → False.
Proof.
  intros.
  assert _ by exact (H (D + 1)%positive 1%positive.
  lia.
Qed. *)

Lemma Qmult_le_replace_nonneg a b c d (Hd : 0 <= d) (hb : 0 <= a * b <= c) (had : d <= a) : (d * b <= c).
Proof.
  destruct (Q_dec a 0). destruct s. lra.
  - assert _ by exact (Qmult_le_compat_nonneg (a * b) c d a hb (conj Hd had)).
    rewrite (Qmult_comm c a) in X. rewrite <-Qmult_assoc in X.
    assert _ by exact (proj1 (Qmult_le_l (b * d) c a q) X).
    lra.
  - assert (d == 0). lra. rewrite H. lra. 
Qed.

Lemma Zmult_le_replace_nonneg a b c d : ((0 <= d) → (0 <= a * b <= c) → (d <= a) → (d * b <= c))%Z.
Proof.
  intros.
  destruct (ZArith_dec.Z_dec' a 0). destruct s. lia. 
  - assert _ by exact (Zorder.Zmult_le_compat (a * b) d c a (proj2 H0) H1 (proj1 H0) H).
    rewrite Zmult_comm in X.
    rewrite (Zmult_comm a b) in X. 
    rewrite Zmult_assoc in X.
    exact (Zorder.Zmult_lt_0_le_reg_r (d * b) c a l X).
  - assert (d = 0)%Z. lia. rewrite H2. lia. 
Qed.

Lemma forall_Qplus_inv a q n : (∀p, q <= a + (n # p)) → q <= a . 
Proof.
  intros.
  assert _ by exact ((Qlt_le_dec a q)).
  destruct X.
  - remember (q - a) as M.
    assert (∀ p : positive, M <= (n # p)). intros. specialize (H p). rewrite HeqM. lra.
    assert (0 < M). rewrite HeqM. lra.
    specialize (H0 ((Z.to_pos n) * Qden (M) + 1)%positive).
    exfalso.
    unfold Qle in H0.
    unfold Qlt in H1. simpl in *.
    assert (1 <= Qnum M)%Z. lia.
    assert (1 * Z.pos ((Z.to_pos n) * Qden (M) + 1) <= (n * QDen M))%Z.
      refine (Zmult_le_replace_nonneg (Qnum M) (Z.pos ((Z.to_pos n) * Qden (M) + 1)) (n * QDen M) 1 _ (conj _ H0) H2).
      lia. lia.
    assert (Z.pos ((Z.to_pos n) * Qden (M) + 1) = Z.pos ((Z.to_pos n) * Qden (M)) + 1)%Z. easy. 
    destruct (ZArith_dec.Z_dec' n 0). destruct s. lia.
    assert (Z.pos (Z.to_pos n * Qden M) = n * (Z.pos (Qden M)))%Z. rewrite Pos2Z.inj_mul. rewrite (Z2Pos.id n l). reflexivity.
    rewrite H4 in H0.
    rewrite H5 in H0.
    lia.
    lia.
  - exact q0.
Qed. 

Print Assumptions forall_Qplus_inv.


Lemma Qeq_cancel_middle a b c : a - c + (c - b) == a - b.
Proof.
  ring.
Qed.

Definition Qround a := Qfloor (a + 0.5).

Notation "⎡ x ⎦" := (Qround x) : Z_scope.


Lemma Qminus_cancel_both a b c : a - c == b - c <-> a == b.
Proof.
  lra.
Qed.

Module Q.

Fixpoint list_max (l : list Q) := 
  match l with
  | nil => None
  | x :: xs => 
    match (list_max xs) with 
    | Some q => Some (Qmax x q)
    | None => Some x
    end
  end.

(* Definition NEList_max (l : NEList Q) := 
  match l with
  | MkNEList x xs => 
    match (list_max xs) with
    | Some q => Qmax x q
    | None => x
    end
  end. *)

(* Lemma list_max_dec (l : list Q) : fold_right or (list_max l = None) (map (fun x => list_max l = Some x) l).
Proof.
  induction l.
  easy.
 *)

End Q.

Lemma Some_eq_Some_iff {A : Type} (x y : A) : Some x = Some y <-> x = y.
Proof.
  split.
  + inversion 1. reflexivity.
  + intros ->. reflexivity.
Qed.

Lemma Qabs_max_le a b c d : (Qmax c d < Qmax a b) -> (Qmax a b == a) -> Qabs (Qmax a b - Qmax c d) <= a - c.
Proof.
  intros. rewrite H0.
  stepl (a - Qmax c d).
  2 : { proveeq. refine (Qabs_pos _ _). unfold Qminus. rewrite <-Qle_minus_iff.
  provelt. rewrite <-H0. exact H. }
  pickaxe [1] [1]. refine (Qopp_le_compat _ _ _).
  apply Q.le_max_l.
Qed.


Lemma Qminus_mult_3 a b c a1 b1 c1 : a*b*c - a1*b1*c1 == a*b*(c - c1) + a*c1*(b - b1) + b1*c1*(a - a1).
Proof.
  ring.
Qed.

Lemma Qminus_mult_2 a b a1 b1 : a*b - a1*b1 == a*(b - b1) + b1*(a - a1).
Proof.
  ring.
Qed.

(* Lemma Kp_Rmult_le_mult x y : (K (x * y)%R <= 2 * K (x) * K (y))%Z.
Proof.
  unfold K. simpl seq.
  do 2 (nameit (seq _ (Pos.max (Kp x) (Kp y))~0) S). 
  set (K x * K y)%Z.
  stepl (Qfloor (Qabs (Sx * Sy) + 0.5) + 2)%Z.
  2 : {  admit. }
Qed. *)

Lemma Qmult_inject_P_Qmake_cancel p p2 z : inject_P p * (z # (p2*p)) == (z # (p2)). 
Proof.
  unfold inject_P.
  rewrite Qmult_inject_Z_l,Pos.mul_comm.
  apply Qreduce_l.
Qed.

Lemma Qabs_Qle x y : Qabs x <= Qabs y -> x <= Qabs y.
Proof.
  intros. destruct (Qlt_le_dec 0 x). 
  - rewrite <-(Qabs_pos x). easy. lra.
  - stepl 0. apply Qabs_nonneg. exact q.
Qed.

Infix "<=>" := iffT (at level 70, no associativity).

Lemma Qmake_inject_P p : 1 # p = / (inject_P p).
Proof.
  auto.
Qed.

Lemma inject_P_to_pos_Qceiling q : q <= inject_P (Z.to_pos (Qceiling q)).
Proof.
  stepl (inject_Z (Qceiling q)).
  unfold inject_P.
  rewrite <-Zle_Qle.
  lia.
  apply Qle_ceiling.
Qed.


Lemma Qabs_dec q : (Qabs q == q) + (Qabs q == -q). 
Proof.
  destruct (Qlt_le_dec 0 q).
  - left.
    refine (Qabs_pos _ _).
    lra.
  - right.
    refine (Qabs_neg _ _).
    lra.
Defined.

Lemma Qle_shift_div_l_iff : forall a b c,
 0 < c -> a*c <= b <-> a <= b/c.
Proof.
  intros.
  split.
  - apply Qle_shift_div_l.
    exact H.
  - intro.
    apply (Qmult_lt_0_le_reg_r _ _ _ (Qinv_lt_0_compat _ H)).
    stepl a. easy.
    proveeq. field.
    lra.
Qed.




