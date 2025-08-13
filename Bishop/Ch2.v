(* BEAWARE If you change the order of these two lines, your COQ will be fucked up! *)
From Stdlib Require Import Unicode.Utf8 BinNat Lia Lra.
From Stdlib Require Import QArith Qabs Psatz Zify Qround.
From Stdlib Require Import PArith Qminmax List.

(* From parseque Require Import NEList. *)

From Ltac2 Require Import Ltac2 Printf Ltac1.

From Bishop Require Import Tactics.

(* From Hammer Require Import Tactics. *)

(* From Stdlib Require Import All. 
   Search Qle. 
  *)

(* Why Didn't they prove this! *)
Lemma Qeq_cancel_r a : a - a == 0. Proof. ring. Qed. 
Lemma Qeq_cancel_l a : -a + a == 0. Proof. ring. Qed.
Lemma Qopp_dist a b : - (a + b) == (-a - b). Proof. ring. Qed.
Lemma Qminus_assoc x y z : x + (- y + z) == x - y + z. Proof. ring. Qed.
Lemma Qmake_le_one p : 1 # p <= 1. Proof. unfold Qle. simpl. lia. Qed.
Lemma Qmake_1_le_iff_Posle p q : 1 # p <= 1 # q <-> (q <= p)%positive. Proof. unfold Qle. simpl. lia. Qed.
Lemma Qmake_le_iff_Posle p q z (Hz : (0 < z)%Z) : z # p <= z # q <-> (q <= p)%positive. Proof. unfold Qle. simpl. nia. Qed.
  (* At least COQ is constructive! |=[_](|< [_] |_34N 4 ! *)


Declare Scope R_scope.
Delimit Scope R_scope with R.

(* (2.1) Definition. *)
Structure R : Set := Rmake {
    seq : positive → Q;
    reg (n m : positive) : Qabs (seq m - seq n) <= (1 # m) + (1 # n)
  }.

Lemma R_reg_no_Qabs (r:R) n m : (seq r m - seq r n) <= (1 # m) + (1 # n).
Proof.
  stepl (Qabs (seq r m - seq r n)).
  apply (reg r). apply Qle_Qabs.
Qed.

Lemma R_seq_le_seq x n m : (seq x m) - ((1 # m) + (1 # n)) <= seq x n <= (seq x m) + ((1 # m) + (1 # n)).
Proof.
  exact (proj1 (Qabs_diff_Qle_condition _ _ _) (reg x n m)).
Qed.

Lemma R_seq_le_seq_of_le x n m N (h : (N <= n)%positive) : (seq x m) - ((1 # m) + (1 # N)) <= seq x n <= (seq x m) + ((1 # m) + (1 # N)).
Proof.
  unfold Qminus. rewrite Qopp_dist.
  constructor.
  stepr ((seq x m) + (- (1 # m) - (1 # n))).
  pickaxe [3] [3].
  unfold Qle. simpl. lia.
  rewrite <-Qopp_dist.
  apply R_seq_le_seq.
  stepl ((seq x m) +  ((1 # m) + (1 # n))).
  pickaxe [3] [3].
  unfold Qle. simpl. lia.
  apply R_seq_le_seq.
Qed.

Print R.

Print Assumptions R.

(** From [Q] to [R] *)

#[refine] Definition of_Q (a:Q) : R := {| seq := (fun (n : positive) => a )|}.
  intros.
  rewrite Qeq_cancel_r.
  easy. 
Defined. (*If you write Qed instead of Defined then Compute will show weird things!*)

Print Assumptions of_Q.

Compute (fun (n : positive) => 1 ) 1%positive. (* 1 *)

Compute seq (of_Q 2) 3. (* 2 *)

Check reg (of_Q 2) 2 4.

Definition Req (x y : R) : Prop := ∀n, Qabs (seq x n - seq y n) <= Qmake 2 n .

Infix "≖" := Req (at level 70, no associativity).

Lemma R_eq_seq x y: (∀n, seq x n == seq y n) -> x ≖ y.
Proof.
  unfold Req. intros.
  rewrite H. rewrite Qeq_cancel_r.
  easy.
Qed.

Lemma Req_with_diff_index x y: (x ≖ y) -> ∀n m, Qabs ((seq x n) - (seq y m)) <= (3 # n) + (1 # m).
Proof.
  intros.
  assert ((3 # n) == (1 # n) + (2 # n)).
  rewrite Qinv_plus_distr. simpl. reflexivity.
  rewrite Qabs_diff_Qle_condition.
  constructor.
  - stepr ((seq y n) - ((1 # n) + (1 # m))).
    2 : { apply (proj1 (R_seq_le_seq _ m n)). }
    rewrite <-(Qplus_le_l _ _ (- (seq y n))).
    rewrite <-(Qplus_le_l _ _ ((3 # n) + (1 # m))).
    pickaxe [1;3] [2;4;5]. stepr (2 # n).
    stepl (Qabs (seq x n + - seq y n)).
    apply H. apply Qle_Qabs.
    rewrite H0. lra.
  - stepl ((seq y n) + ((1 # n) + (1 # m))).
    2 : { apply (proj2 (R_seq_le_seq _ m n)). }
    rewrite <-(Qplus_le_l _ _ (- (seq x n))).
    rewrite <-(Qplus_le_l _ _ (-((1 # n) + (1 # m)))).
    pickaxe [1;4] [2;3;5;6]. stepr (2 # n).
    stepl (Qabs (seq y n - seq x n)).
    rewrite Qabs_Qminus.
    apply H. apply Qle_Qabs.
    rewrite H0. lra.
Qed.

(** * Properties of equality. *)
(* (2.2) Proposition. (i) *)
Proposition Req_refl x : x ≖ x.
Proof.
  unfold Req.
  intro.
  rewrite Qeq_cancel_r.
  easy.
Qed.

(* (2.2) Proposition. (ii) *)
Proposition Req_sym x y : x ≖ y → y ≖ x.
Proof.
  unfold Req.
  intros.
  rewrite Qabs_Qminus.
  easy.
Qed.

(* Some Extra stuff *)

Lemma Req_of_Qed a b : a = b -> of_Q a ≖ of_Q b.
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

Definition exists_of_Req_def x y : x ≖ y -> ∀j, { N:positive | ∀n, (N <= n)%positive -> Qabs (seq x n - seq y n) <= Qmake 1 j}.
Proof. 
  intros. exists (2*j)%positive. intros. unfold Req in H.
  assert (2 # n <= 1 # j).
     refine (proj2 (Qinv_le_contravar (2 # n) (1 # j) _ _) _).
     easy. easy.
     rewrite Qinv_pos. rewrite Qinv_pos.
     (* Hint : just unfold Qle and simpl and then enjoy lia! *)
     unfold Qle. simpl. lia.
  exact (Qle_trans _ _ _ (H n) H1).
Defined.

(* (2.3) Lemma. *)
(* Hint : I guess (∀n j, ∃N) is different from (∀j ∃N, ∀n) *)
(* I use sig instead of ∃ *)
Lemma Req_iff_exists x y : x ≖ y <-> ∀j, ∃N, ∀n, (N <= n)%positive -> Qabs (seq x n - seq y n) <= Qmake 1 j .
Proof.
  constructor.
  - intros. exact (ex_of_sig (exists_of_Req_def x y H j)).
  - unfold Req. intros.
    assert (∀j, Qabs (seq x n - seq y n) <= (2 # n) + (3 # j)). intros.
      specialize (H j). destruct H as [N1 H].
      (* I let m = N+j so max(N,j)<=N+j *)
      remember (N1 + j)%positive as m. 
      assert _ by exact (Qabs_triangle_3_diff (seq x n) (seq y n) (seq x m) (seq y m)).
      specialize (H m).
      assert ((N1 <= m)%positive). lia. specialize (H H0).
      assert _ by exact (reg x m n).
      assert _ by exact (reg y n m).
      assert ((1 # m) <= (1 # j)). unfold Qle. simpl. lia.
      assert (2*(1 # n) + 3*(1 # j) = (2 # n) + (3 # j)). easy.
      rewrite <-H2. lra.
    exact (forall_Qplus_inv (2 # n) (Qabs (seq x n - seq y n)) 3 H0).
Qed.

(* It is not just a proof, it is an algorithm! *)
Compute proj1_sig (exists_of_Req_def (of_Q 2) (of_Q 2) (Req_of_Qed 2 2 eq_refl) 500).

Lemma Qeq_cancel_middle a b c : a - c + (c - b) == a - b.
Proof.
  ring.
Qed.

(* (2.2) Proposition. (iii) *)
Proposition Req_trans x y z : x ≖ y -> y ≖ z -> x ≖ z.
Proof.
  repeat (rewrite Req_iff_exists). intros.
  specialize (H (2*j)%positive). destruct H.
  specialize (H0 (2*j)%positive). destruct H0.
  exists (x0 + x1)%positive. intros.
  specialize (H n). specialize (H0 n).
  ltac1:(epose proof (Qplus_le_compat _ _ _ _ (H _) (H0 _))).
  assert _ by exact (Qabs_triangle (seq x n - seq y n) (seq y n - seq z n)).
  rewrite Qeq_cancel_middle in X.
  assert ((1 # 2 * j) + (1 # 2 * j) == (1 # j)). unfold Qeq. simpl. lia.
  rewrite H3 in H2.
  lra. Unshelve. lia. lia.
Qed.

Print Assumptions Req_trans.

#[global]
Add Relation R Req 
  reflexivity proved by Req_refl
  symmetry proved by Req_sym
  transitivity proved by Req_trans as Req_rel.

(* canonical bound *)
Compute Qceiling (331 # 20).

Definition Qround a := Qfloor (a + 0.5).

Notation "⎡ x ⎦" := (Qround x) : Z_scope.

(* Note that this definition is a little different from Bishop's book *)
Definition K x : Z := (⎡(Qabs (seq x 1))⎦ + 2)%Z. 

Definition Kp x : positive := Z.to_pos (K x).
(* Wrong Definition. K' isn't the least integer.
Definition K' (x : R) : Z := (Qfloor (Qabs (seq x 1)) + 3)%Z. 
Compute K (of_Q 2).
Compute K' (of_Q 2). *)

Lemma two_le_Kp x : (2 <= (Kp x))%positive.
Proof.
  unfold Kp,K.
  assert (0<=(⎡(Qabs (seq x 1))⎦))%Z.
  unfold Qround. stepl (Qfloor 0).
  refine (Qfloor_resp_le _ _ _).
  stepr (Qabs (seq x 1)). apply Qabs_nonneg.
  lra. easy.  
  stepl (Z.to_pos 2).
  rewrite <-Zle_Posle.
  all : lia.
Qed.

Lemma K_gt x n : Qabs (seq x n) < inject_Z (K x).
Proof.
  assert _ by exact (Qlt_floor (Qabs (seq x 1) + 0.5)).
  destruct (Pos.eq_dec n 1).
  - rewrite e. unfold K. stepr (inject_Z (Qfloor (Qabs (seq x 1) + 0.5) + 1) + 1).
    + lra.
    + proveeq. unfold Qround.
      repeat (rewrite inject_Z_plus). ring.
  - stepl (Qabs (seq x n - seq x 1) + Qabs (seq x 1)).
    stepl ((1 # n) + 1 + Qabs (seq x 1)).
    stepl (Qabs (seq x 1) + 0.5 + 1).
    unfold K.
    stepr (inject_Z (Qfloor (Qabs (seq x 1) + 0.5) + 1) + 1).
    + lra.
    + proveeq. unfold Qround.
      repeat (rewrite inject_Z_plus). ring.
    + assert ((1 # n) <= 0.5). unfold Qle. simpl. lia. lra.
    + assert _ by exact (reg x 1 n). lra.
    + assert _ by exact (Qabs_triangle (seq x n - seq x 1) (seq x 1)).
      rewrite <-Qminus_assoc in X0.
      rewrite (Qeq_cancel_l (seq x 1)) in X0.
      rewrite Qplus_0_r in X0.
      assumption.
Qed.

Lemma K_pos x : (0 < (K x))%Z.
Proof.
  unfold K.
  assert (0 <= Qfloor (Qabs (seq x 1) + 0.5))%Z. 
    stepl (Qfloor 0). refine (Qfloor_resp_le _ _ _).
    stepr (Qabs (seq x 1)).
    exact (Qabs_nonneg (seq x 1)).
    unfold Qle. simpl. lia.
    easy.
  assert (0 < 2)%Z. lia.
  exact (Z.add_nonneg_pos _ _ H H0).
  (* Either Coq is too stupid or I don't know how to use it!!! *)
Qed.

Lemma Kp_gt x n : Qabs (seq x n) < inject_P (Kp x).
Proof.
  unfold Kp. unfold inject_P. rewrite (Z2Pos.id _ (K_pos x)).
  exact (K_gt x n).
Qed.

Print Assumptions K_gt.

(* (2.4) Definition. Part (a) *)
#[refine] Definition Rplus (x y : R) : R := {| seq := (fun n => (seq x (2*n)) + (seq y (2*n)) ) |}.
  intros.
  do 4 (nameit (seq _ (2*_))).
  stepl (Qabs ((xm - xn) + (ym - yn))).
  2:{ proveeq. refine (Qabs_wd _ _ _). ring. }
  stepl (Qabs (xm - xn) + Qabs (ym - yn)).
  2:{ auto using Qabs_triangle. }
  assert _ by exact (reg x). assert _ by exact (reg y).
  stepl ((1 # 2 * m) + (1 # 2 * n) + ((1 # 2 * m) + (1 # 2 * n))).
  2:{ exact (Qplus_le_compat _ _ _ _ (X _ _) (X0 _ _)). }
  proveeq. unfold Qeq. simpl. lia.
Defined.

Infix "+" := Rplus : R_scope.

Time Compute (1 + 3).

Time Compute seq ((of_Q 1) + (of_Q 3))%R 10. (* 4 *)

(* (2.4) Definition. Part (b) *) 
#[refine] Definition Rmult (x y : R) : R := {| seq := (fun n => (seq x (2*n*(Pos.max (Kp x) (Kp y)))) * (seq y (2*n*(Pos.max (Kp x) (Kp y)))) ) |}.
  intros.
  remember (Pos.max (Kp x) (Kp y)) as k.
  do 4 (nameit (seq _ (2*_*k))).
  stepl (Qabs (xm*(ym - yn) + yn*(xm - xn))).
  2:{ proveeq. refine (Qabs_wd _ _ _). lra. }
  assert (Qabs xm <= (inject_P k)).
  1:{ stepl (inject_P (Kp x)). 2:{ provelt. apply Kp_gt. }
      rewrite <-Posle_Qle. rewrite Heqk. lia. }
  assert (Qabs yn <= (inject_P k)).
  1:{ stepl (inject_P (Kp y)). 2:{ provelt. apply Kp_gt. }
      rewrite <-Posle_Qle. rewrite Heqk. lia. }
  stepl (Qabs xm * Qabs (ym - yn) + Qabs yn * Qabs (xm - xn)).
  2: { do 2 (rewrite <-Qabs_Qmult). apply Qabs_triangle. }
  stepl ((inject_P k) * Qabs (ym - yn) + (inject_P k) * Qabs (xm - xn)).
  2: { pickaxe [1] [1]. pickaxe [1] [1]. exact H. 
  pickaxe [1] [1]. exact H0. }
  stepl ((inject_P k) * ((1 # 2*m*k) + (1 # 2*n*k)) + (inject_P k) * ((1 # 2*m*k) + (1 # 2*n*k))).
  2: { pickaxe [1] [1]. pickaxe [1] [1].
  exact (reg y (2*n*k) (2*m*k)). pickaxe [1] [1]. exact (reg x (2*n*k) (2*m*k)). }
  proveeq. unfold inject_P,inject_Z,Qeq. simpl. lia.
Defined.

Infix "*" := Rmult : R_scope.

Time Compute seq ((of_Q 40) * (of_Q 3))%R 10. (* 120 *)

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

(* (2.4) Definition. Part (c) *) 
#[refine] Definition Rmax (x y : R) : R := {| seq := (fun n => Qmax (seq x n) (seq y n)) |}.
  intros.
  do 4 (nameit (seq _ _)).
  destruct (Qlt_le_dec (Qmax xm ym) (Qmax xn yn)).
  - destruct (Q.max_dec xn yn).
    + stepl (xn - xm). rewrite Qplus_comm. apply R_reg_no_Qabs.
      rewrite Qabs_Qminus. apply (Qabs_max_le _ _ _ _ q q0).
    + stepl (yn - ym). rewrite Qplus_comm. apply R_reg_no_Qabs.
      rewrite Q.max_comm in *. rewrite (Q.max_comm xn yn) in *.
      rewrite Qabs_Qminus. apply (Qabs_max_le _ _ _ _ q q0).
  - destruct (Qle_lt_or_eq _ _ q).
    destruct (Q.max_dec xm ym).
    + stepl (xm - xn). apply R_reg_no_Qabs.
      apply (Qabs_max_le _ _ _ _ H q0).
    + stepl (ym - yn). apply R_reg_no_Qabs.
      rewrite (Q.max_comm xm ym) in *. rewrite Q.max_comm in H.
      rewrite (Q.max_comm xn yn). apply (Qabs_max_le _ _ _ _ H q0).
    + rewrite H. rewrite Qeq_cancel_r. easy.
Defined. 

Print Assumptions Rmax.

Time Compute seq (Rmax (of_Q 1) (of_Q 200)) 20. (* 200 *)
(* Beautiful *)

(* (2.4) Definition. Part (d) *) 
#[refine] Definition Ropp (x: R) : R := {| seq := (fun n => - seq x n) |}.
  intros. unfold Qminus. rewrite Qopp_opp.
  rewrite (Qplus_comm (1 # m) (1 # n)).
  rewrite Qplus_comm. apply reg.
Defined.

Notation "- x" := (Ropp x) : R_scope.

Definition Rminus (x y : R) := (x + - y)%R.

(* (2.4) Definition. Part (e) *) 
Check of_Q. (* use this *)

(* (2.5) Proposition. is already proved in Definition 2.4*) 

Definition Rabs (x : R) := (Rmax x (-x))%R.

Definition Rmin (x y : R) := (- Rmax (-x) (-y))%R.

(* (2.6) Proposition. (a) *)
Proposition Rplus_comm x y : (x + y ≖ y + x)%R.
Proof.
  refine (R_eq_seq _ _ _). intros.
  simpl. apply Qplus_comm.
Qed.

Lemma Rmult_seq_comm x y n : seq (x*y)%R n == seq (y*x)%R n.
Proof.
  simpl. rewrite Pos.max_comm. ring.
Qed.

Proposition Rmult_comm x y : (x * y ≖ y * x)%R.
Proof.
  refine (R_eq_seq _ _ _). apply Rmult_seq_comm.
Qed.

(* (2.6) Proposition. (b) *)
Proposition Rplus_assoc x y z : ((x + y) + z ≖ x + (y + z))%R.
Proof.
  unfold Req. intros. simpl seq. 
  do 2 (nameit (seq _ (n)~0) r2).
  do 3 (nameit (seq _ (n~0)~0) r4).
  stepl (Qabs (r4x - r2x + r2z - r4z)).
  2: { proveeq. refine (Qabs_wd _ _ _). ring. }
  stepl (Qabs (r4x - r2x) + Qabs (r2z - r4z)).
  2: { unfold Qminus. rewrite <-Qplus_assoc. apply Qabs_triangle. }
  stepl ((1 # (n~0~0)) + (1 # (n~0))  + (1 # (n~0)) + (1 # (n~0~0))).
  2: { pickaxe [1] [1;2]. apply reg. apply reg. }
  unfold Qle. simpl. lia.
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

Proposition Rmult_assoc x y z : ((x * y) * z ≖ x * (y * z))%R.
Proof.
  rewrite Req_iff_exists. intros.
  do 2 (simpl head seq).
  do 2 (nameit (_ * _)%R p).
  do 4 (nameit (Pos.max (Kp _) (Kp _)) m).
  exists (6 * j * (Kp x) * (Kp y) * (Kp z))%positive.
  intros.
  do 3 (nameit (seq _ ?[ign]) S).
  do 3 (nameit (seq _ ?[ign]) S2).
  rewrite Qmult_assoc,Qminus_mult_3.
  refine (Qle_stepl _ _ _ _ (Qabs_triangle_3 _ _ _)).
  remember (6 * j * (Kp x) * (Kp y) * (Kp z))%positive as Nj.
  remember (fun x => inject_P (Kp x)) as Kq.
  remember (fun x y => 2 # (6 * j * (Kp x) * (Kp y))) as Aj.
  stepl (Kq x * Kq y * (Aj x y) + Kq x * Kq z * (Aj x z) + Kq y * Kq z * (Aj y z)).
  2 : {
    assert (2=1+1)%Z. easy.
    rewrite HeqAj. rewrite H0.
    do 3 (rewrite <-Qinv_plus_distr).
    rewrite HeqKq.
    pickaxe [1] [1].
    2 : pickaxe [1] [1].
    Local Ltac2 Notation "tac1" := rewrite Qabs_Qmult;
      pickaxe [1] [1;2];
      Control.focus 1 1 (fun () => 
        rewrite Qabs_Qmult;
        pickaxe [1] [1];
        Control.focus 1 1 (fun () => provelt; apply Kp_gt);
        Control.focus 1 1 (fun () => provelt; apply Kp_gt)
        ).
    Local Ltac2 tac2 (n1 : int) (n2 : int) := 
      do n1 (rewrite Qmult_frac_r); pickaxe [1] [1];
      Control.focus 1 1 (fun () => pickaxe [n2] [1]);
      Control.focus 1 1 (fun () => rewrite Qmake_1_le_iff_Posle;
        stepr &Nj; rewrite &HeqNj;
        nia; lia);
      Control.focus 1 1 (fun () => apply Qmake_le_one).
    - tac1.
      refine (Qle_stepl _ _ _ _ (reg z _ _)).
      tac2 6 2. 
      pickaxe [3] [1]. rewrite Qmake_1_le_iff_Posle.
      stepr Nj. rewrite HeqNj.
      nia. lia. apply Qmake_le_one.
    - tac1.
      refine (Qle_stepl _ _ _ _ (reg y _ _)).
      tac2 8 3.
      pickaxe [3] [1]. rewrite Qmake_1_le_iff_Posle.
      stepr Nj. rewrite HeqNj.
      nia. lia. apply Qmake_le_one.
    - tac1.
      refine (Qle_stepl _ _ _ _ (reg x _ _)).
      tac2 6 3.
      pickaxe [2] [1]. rewrite Qmake_1_le_iff_Posle.
      stepr Nj. rewrite HeqNj.
      nia. lia. apply Qmake_le_one.
    }
  stepl (Qabs (1 # j)).
  simpl. lra.
  rewrite HeqAj,HeqKq.
  do 3 (rewrite <-Qmult_assoc).
  do 6 (rewrite Qmult_inject_P_Qmake_cancel).
  unfold Qle. simpl. lia.
Qed.

Print Assumptions Rmult_assoc.

Lemma Qabs_seq_le {nx x y n m A} : (2*A*(Kp x)<=n)%positive -> (2*A*(Kp x)<=m)%positive -> Qabs ((seq x nx) * ((seq y n) - (seq y m))) <= (1 # A).
Proof.
  intros. rewrite Qabs_Qmult.
  stepl (inject_P (Kp x) * ((1 # 2*A*(Kp x)) + (1 # 2*A*(Kp x)))).
  2 : { 
    pickaxe [1] [1].
    provelt. apply Kp_gt.
    stepl ((1 # n) + (1 # m)).
    2 : { apply reg. }
    pickaxe [1] [1].
    all : rewrite Qmake_1_le_iff_Posle; easy. 
   }
  unfold Qle. simpl. lia.
Qed.

(* (2.6) Proposition. (c) *)
Proposition Rmult_plus_distr_r x y z : (x * (y + z) ≖ x * y + x * z)%R.
Proof.
  rewrite Req_iff_exists. intros.
  do 2 (simpl head seq).
  nameit (_ + _)%R p.
  do 3 (nameit (Pos.max (Kp _) (Kp _)) m).
  exists (2 * (4 * j) * Kp x * Kp y * Kp z)%positive. intros.
  do 3 (nameit (seq _ ?[ign]) S).
  do 4 (nameit (seq _ (2 * (2 * n) * _)) S2).
  stepl (Qabs ((Sx * Sy - S2xmxy * S2ymxy) + (Sx * Sz - S2xmxz * S2zmxz))).
  2: { proveeq. refine (Qabs_wd _ _ _). ring. }
  refine (Qle_stepl _ _ _ _ (Qabs_triangle _ _)).
  Check reg (x*y)%R.
  do 2 (rewrite Qminus_mult_2).
  stepr ((1 # (4*j)) + (1 # (4*j)) + (1 # (4*j)) + (1 # (4*j))).
  pickaxe [1] [1;2].
  1,2 : refine (Qle_stepl _ _ _ _ (Qabs_triangle _ _)).
  Local Ltac2 Notation "tac1" c1(constr) c2(constr) := 
      stepr (&n)%positive;
      Control.focus 1 1 (fun () =>
      refine (POrderedType.Positive_as_DT.le_trans _ _ _ _ &H);
      match! goal with 
      [|- (?t <= _)%positive] => stepr ((Kp $c1 * Kp $c2) * $t)%positive
      end;
      Control.focus 1 1 (fun () => apply PosExtra.Pos_le_multiple);
      Control.focus 1 1 (fun () => lia)
      ); nia.
  - pickaxe [1] [1].
    refine (Qabs_seq_le _ _).
    tac1 y z. tac1 y z.
    refine (Qabs_seq_le _ _).
    tac1 x z. tac1 x z.
  - pickaxe [1] [1].
    refine (Qabs_seq_le _ _).
    tac1 y z. tac1 y z.
    refine (Qabs_seq_le _ _).
    tac1 x y. tac1 x y.
  - unfold Qle. simpl. lia.
Qed.  
  
(* (2.6) Proposition. (d) *)
Proposition Rplus_0_l x : ((of_Q 0) + x)%R ≖ x.
Proof.
  unfold Req. simpl seq. intros.
  rewrite Qplus_0_l.
  stepl ((1 # (n~0)) + (1 # n)).
  unfold Qle. simpl. lia.
  apply reg.
Qed.

Proposition Rmult_1_l x : ((of_Q 1) * x)%R ≖ x.
Proof.
  unfold Req. simpl seq. intros.
  rewrite Qmult_1_l.
  stepl ((1 # ((n * Pos.max (Kp (of_Q 1)) (Kp x))~0)) + (1 # n)).
  stepr ((1 # n) + (1 # n)).
  pickaxe [1] [1].
  rewrite Qmake_1_le_iff_Posle. nia.
  unfold Qle. simpl. lia.
  apply reg.
Qed.

(* (2.6) Proposition. (e) *)
Lemma Rplus_opp_r x : (x + - x ≖ (of_Q 0))%R.
Proof.
  unfold Req. do 2 (simpl head seq).
  intros. unfold Qabs,Qle. simpl. lia.
Qed.

#[global]
Add Morphism Rplus 
  with signature Req ==> Req ==> Req as Rplus_mor.
Proof.
  unfold Req. intros.
  simpl head seq.
  do 4 (nameit (seq _ (2 * n)) s).
  stepl (Qabs ((sx - sy) + (sx0 - sy0))).
  2 : { proveeq. refine (Qabs_wd _ _ _). ring. }
  refine (Qle_stepl _ _ _ _ (Qabs_triangle _ _)).
  stepr ((2 # (2 * n)) + (2 # (2 * n))).
  2 : { unfold Qle. simpl. lia. }
  pickaxe [1] [1].
  apply H. apply H0.
Qed.
  
#[global]
Add Morphism Rmult 
  with signature Req ==> Req ==> Req as Rmult_mor.
Proof.
  intros. rewrite Req_iff_exists. intros.
  exists (Kp y0 * 3 * 4 * j * Kp x )%positive. intros.
  simpl head seq.
  do 2 (nameit (2 * n * Pos.max (Kp _) (Kp _))%positive m).
  do 4 (nameit (seq _ ?[ign]) s).
  rewrite Qminus_mult_2.
  refine (Qle_stepl _ _ _ _ (Qabs_triangle _ _)).
  do 2 (rewrite Qabs_Qmult).
  stepr ((1 # (2 * j)) + (1 # (2 * j))).
  2 : { unfold Qle. simpl. lia. }
  pickaxe [1] [1].
  (* Write a tactic to avoid repetition! *)
  stepl (inject_P (Kp x) * ((3 # 12*j*(Kp x)) + (1 # 4*j*(Kp x)))).
  2 : { 
    pickaxe [1] [1].
    provelt. apply Kp_gt.
    stepl ((3 # mxx0) + (1 # myy0)).
    2 : { apply (Req_with_diff_index _ _ H0). }
    pickaxe [1] [1].
    rewrite Qmake_le_iff_Posle.
    stepr n. nia. nia.
    lia.
    rewrite Qmake_1_le_iff_Posle.
    stepr n.
    refine (Pos.le_trans _ _ _ _ H1).
    nia. nia.
   }
  unfold Qle. simpl. lia.
  stepl (inject_P (Kp y0) * ((3 # 12*j*(Kp y0)) + (1 # 4*j*(Kp y0)))).
  2 : { 
    pickaxe [1] [1].
    provelt. apply Kp_gt.
    stepl ((3 # mxx0) + (1 # myy0)).
    2 : { apply (Req_with_diff_index _ _ H). }
    pickaxe [1] [1].
    rewrite Qmake_le_iff_Posle.
    stepr n. nia. nia.
    lia.
    rewrite Qmake_1_le_iff_Posle.
    stepr n.
    refine (Pos.le_trans _ _ _ _ H1).
    nia. nia.
   }
  unfold Qle. simpl. lia.
Qed.

#[global]
Add Morphism Ropp
  with signature Req ==> Req as Ropp_mor.
Proof.
  intros. unfold Req. intros.
  simpl head seq. unfold Qminus. rewrite Qopp_opp.
  rewrite Qplus_comm.
  symmetry in H.
  exact (H n).
Qed.

Definition Rsrt : ring_theory (of_Q 0) (of_Q 1) Rplus Rmult Rminus Ropp Req.
Proof.
  constructor.
  - exact Rplus_0_l.
  - exact Rplus_comm.
  - symmetry. apply Rplus_assoc.
  - exact Rmult_1_l.
  - exact Rmult_comm.
  - symmetry. apply Rmult_assoc.
  - intros. rewrite (Rmult_comm). rewrite (Rmult_comm x z). 
    rewrite (Rmult_comm y z). apply Rmult_plus_distr_r.
  - reflexivity.
  - exact Rplus_opp_r.
Qed.

Add Ring Rring : Rsrt.

(* It feels like enrolling your child in a school! *)

