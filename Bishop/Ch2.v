(* BEAWARE If you change the order of these two lines, your COQ will be fucked up! *)
From Stdlib Require Import Unicode.Utf8 BinNat Lia Lra.
From Stdlib Require Import QArith Qabs Psatz Zify Qround.
From Stdlib Require Import PArith Qminmax List.

(* From parseque Require Import NEList. *)

From Ltac2 Require Import Ltac2.
From Ltac2 Require Import Ltac1.

From Bishop Require Import Tactics.

(* From Hammer Require Import Tactics. *)

(* From Stdlib Require Import All. 
   Search Qle. 
  *)
  
(* Why Didn't they prove this! *)
Lemma Qeq_cancel_r a : a - a == 0. Proof. ring. Qed. 
Lemma Qeq_cancel_l a : -a + a == 0. Proof. ring. Qed.
Lemma Qminus_assoc x y z : x + (- y + z) == x - y + z. Proof. ring. Qed.
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

Definition exists_of_Req_def x y : x =ʳ y -> ∀j, { N:positive | ∀n, (N <= n)%positive -> Qabs (seq x n - seq y n) <= Qmake 1 j}.
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
Lemma Req_iff_exists x y : x =ʳ y <-> ∀j, ∃N, ∀n, (N <= n)%positive -> Qabs (seq x n - seq y n) <= Qmake 1 j .
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

Theorem Req_trans x y z : x =ʳ y -> y =ʳ z -> x =ʳ z.
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

(* canonical bound *)
Compute Qceiling (331 # 20).

(* Note that this definition is a little different from Bishop's book *)
Definition K (x : R) : Z := (Qfloor (Qabs (seq x 1) + 0.5) + 2)%Z. 

Definition Kp (x : R) : positive := Z.to_pos (K x).
(* Wrong Definition. K' isn't the least integer.
Definition K' (x : R) : Z := (Qfloor (Qabs (seq x 1)) + 3)%Z. 
Compute K (of_Q 2).
Compute K' (of_Q 2). *)

Lemma K_gt x n : Qabs (seq x n) < inject_Z (K x).
Proof.
  assert _ by exact (Qlt_floor (Qabs (seq x 1) + 0.5)).
  destruct (Pos.eq_dec n 1).
  - rewrite e. unfold K. stepr (inject_Z (Qfloor (Qabs (seq x 1) + 0.5) + 1) + 1).
    + lra.
    + proveeq.
      repeat (rewrite inject_Z_plus). ring.
  - stepl (Qabs (seq x n - seq x 1) + Qabs (seq x 1)).
    stepl ((1 # n) + 1 + Qabs (seq x 1)).
    stepl (Qabs (seq x 1) + 0.5 + 1).
    unfold K.
    stepr (inject_Z (Qfloor (Qabs (seq x 1) + 0.5) + 1) + 1).
    + lra.
    + proveeq.
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
