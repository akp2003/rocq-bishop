(* BEAWARE If you change the order of these two lines, your COQ will be fucked up! *)
From Stdlib Require Import Unicode.Utf8 BinNat Lia Lra.
From Stdlib Require Import QArith Qabs Psatz Zify Qround.
From Stdlib Require Import PArith Qminmax List.

(* From parseque Require Import NEList. *)

From Ltac2 Require Import Ltac2 Printf Ltac1.

From Bishop Require Import Tactics Extra.

(* From Hammer Require Import Tactics. *)

(* From Stdlib Require Import All. 
   Search Qle. 
  *)

Declare Scope R_scope.
Delimit Scope R_scope with R.

(* (2.1) Definition. *)
Structure R : Set := Rmake {
    seq : positive → Q;
    reg (n m : positive) : Qabs (seq m - seq n) <= (1 # m) + (1 # n)
  }.

Module R.

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

(* I use sig instead of ∃ *)
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

Notation "Rmax( x , y , .. , z )" := (Rmax .. (Rmax x y) .. z) : R_scope.

Compute seq (Rmax( (of_Q 1), (of_Q 3) , (of_Q 2242)))%R 3.

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

Notation "Rmin( x , y , .. , z )" := (Rmin .. (Rmin x y) .. z) : R_scope.

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

Lemma Kp_opp x : Kp x = Kp (-x)%R.
Proof.
  unfold Kp.
  rewrite (Z2Pos.inj_iff _ _ (K_pos x) (K_pos (Ropp x))).
  unfold K,Qround. simpl seq.
  rewrite (Qabs_opp (seq x 1)).
  reflexivity.
Qed.

Lemma Kp_abs x : Kp x = Kp (Rabs x).
Proof.
  unfold Kp.
  unfold K,Qround. simpl seq.
  rewrite Qmax_eq_Qabs_self.
  rewrite (Qabs_Qabs (seq x 1)).
  reflexivity.
Qed.

(* (2.6) Proposition. (f) *)
Proposition Rabs_Rmult x y : (Rabs (x * y) ≖ (Rabs x) * (Rabs y))%R.
Proof.
  unfold Req. do 3 (simpl head seq).
  intros.
  do 2 (rewrite <-Kp_abs).
  do 3 (rewrite Qmax_eq_Qabs_self).
  rewrite Qabs_Qmult.
  rewrite Qeq_cancel_r.
  easy.
  (* Beautiful *)
Qed.
  
(* (2.6) Proposition. (g) *)
Proposition of_Q_Rplus a b : of_Q (a + b) ≖ (of_Q a + of_Q b)%R.
Proof.
  refine (R_eq_seq _ _ _).
  intros. simpl. reflexivity.
Qed.

Proposition of_Q_Rmult a b : of_Q (a * b) ≖ (of_Q a * of_Q b)%R.
Proof.
  refine (R_eq_seq _ _ _).
  intros. simpl. reflexivity.
Qed.

Proposition of_Q_Ropp a : of_Q (-a) ≖ (- of_Q a)%R.
Proof.
  refine (R_eq_seq _ _ _).
  intros. simpl. reflexivity.
Qed.

(* (2.7) Definition. *)
Definition IsPos x := { n | (1 # n) < (seq x n) }.

Definition IsNN x := ∀n,  (-1 # n) <= (seq x n).

(* (2.8) Lemma. Part 1 *)
Lemma IsPos_iff x : IsPos x <=> {N | ∀m, (N <= m)%positive -> ((1 # N) <= seq x m) }.
Proof.
  split; intros.
  - destruct H as [n H].
    remember (((seq x n - (1 # n))/2)) as M.
    exists (Qden M). intros.
    stepl (seq x n - Qabs (seq x m - seq x n)).
    destruct (Qlt_le_dec 0 ((seq x m) - (seq x n))).
    erewrite (Qabs_pos). lra. lra.
    erewrite (Qabs_neg). lra. lra.
    stepl (seq x n - (1 # n) - (1 # m)).
    ltac1:(epose proof reg x n m). lra.
    stepl (seq x n - (1 # n) - (1 # (Qden M))).
    apply Qmake_1_le_iff_Posle in H0. lra.
    stepl (2*(1 # (Qden M)) - (1 # (Qden M))).
    pickaxe [1] [1;2].
    rewrite Qmult_comm.
    refine (proj2 (Qle_shift_div_l_iff _ _ _ _) _).
    easy. unfold Qminus in HeqM.
    rewrite <-HeqM.
    assert (0 < M). rewrite HeqM. 
    refine (Qlt_shift_div_l _ _ _ _ _).
    easy. nra.
    unfold Qle. unfold Qlt in H1.
    simpl in *.  
    nia. lra.
  - destruct H.
    exists (x0+1)%positive.
    specialize (q (x0 + 1)%positive).
    assert (x0 <= x0 + 1)%positive by lia.
    destruct (Qle_lt_or_eq _ _ (q H)).
    + stepl (1 # x0).
      exact H0.
      easy.
    + rewrite <-H0.
      unfold Qlt. simpl.
      lia.
Defined.

(* (2.8) Lemma. Part 2 *)
Lemma IsNN_iff x : IsNN x <=> ∀n, {Nn | ∀m, (Nn <= m)%positive -> ((- 1 # n) <= seq x m) }.
Proof.
  (* This proof is AI generated, (GPT 5.6 Sol at High) *)
  (* Future of Formal Verification is going to be wonderful! *)
  split.
  - intros Hnn n.
    exists n.
    intros m Hnm.
    specialize (Hnn m).
    assert (Hrecip : (-1 # n) <= (-1 # m)).
      unfold Qle. simpl. lia.
    lra.
  - intros Heventual n.
    destruct (Qlt_le_dec (seq x n) (-1 # n)) as [Hbad | Hgood].
    + remember (((-1 # n) - seq x n)/2) as M.
      assert (HMpos : 0 < M).
        rewrite HeqM.
        refine (Qlt_shift_div_l _ _ _ _ _).
        easy.
        lra.
      destruct (Heventual (Qden M)) as [Nn HN].
      remember (Nn + (Qden M))%positive as m.
      assert (HNm : (Nn <= m)%positive) by lia.
      specialize (HN m).
      specialize (HN HNm).
      assert (Hden_m : (Qden M < m)%positive) by lia.
      assert (Hrecip : (1 # m) < (1 # (Qden M))).
        unfold Qlt. simpl. lia.
      assert (Hden_M : (1 # (Qden M)) <= M).
        unfold Qle. unfold Qlt in HMpos.
        simpl in HMpos.
        simpl.
        nia.
      destruct (R_seq_le_seq x n m) as [Hreg _].
      apply False_ind.
      assert (Hopp : (-1 # (Qden M)) == -(1 # (Qden M))).
        unfold Qeq. simpl. ring.
      rewrite Hopp in HN.
      assert (Hstrict : (-2*M - (1 # n)) < seq x n) by lra.
      assert (Htwice : 2*M == ((-1 # n) - seq x n)).
        rewrite HeqM.
        apply Qmult_div_r.
        intro Htwo.
        unfold Qeq in Htwo. simpl in Htwo. lia.
      assert (Hopp_n : (-1 # n) == -(1 # n)).
        unfold Qeq. simpl. ring.
      rewrite Hopp_n in Htwice.
      assert (Heqseq : (-2*M - (1 # n)) == seq x n).
        apply (Qeq_trans _ (-(2*M) - (1 # n)) _).
        ring.
        rewrite Htwice.
        ring.
      rewrite Heqseq in Hstrict.
      apply (Qlt_irrefl (seq x n) Hstrict).
    + exact Hgood.
Defined.

(* The following proofs are AI generated, (Anthropic Opus 5) *)
(* The theorems are written by a human *)

Lemma IsPos_of_Req x y : x ≖ y -> IsPos x -> IsPos y.
Proof.
  intros Hxy Hx.
  destruct (IsPos_iff x) as [Hfwd _].
  destruct (Hfwd Hx) as [N' HN].
  exists (4 * N')%positive.
  assert (HleN : (N' <= 4 * N')%positive) by lia.
  specialize (HN (4 * N')%positive HleN).
  assert (Hd : seq x (4 * N')%positive - seq y (4 * N')%positive <= (2 # 4 * N')).
  { refine (Qle_trans _ _ _ (Qle_Qabs _) (Hxy (4 * N')%positive)). }
  assert (Hq : (1 # 4 * N') + (2 # 4 * N') < (1 # N')).
  { rewrite Qinv_plus_distr. unfold Qlt. simpl. lia. }
  lra.
Defined.

Lemma IsNN_of_Req x y : x ≖ y -> IsNN x -> IsNN y.
Proof.
  intros Hxy Hx.
  destruct (IsNN_iff x) as [Hxf _].
  destruct (IsNN_iff y) as [_ Hyb].
  apply Hyb. intro n.
  destruct (Hxf Hx (2 * n)%positive) as [N' HN].
  exists (N' + 4 * n)%positive. intros m Hm.
  assert (HNm : (N' <= m)%positive) by lia.
  specialize (HN m HNm).
  assert (Hd : seq x m - seq y m <= (2 # m)).
  { refine (Qle_trans _ _ _ (Qle_Qabs _) (Hxy m)). }
  assert (Hq : (2 # m) <= (1 # 2 * n)) by (unfold Qle; simpl; lia).
  assert (Hopp : ∀ k : positive, (-1 # k) == - (1 # k))
    by (intros; unfold Qeq; simpl; ring).
  rewrite (Hopp n). rewrite (Hopp (2 * n)%positive) in HN.
  assert (Hhalf : (1 # 2 * n) + (1 # 2 * n) == (1 # n)) by (unfold Qeq; simpl; lia).
  lra.
Defined.

(* First Corollary of Lemma (2.8) *)
Corollary Req_IsPos_iff x y : x ≖ y → IsPos x <=> IsPos y. 
Proof.
  intro H. split.
  - exact (IsPos_of_Req x y H).
  - exact (IsPos_of_Req y x (Req_sym _ _ H)).
Defined.

(* Second Corollary of Lemma (2.8) *)
Corollary Req_IsNN_iff x y : x ≖ y → IsNN x <=> IsNN y. 
Proof.
  intro H. split.
  - exact (IsNN_of_Req x y H).
  - exact (IsNN_of_Req y x (Req_sym _ _ H)).
Defined.

Corollary IsPos_then_IsNN x : IsPos x → IsNN x. 
Proof.
  intros [n Hn] m.
  destruct (R_seq_le_seq x m n) as [Hlow _].
  assert (Hopp : (-1 # m) == - (1 # m)) by (unfold Qeq; simpl; ring).
  rewrite Hopp. lra.
Defined.

(* (2.9) Proposition. (a) Part 1 *)
Proposition Rplus_of_IsNN (x y : R) (HNNx : IsNN x) (HNNy : IsNN y) : 
    IsNN (x + y)%R.
Proof.
Admitted.

(* (2.9) Proposition. (a) Part 2 *)
Proposition Rmult_of_IsNN x y (HNNx : IsNN x) (HNNy : IsNN y) : 
    IsNN (x * y)%R.
Proof.
Admitted.

Proposition Rmult_of_IsPos x y (HPosx : IsPos x) (HPosy : IsPos y) : 
    IsPos (x * y)%R.
Proof.
Admitted.

(* (2.9) Proposition. (b) *)
Proposition Rplus_of_IsPos_IsNN x y (HPosx : IsPos x) (HNNy : IsNN y) : 
    IsPos (x + y)%R.
Proof.
Admitted.

(* (2.9) Proposition. (c) *)
Proposition IsNN_Rabs x : 
    IsNN (Rabs x).
Proof.
Admitted.

(* (2.9) Proposition. (d) *)
Proposition Rmax_of_IsNN x y (HNNx : IsNN x) : 
    IsNN (Rmax x y)%R.
Proof.
Admitted.

Proposition Rmax_of_IsPos x y (HPosx : IsPos x) : 
    IsPos (Rmax x y)%R.
Proof.
Admitted.

(* (2.9) Proposition. (e) *)
Proposition Rmin_of_IsPos x y (HPosx : IsPos x) (HPosy : IsPos y) : 
    IsPos (Rmin x y)%R.
Proof.
Admitted.

Proposition Rmin_of_IsNN x y (HNNx : IsNN x) (HNNy : IsNN y) : 
    IsNN (Rmin x y)%R.
Proof.
Admitted.

End R.

