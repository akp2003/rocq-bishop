(* BEAWARE If you change the order of these two lines, your COQ will be fucked up! *)
From Stdlib Require Import Unicode.Utf8 BinNat Lia Lra.
From Stdlib Require Import QArith Qabs Psatz Zify Qround.
From Stdlib Require Import PArith Qminmax List CRelationClasses CMorphisms.

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

Infix "-" := Rminus : R_scope.

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
  (* Opus 5 generated, A human finished it! *)
  unfold IsNN. intros n.
  simpl seq.
  assert (Hx := HNNx (2*n)%positive).
  assert (Hy := HNNy (2*n)%positive).
  assert (Hopp : (-1 # n) == (-1 # 2*n) + (-1 # 2*n)).
  { unfold Qeq. simpl. lia. }
  rewrite Hopp.
  apply Qplus_le_compat.
  exact Hx. exact Hy.
Defined.


(* (2.9) Proposition. (a) Part 2 *)
Proposition Rmult_of_IsNN x y (HNNx : IsNN x) (HNNy : IsNN y) : 
    IsNN (x * y)%R.
Proof.
  unfold IsNN. intros n. simpl seq.
  set (M := Pos.max (Kp x) (Kp y)).
  set (m := (2 * n * M)%positive).
  assert (Hxl : - (1 # m) <= seq x m) by (apply HNNx).
  assert (Hyl : - (1 # m) <= seq y m) by (apply HNNy).
  assert (Hxu : Qabs (seq x m) <= inject_P M).
  { apply (Qle_trans _ (inject_P (Kp x))).
    - apply Qlt_le_weak, Kp_gt.
    - rewrite <-Posle_Qle. apply Pos.le_max_l. (* AI could not figure this out! *)
    }
  assert (Hyu : Qabs (seq y m) <= inject_P M).
  { apply (Qle_trans _ (inject_P (Kp y))).
    - apply Qlt_le_weak, Kp_gt.
    - rewrite <-Posle_Qle. apply Pos.le_max_r. (* AI could not figure this out! *) }
  apply (Qle_trans _ (- ((1 # m) * inject_P M))).
  - rewrite Qopp_1_num. apply Qopp_le_compat.
    unfold inject_P, Qle, Qmult. simpl. nia.
  - apply Qmult_lower_bound; try assumption.
    unfold Qle. simpl. lia.
Defined.

Proposition Rmult_of_IsPos x y (HPosx : IsPos x) (HPosy : IsPos y) : 
    IsPos (x * y)%R.
Proof.
  apply IsPos_iff in HPosx as [N1 H1].
  apply IsPos_iff in HPosy as [N2 H2].
  set (M := Pos.max (Kp x) (Kp y)).
  set (n := (N1 * N2 + N1 + N2)%positive).
  exists n. simpl seq.
  set (m := (2 * n * M)%positive).
  assert (HM : (1 <= M)%positive) by apply Pos.le_1_l.
  assert (Hm1 : (N1 <= m)%positive) by (nia).
  assert (Hm2 : (N2 <= m)%positive) by (nia).
  apply (Qlt_le_trans _ ((1 # N1) * (1 # N2))).
  - unfold Qlt, Qmult. simpl. nia.
  (* AI generated, Human completed *)
  -  assert ((n * Pos.max (Kp x) (Kp y))~0 = m)%positive by easy.
     rewrite H.
     apply Qmult_le_compat_nonneg.
    + constructor. easy. apply (H1 m Hm1).
    + constructor. easy. apply (H2 m Hm2).
Defined.

(* (2.9) Proposition. (b) *)
Proposition Rplus_of_IsPos_IsNN x y (HPosx : IsPos x) (HNNy : IsNN y) : 
    IsPos (x + y)%R.
Proof.
  apply IsPos_iff in HPosx as [N1 H1].
  apply IsPos_iff.
  exists (2 * N1)%positive.
  intros m Hm.
  cbn [seq Rplus].
  apply (Qle_trans _ ((1 # N1) + (-1 # 2 * m))).
  - assert (HZ : (Z.pos N1 <= Z.pos m)%Z) by lia.
    assert (Hprod : (Z.pos N1 * Z.pos N1 <= Z.pos N1 * Z.pos m)%Z).
    { apply Z.mul_le_mono_nonneg_l.
      - lia.
      - exact HZ. }
    unfold Qle, Qplus; cbn [Qnum Qden].
    rewrite !Pos2Z.inj_mul.
    nia.
  - apply Qplus_le_compat.
    + apply H1. nia.
    + apply (HNNy (2 * m)%positive).
Defined.

(* (2.9) Proposition. (c) *)
Proposition IsNN_Rabs x : 
    IsNN (Rabs x).
Proof.
  intros n. simpl. rewrite Qmax_eq_Qabs_self.
  stepl 0. 2:{ unfold Qle; simpl; lia. }
  apply Qabs_nonneg.
Defined.

(* (2.9) Proposition. (d) *)
Proposition Rmax_of_IsNN x y (HNNx : IsNN x) : 
    IsNN (Rmax x y)%R.
Proof.
  intros n. simpl.
  apply (Qle_trans _ (seq x n)).
  - exact (HNNx n).
  - apply Q.le_max_l.
Defined.

Proposition Rmax_of_IsPos x y (HPosx : IsPos x) : 
    IsPos (Rmax x y)%R.
Proof.
  destruct HPosx as [n Hn].
  exists n. simpl.
  apply (Qlt_le_trans _ (seq x n)).
  - exact Hn.
  - apply Q.le_max_l.
Defined.

(* AI suggested *)
Lemma seq_lower_bound (x : R) (n m : positive) :
    seq x n - (1 # n) - (1 # m) <= seq x m.
Proof.
  ltac1:(pose proof (reg x n m) as H).
  apply Qabs_Qle_condition in H as [H1 _].
  lra.
Defined.

(* (2.9) Proposition. (e) *)
Proposition Rmin_of_IsPos x y (HPosx : IsPos x) (HPosy : IsPos y) : 
    IsPos (Rmin x y)%R.
Proof.
  destruct HPosx as [n Hn].
  destruct HPosy as [m Hm].
  assert (Hd : 0 < Qmin (seq x n - (1 # n)) (seq y m - (1 # m))).
  { apply Q.min_glb_lt; lra. }
  assert (∀q, 0 < q -> { k : positive | (2 # k) < q }).
  { intros. exists (3 * Qden q)%positive.
    apply Qlt_le_trans with (1 # Qden q).
    - unfold Qlt; simpl; lia.
    - unfold Qle; unfold Qlt in H; simpl in *; nia. }
  destruct (H _ Hd) as [k Hk].
  ltac1:(pose proof (Qhalves k) as Hh).
  ltac1:(pose proof (Q.le_min_l (seq x n - (1 # n)) (seq y m - (1 # m))) as Hlx).
  ltac1:(pose proof (Q.le_min_r (seq x n - (1 # n)) (seq y m - (1 # m))) as Hly).
  exists k. simpl.
  rewrite Qmin_eq_neg_Qmax.
  apply Q.min_glb_lt.
  - apply Qlt_le_trans with (seq x n - (1 # n) - (1 # k)).
    + lra.
    + rewrite Qopp_opp. apply seq_lower_bound.
  - apply Qlt_le_trans with (seq y m - (1 # m) - (1 # k)).
    + lra.
    + rewrite Qopp_opp. apply seq_lower_bound.
Defined.

Proposition Rmin_of_IsNN x y (HNNx : IsNN x) (HNNy : IsNN y) : 
    IsNN (Rmin x y)%R.
Proof.
  intros n. simpl.
  rewrite Qmin_eq_neg_Qmax.
  apply Q.min_glb.
  - rewrite Qopp_opp. exact (HNNx n).
  - rewrite Qopp_opp. exact (HNNy n).
Defined.

(* (2.10) Definition. *)
Definition Rle (x y : R) := IsNN (y - x)%R.
Definition Rlt (x y : R) := IsPos (y - x)%R.
Abbreviation Rgt a b := (Rlt b a) (only parsing).
Abbreviation Rge a b := (Rle b a) (only parsing).

Infix "<" := Rlt : R_scope.
Infix "<=" := Rle : R_scope.
Notation "x > y" := (Rlt y x)(only parsing) : R_scope.
Notation "x >= y" := (Rle y x)(only parsing) : R_scope.
Notation "x <= y <= z" := (x<=y/\y<=z) : R_scope.
Notation "x <= y < z" := (x<=y/\y<z) : R_scope.
Notation "x < y <= z" := (x<y/\y<=z) : R_scope.
Notation "x < y < z" := (x<y/\y<z) : R_scope.
Definition IsNeg x := (x < of_Q 0)%R.

(* A beautiful excerpt of the book: *)
(* If x < y or x = y, then x ~ y. The converse is not valid: as we shall
see later, it is possible that we have x ~ y without being able to prove
that x < y or x = y. For this reason it was necessary to define the
relations < and ~ independently of each other. *)

(* Morphisms suggested by AI *)
#[global]
Add Parametric Morphism : IsNN
  with signature (Req ==> iff) as IsNN_mor.
Proof. intros a b Hab.  constructor. apply Req_IsNN_iff. easy. apply Req_IsNN_iff. easy. Defined.

#[global]
Add Parametric Morphism : Rle
  with signature (Req ==> Req ==> iff) as Rle_mor.
Proof.
  intros a b Hab c d Hcd. unfold Rle.
  constructor.
  apply Req_IsNN_iff. unfold Rminus. rewrite Hab, Hcd. reflexivity.
  apply Req_IsNN_iff. unfold Rminus. rewrite Hab, Hcd. reflexivity.
Defined.

#[global]
Instance IsPos_mor : Proper (Req ==> iffT) IsPos.
Proof.
  intros x y Hxy. split; intro H.
  - apply (IsPos_of_Req x y); assumption.
  - apply (IsPos_of_Req y x). symmetry. assumption. exact H.
Defined.

(* You need to do it also for crelation :|, I don't understand any of this but anyways *)
#[global] Instance Req_CEquivalence : CRelationClasses.Equivalence Req.
Proof. split. exact Req_refl. exact Req_sym. exact Req_trans. Defined.

#[global] Instance Rplus_CProper :
CMorphisms.Proper (CMorphisms.respectful Req (CMorphisms.respectful Req Req)) Rplus.
Proof. intros a b Hab c d Hcd. rewrite Hcd,Hab. reflexivity. Defined.

#[global] Instance Ropp_CProper :
CMorphisms.Proper (CMorphisms.respectful Req Req) Ropp.
Proof. intros a b Hab. rewrite Hab. reflexivity. Defined.

#[global]
Instance Rlt_mor : Proper (Req ==> Req ==> iffT) Rlt.
Proof.
  intros a b Hab c d Hcd. unfold Rlt.
  constructor.
  intros. unfold Rminus. rewrite <-Hcd,<-Hab.
  exact H.
  intros. unfold Rminus. rewrite Hcd,Hab.
  exact H.
Defined.

(* (2.11) Proposition. (a) *)
Proposition Rle_lt_trans x y z : (x <= y -> y < z -> x < z)%R.
Proof.
  intros Hxy Hyz. unfold Rlt, Rle in *.
  refine (fst (Req_IsPos_iff ((z - y) + (y - x))%R (z - x)%R _) _).
  - ring.
  - apply Rplus_of_IsPos_IsNN.
    + exact Hyz.
    + exact Hxy.
Defined.

Proposition Rlt_le_trans x y z : (x < y -> y <= z -> x < z)%R.
Proof.
  unfold Rle,Rlt.
  intros Hxy Hyz.
  apply IsPos_of_Req with (x := ((y - x) + (z - y))%R).
  - ring.
  - apply Rplus_of_IsPos_IsNN.
    + exact Hxy.
    + exact Hyz.
Defined.

(* (2.11) Proposition. (b) *)
Proposition Rle_le_trans x y z : (x <= y -> y <= z -> x <= z)%R.
Proof.
  intros Hxy Hyz.
  apply IsNN_of_Req with (x := ((z - y) + (y - x))%R).
  - ring.
  - apply Rplus_of_IsNN.
    + exact Hyz.
    + exact Hxy.
Defined.

(* (2.11) Proposition. (c) *)
Proposition Rplus_le_compat x y z t : (x <= z -> y <= t -> x + y <= z + t)%R.
Proof.
  intros Hxz Hyt.
  unfold Rle in *.
  assert (H : ((z + t) - (x + y) ≖ (z - x) + (t - y))%R) by ring.
  apply (Req_IsNN_iff _ _ H).
  apply Rplus_of_IsNN.
  - exact Hxz.
  - exact Hyt.
Defined.

(* (2.11) Proposition. (d) *)
Proposition Rplus_lt_compat x y z t : (x <= z -> y < t -> x + y < z + t)%R.
Proof.
  intros Hxz Hyt.
  unfold Rlt in *. unfold Rle in Hxz.
  assert (H : ((z + t) - (x + y) ≖ (t - y) + (z - x))%R) by ring.
  apply (Req_IsPos_iff _ _ H).
  apply Rplus_of_IsPos_IsNN.
  - exact Hyt.
  - exact Hxz.
Defined.

(* (2.11) Proposition. (e) *)
Proposition Rmult_le_compat_r x y z : (of_Q 0 <= y -> x <= z -> x * y <= z * y)%R.
Proof.
  intros Hy Hxz.
  unfold Rle in *.
  apply IsNN_of_Req with (x := ((z - x) * y)%R).
  - ring.
  - apply Rmult_of_IsNN.
    + exact Hxz.
    + apply IsNN_of_Req with (x := (y - of_Q 0)%R).
      * ring.
      * exact Hy.
Defined.

(* (2.11) Proposition. (f) *)
Proposition Rmult_lt_compat_r x y z : (of_Q 0 < y -> x < z -> x * y < z * y)%R.
Proof.
  intros Hy Hxz.
  unfold Rlt in *.
  apply IsPos_of_Req with (x := ((z - x) * y)%R).
  - ring.
  - apply Rmult_of_IsPos.
    + exact Hxz.
    + apply IsPos_of_Req with (x := (y - of_Q 0)%R).
      * ring.
      * exact Hy.
Defined.

(* (2.11) Proposition. (g) *)
Proposition Ropp_lt_compat x y : (x < y -> - y < - x)%R.
Proof.
  intros Hxy.
    unfold Rlt in *.
    apply IsPos_of_Req with (x := (y - x)%R).
    - ring.
    - exact Hxy.
Defined.

(* (2.11) Proposition. (h) *)
Proposition Ropp_le_compat x y : (x <= y -> - y <= - x)%R.
Proof.
  intros H.
  unfold Rle in *.
  apply (IsNN_of_Req (y - x)%R).
  1:{ ring. }
  exact H.
Defined.
  
(* (2.11) Proposition. (i) *)
Proposition le_max_l x y : (x <= Rmax x y)%R.
Proof.
  unfold Rle, IsNN.
  intros n. 
  simpl.
  assert (Hmax := Q.le_max_l (seq x (2 * n)) (seq y (2 * n))).
  assert (Hneg : -1 # n <= 0) by (unfold Qle; simpl; lia).
  change (n~0)%positive with (2 * n)%positive.
  lra.
Defined.

(* (2.11) Proposition. (j) *)
Proposition le_min_l x y : (Rmin x y <= x)%R.
Proof.
  unfold Rle, IsNN.
  intros n. 
  simpl.
  assert (Hmin := Q.le_min_l (seq x (2 * n)) (seq y (2 * n))).
  assert (Hneg : -1 # n <= 0) by (unfold Qle; simpl; lia).
  change (n~0)%positive with (2 * n)%positive.
  rewrite Qmin_eq_neg_Qmax.
  rewrite Qopp_opp,Qopp_opp.
  lra.
Defined.

(* (2.11) Proposition. (k) *)
Proposition le_antisym x y : (x <= y -> y <= x -> x ≖ y)%R.
Proof.
  (* Gemini Pro 3.1 *)
  intros Hxy Hyx n.
  (* We use your provided lemma to show that bounding by an arbitrarily small positive rational implies the tight bound *)
  apply (forall_Qplus_inv (2 # n) _ 2).
  intros p.
  assert (Hx := reg x (2 * p) n).
  assert (Hy := reg y n (2 * p)).
  assert (H1 := Hxy p).
  assert (H2 := Hyx p).
  simpl in H1, H2.
  
  (* We decompose the difference to apply the triangle inequality *)
  assert (H_eq : seq x n - seq y n == (seq x n - seq x (2 * p)) + (seq x (2 * p) - seq y (2 * p)) + (seq y (2 * p) - seq y n)) by ring.
  rewrite H_eq.
  eapply Qle_trans. apply Qabs_triangle_3.
  
  (* Extracting the middle term bound using lra *)
  assert (H_mid : Qabs (seq x (2 * p) - seq y (2 * p)) <= 1 # p).
  { (* Human *)
    change (p~0)%positive with (2 * p)%positive in H1,H2.
    apply Qabs_Qle_condition.
    assert (H_opp : -1 # p == - (1 # p)) by (unfold Qeq; simpl; lia).
    rewrite H_opp in H1.
    lra.
  }
  (* Helper equations to assist lra with Qmake fractions *)
  assert (H2p : (1 # p) + (1 # p) == 2 # p) by (unfold Qeq; simpl; lia).
  assert (H2n : (1 # n) + (1 # n) == 2 # n) by (unfold Qeq; simpl; lia).
  assert (Hp_half : (1 # (2 * p)) + (1 # (2 * p)) == 1 # p) by (unfold Qeq; simpl; lia).
  
  (* lra closes the remaining bounds sum perfectly *)
  lra.
Defined.

(* (2.11) Proposition. (l) *)
Proposition Rabs_nonneg x: (of_Q 0 <= Rabs x)%R.
Proof.
  unfold Rle, IsNN.
  intros n.
  simpl.
  (* seq of Rabs evaluates to Qmax, which is equal to Qabs. lra takes it from there. *)
  assert (H_max := Qmax_eq_Qabs_self (seq x (2 * n))).
  assert (H_abs : 0 <= Qabs (seq x (2 * n))) by apply Qabs_nonneg.
  assert (H_neg : -1 # n <= 0) by (unfold Qle; simpl; lia).
  change (n~0)%positive with (2 * n)%positive.
  lra.
Defined.

(* (2.11) Proposition. (m) *)
Proposition Rabs_triangle x y: (Rabs (x + y) <= Rabs x + Rabs y)%R.
Proof.
  unfold Rle, IsNN.
  intros n.
  simpl.
  (* Expose the Qabs equivalence for all three components generated by the Rplus and Rabs definitions *)
  assert (H_maxx := Qmax_eq_Qabs_self (seq x (2 * (2 * n)))).
  assert (H_maxy := Qmax_eq_Qabs_self (seq y (2 * (2 * n)))).
  assert (H_maxxy := Qmax_eq_Qabs_self (seq x (2 * (2 * n)) + seq y (2 * (2 * n)))).
  
  (* Import standard rational triangle inequality constraint *)
  assert (H_tri := Qabs_triangle (seq x (2 * (2 * n))) (seq y (2 * (2 * n)))).
  assert (H_neg : -1 # n <= 0) by (unfold Qle; simpl; lia).
  
  (* Feed properties directly to the linear solver *)
  change (n~0~0)%positive with (2 * (2 * n))%positive.
  lra.
Defined.

(* (2.12) Definition. *)
Definition RNeq x y := (sum (x<y) (y<x))%R. (* sum means or  *)

(* 
(* TODO Extra *)
Lemma RNeq_not_Req_iff x y : RNeq x y <=> not (x ≖ y).
 *)

Lemma Rmax_comm x y : (Rmax x y) ≖ (Rmax y x).
Proof.
  intro n. simpl head seq.
  rewrite (Q.max_comm (seq y n) (seq x n)).
  rewrite Qeq_cancel_r.
  easy.
Defined.

(* (2.13) Proposition.  *)
(* We shall break this into 9 sub parts *)
(* part 1 *)
Proposition Rinv_exists x (Hnz : RNeq x (of_Q 0)): 
  {M | ∀m, (M <= m)%positive -> (1 # M) <= (Qabs (seq x m))}.
Proof.
  (* First, show that Rabs x is positive *)
  assert (IsPos (Rabs x)) as HPos.
  {
    destruct Hnz as [Hlt | Hgt].
    - (* Case: x < 0, then |x| = -x > 0 *)
      unfold Rabs.
      rewrite Rmax_comm.
      apply Rmax_of_IsPos.
      apply Ropp_lt_compat in Hlt.
      assert (of_Q 0 ≖ - of_Q 0)%R.
      { rewrite <- (of_Q_Ropp 0). easy. }
      rewrite <-H in Hlt.
      unfold Rlt in Hlt.
      assert (-x ≖ - x - of_Q 0 )%R by ring.
      rewrite H0. exact Hlt.
    - (* Case: 0 < x, then |x| = x > 0 *)
      unfold Rabs.
      apply Rmax_of_IsPos.
      unfold Rlt in Hgt.
      assert (x ≖ x - of_Q 0)%R by ring.
      rewrite H. exact Hgt.
  }
  
  (* Use IsPos_iff to extract the witness N *)
  apply IsPos_iff in HPos.
  destruct HPos as [M HM].
  
  (* N is our desired M *)
  exists M.
  intros m Hm.
  specialize (HM m Hm).
  
  (* Now relate seq (Rabs x) m to Qabs (seq x m) *)
  unfold Rabs in HM.
  simpl in HM.
  simpl in HM.
  rewrite Qmax_eq_Qabs_self in HM.
  exact HM.
Defined.

(* AI suggested for a shorter proof *)
(* Shared core: if both seq x a and seq x b have |·| >= 1#M,
   then |/seq x a - /seq x b| <= (1#m) + (1#n)
   provided |(seq x a - seq x b)| <= (1#a) + (1#b) and
   (1#a)+(1#b) <= (1#m)+(1#n) after dividing by (1#M)^2 *)
Lemma Rinv_reg_aux (x : R) (M a b : positive) (m n : positive)
    (Hba : (1#M) <= Qabs (seq x a))
    (Hbb : (1#M) <= Qabs (seq x b))
    (Hreg : Qabs (seq x a - seq x b) <= (1#a) + (1#b))
    (Hfin : ((1#a) + (1#b)) / ((1#M)*(1#M)) <= (1#m) + (1#n)) :
    Qabs (/ seq x a - / seq x b) <= (1#m) + (1#n).
Proof.
  assert (Qabs 0 == 0) as Qabs_0 by easy.
  assert (Hnza : ~ seq x a == 0).
  { intro E; rewrite E, Qabs_0 in Hba.
    refine (Qlt_irrefl 0 (Qlt_le_trans _ _ _ _ Hba)).
    easy. }
  assert (Hnzb : ~ seq x b == 0).
  { intro E; rewrite E, Qabs_0 in Hbb.
    refine (Qlt_irrefl 0 (Qlt_le_trans _ _ _ _ Hbb)). easy. }
  rewrite (Qinv_diff_bound _ _ Hnza Hnzb).
  apply Qle_trans with (((1#a)+(1#b)) / ((1#M)*(1#M)))> [|exact Hfin].
  ltac1:(setoid_replace
    (Qabs (seq x a - seq x b) * Qabs (/seq x a) * Qabs (/seq x b))
    with (Qabs (seq x a - seq x b) / (Qabs (seq x a) * Qabs (seq x b)))
    ).
  + apply Qdiv_le_compat.
  - apply Qabs_nonneg.
  - exact Hreg.
  - reflexivity.
  - apply Qle_trans with (Qabs (seq x a) * (1#M)).
    ++ apply Qmult_le_compat_r> [exact Hba | apply Qlt_le_weak; reflexivity].
    ++ rewrite (Qmult_comm _ (1#M)), (Qmult_comm _ (Qabs (seq x b))).
      apply Qmult_le_compat_r> [exact Hbb | apply Qabs_nonneg].
  + rewrite !Qabs_Qinv; field; split. 
    apply Qabs_nonzero. assumption.
    apply Qabs_nonzero. assumption.
Defined.

Structure RNZ : Set := RNZmake {
    rnz_r : R;
    rnz_hnz : RNeq rnz_r (of_Q 0)
  }.

(* part 2 *)
#[refine] Definition RNZinv (r : RNZ) : RNZ :=
 let x := (rnz_r r) in 
 let M := proj1_sig (Rinv_exists x (rnz_hnz r)) in 
 {| rnz_r := {| seq := (
                fun n => 
                  if (n <? M)%positive then Qinv (seq x (M^3))
                  else Qinv (seq x (n*M^2)%positive)
              ) |};
    rnz_hnz := _
 |}.
Proof.
  (* First let's prove the non zero *)
  2:{ 
    destruct (rnz_hnz r).
    + left. admit.
    + right. admit.
  }
  (* simplified with Fable 5 *)
  intros m n.
  ltac1:(pose proof (proj2_sig (Rinv_exists x (rnz_hnz r))) as HM). simpl in HM.
  destruct (m <? M)%positive eqn:Hm; destruct (n <? M)%positive eqn:Hn.
  - rewrite Qeq_cancel_r. easy.
  - (* m < M, n >= M: left=M^3, right=n*M^2 *)
    assert (HMm : (m <= M)%positive) by (apply Pos.ltb_lt in Hm; lia).
    assert (HMn : (M <= n)%positive) by (apply Pos.ltb_ge; exact Hn).
    apply (Rinv_reg_aux x M (n*M^2) (M^3) n m).
    + apply HM; nia.
    + apply HM; nia.
    + apply reg.
    + assert ((1#M)*(1#M) == (1#(M^2)%positive)) by (unfold Qeq; simpl; lia).
      apply Qle_trans with ((1#M) + (1#n)).
      * apply Qle_lteq; right. rewrite H. ltac1:(field_simplify). unfold Qeq; simpl; lia.
        unfold Qeq; simpl; lia.
      * rewrite Qplus_comm. apply Qplus_le_r. unfold Qle; simpl; nia.
  - (* m >= M, n < M: left=m*M^2, right=M^3 *)
    assert (HMn : (n <= M)%positive) by (apply Pos.ltb_lt in Hn; lia).
    assert (HMm : (M <= m)%positive) by (apply Pos.ltb_ge; exact Hm).
    apply (Rinv_reg_aux x M (M^3) (m*M^2) n m).
    + apply HM; nia.
    + apply HM; nia.
    + rewrite Qabs_Qminus. rewrite Qplus_comm. apply reg.
    + assert ((1#M)*(1#M) == (1#(M^2)%positive)) by (unfold Qeq; simpl; lia).
      apply Qle_trans with ((1#M) + (1#m)).
      * apply Qle_lteq; right. rewrite H. ltac1:(field_simplify). unfold Qeq; simpl; lia.  unfold Qeq; simpl; lia.
      * apply Qplus_le_l. unfold Qle; simpl; nia.
  - (* m >= M, n >= M: left=m*M^2, right=n*M^2 *)
    assert (HMm : (M <= m)%positive) by (apply Pos.ltb_ge; exact Hm).
    assert (HMn : (M <= n)%positive) by (apply Pos.ltb_ge; exact Hn).
    apply (Rinv_reg_aux x M (n*M^2) (m*M^2) n m).
    + apply HM; nia.
    + apply HM; nia.
    + apply reg.
    + assert ((1#M)*(1#M) == (1#(M^2)%positive)) by (unfold Qeq; simpl; lia).
      apply Qle_trans with ((1#m) + (1#n)).
      * apply Qle_lteq; right. rewrite H. ltac1:(field_simplify). unfold Qeq; simpl; lia. unfold Qeq; simpl; lia.
      * proveeq. lra.
Admitted.

(* part 3 *)
Proposition Rinv_IsPos (x : RNZ) :
  IsPos (rnz_r x) <=> IsPos (rnz_r (RNZinv x)).
Proof.
Admitted.

(* part 4 *)
Proposition Rinv_IsNeg (x : RNZ):
  IsNeg (rnz_r x) <=> IsNeg (rnz_r (RNZinv x)).
Proof.
Admitted.

(* part 5 *)
(* Proposition Rmult_inv_r (x : R) (Hnz : RNeq x (of_Q 0)) :
  (x * (Rinv x Hnz) ≖ of_Q 1)%R.
Proof.
Admitted. *)

(* part 6 *)
(* Proposition Rinv_unique (x t : R) (Hnz : RNeq x (of_Q 0)) :
  (x * t ≖ of_Q 1)%R -> t ≖ (Rinv x Hnz).
Proof.
Admitted. *)

(* Lemma Rmult_Neq_zero x y (Hxnz : RNeq x (of_Q 0)) (Hynz : RNeq y (of_Q 0)):
  RNeq (x*y)%R (of_Q 0).
Proof.
Admitted. *)

(* part 7 *)
(* Proposition Rinv_mult x y (Hxnz : RNeq x (of_Q 0)) (Hynz : RNeq y (of_Q 0)) :
  (Rinv (x*y) (Rmult_Neq_zero x y )) ≖ (Rinv x Hnz).
Proof.
Admitted. *)

(* part 8 *)

(* part 9 *)

(* TODO
Add autocast feature
Make sum of RNZ and R easier
write all spec for (2.13) Proposition. 
prove them all 
*)

End R.

