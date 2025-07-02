From Ltac2 Require Import Ltac2 List String Ltac1 Rewrite.
From Ltac2 Require Import Constr Option Pattern Printf Bool.

From Stdlib Require Import Unicode.Utf8 Lia Lra.
From Stdlib Require Import QArith Psatz Qabs.

Ltac2 Notation "ring" := ltac1:(ring).
Ltac2 Notation "field" := ltac1:(field).
Ltac2 Notation "easy" := ltac1:(easy).
Ltac2 Notation "lra" := ltac1:(lra).
Ltac2 Notation "nra" := ltac1:(nra).
Ltac2 Notation "lia" := ltac1:(lia).
Ltac2 Notation "nia" := ltac1:(nia).
Ltac2 Notation "stepl" c(constr) := ltac1:(c|-stepl c) (Ltac1.of_constr c).
Ltac2 Notation "stepr" c(constr) := ltac1:(c|-stepr c) (Ltac1.of_constr c).
Ltac2 Notation "refine" c(thunk(open_constr)) := Control.refine c.

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

Declare Left  Step Z.lt_stepl.
Declare Right Step Z.lt_stepr.
Declare Left  Step Z.le_stepl.
Declare Right Step Z.le_stepr.

Module Pos.
Lemma le_stepl x y z : (x <= y -> z <= x -> z <= y)%positive.
Proof.
  intros. lia. 
Qed.
End Pos.

Declare Left Step Pos.le_stepl.
Declare Right Step POrderedType.Positive_as_DT.le_trans.

(* inject_P *)
Definition inject_P p := inject_Z (Zpos p).

(** injection from Pos is injective. *)

Lemma inject_P_injective (a b: positive): inject_P a == inject_P b <-> a = b.
Proof.
 unfold Qeq. simpl. rewrite (Pos2Z.inj_iff (a*1) (b*1)). rewrite !Pos.mul_1_r; reflexivity.
Qed.

Lemma Posle_Qle x y: (x <= y)%positive = (inject_P x <= inject_P y).
Proof.
 unfold Qle. simpl. now rewrite !Pos.mul_1_r.
Qed.

Lemma Poslt_Qlt x y: (x < y)%positive = (inject_P x < inject_P y).
Proof.
 unfold Qlt. simpl. now rewrite !Pos.mul_1_r.
Qed.

Lemma inject_P_pos x : 0 < inject_P x.
Proof.
  stepl (inject_Z 0). unfold inject_P. rewrite <-Zlt_Qlt. lia.
  (rewrite Qminmax.Q.OT.le_lteq). right. easy.
Qed.

(* Zle and Posle *)

Lemma Zle_Posle x y : (0 < x)%Z -> (0 < y)%Z -> (x <= y)%Z = (Z.to_pos x <= Z.to_pos y)%positive.
Proof.
  destruct x,y.
  all : easy.
Qed.

(* New tactics! *)

(* proveeq tries to change the current goal into _ = _ *)
Ltac2 Notation "proveeq"  := 
  let dir := (fun _ => right) in 
  match! goal with
  | [|- _ <= _] => (rewrite Qminmax.Q.OT.le_lteq);dir ()
  | [|- (_ <= _)%Z] => (rewrite Z.le_lteq);dir ()
  | [|- (_ <= _)%positive] => (rewrite POrderedType.Positive_as_OT.le_lteq);dir ()
  end.

(* provelt tries to change the current goal into _ < _ *)
Ltac2 Notation "provelt"  := 
  let dir := (fun _ => left) in 
  match! goal with
  | [|- (_ <= _)] => (rewrite Qminmax.Q.OT.le_lteq);dir ()
  | [|- (_ <= _)%Z] => (rewrite Z.le_lteq);dir ()
  | [|- (_ <= _)%positive] => (rewrite POrderedType.Positive_as_OT.le_lteq);dir ()
  end.

Ltac2 rec get_last_digit (n : int) :=
  match Int.ge n 0 with  
  | true =>
    match (Int.mod n 10) with
    | 0 => "0"
    | 1 => "1"
    | 2 => "2"
    | 3 => "3"
    | 4 => "4"
    | 5 => "5"
    | 6 => "6"
    | 7 => "7"
    | 8 => "8"
    | _ => "9"
    end
  | false => get_last_digit (Int.abs n)
  end.

Ltac2 rec of_int (n : int) :=
  match Int.gt n 0 with
  | true => 
    match Int.ge n 10 with
    | true => app (of_int (Int.div n 10)) (get_last_digit n)
    | false => (get_last_digit n)
    end
  | false => 
    match Int.equal n 0 with
    | true => "0"
    | false => app "-" (of_int (Int.abs n))
    end
  end.

Module Message.
Ltac2 of_bool (b : bool) := 
  match b with
  | true => Message.of_string "true"
  | false => Message.of_string "true"
  end.
End Message.

Ltac2 constr_to_string (c : constr) :=
  (Message.to_string (Message.of_constr c)).

(* This function is similar to Pattern.matches_vect*)
Module Constr.
Ltac2 rec matches_list (c : constr list) (ce : constr list) :=
  match (c,ce) with
  | ([],[]) => []
  | (chd :: ctl,cehd :: cetl) => 
  let (x,clist,celist) := if is_evar cehd then ([(chd,cehd)],[],[])
  else 
    let (chdl,chdr) := decompose_app_list chd in
    let (cehdl,cehdr) := decompose_app_list cehd in
    if is_evar cehdl then ([(chdl,cehdl)],chdr,cehdr)
    else 
    if (Constr.equal chdl cehdl) then 
      ([],chdr,cehdr)
    else
      Control.throw Match_failure
  in
    List.append x (matches_list (List.append clist ctl) (List.append celist cetl))
  | _ => Control.throw Match_failure
  end.
End Constr.

Ltac2 Notation "nameit" p(thunk(pose)) s(opt(ident)) cl(opt(clause)) :=
  Std.set false p (default_on_concl cl);
  let (idnt,cnstr,_) := List.last (Control.hyps ()) in
  let c1 := (Option.get cnstr) in
  let c2 := (snd (p ())) in
  let l := (List.map (fun (x,_) => constr_to_string x) (filter (fun (_,y) => neg (String.equal (sub (constr_to_string y) 1 1) "i")) (Constr.matches_list [c1] [c2]))) in
  let begin := match s with | Some i => (Ident.to_string i) | None => "" end in
  let st := (String.app begin (String.concat "" l)) in
  printf "Trying the name %s" st;
   match (Ident.of_string st) with
  | Some i => Std.rename [(idnt,i)]
  | None => ()
  end; Std.unify c1 c2. (* Will remove those unwanted goals produced in shelve somehow! *)

(* Test nameit *)
Local Lemma test_nameit (a b c d:Q) (f:Q->Q->Q->Q) (bad_name : Q): f a 1 bad_name + f 1 b bad_name = a -> f c d bad_name = f (d+1) a bad_name.
  do 4 (nameit (f _ _ bad_name) f).
Abort.

Lemma Qle_Qplus_mid a b c d e f (h : a + c <= d + f) (Hbe : b <= e) : a + b + c <= d + e + f.
Proof.
  lra.
Qed.

Lemma Qle_Qmult_mid a b c d e f (h : 0 <= a * c <= d * f) (Hbe : 0 <= b <= e) : a * b * c <= d * e * f.
Proof.
  assert _ by exact (Qmult_le_compat_nonneg _ _ _ _ h Hbe).
  lra.
Qed.

(* Maybe I could use matches_list instead of sep_constr! *)
Ltac2 rec sep_constr (clist : constr list) (sep : constr) :=
  match clist with
  | [] => []
  | c :: crest => 
  let (cl,cr) := decompose_app_list c in
  if Constr.equal cl sep then
    List.append (sep_constr cr sep) (sep_constr crest sep)
  else 
    c :: (sep_constr crest sep)
  end.

(* sep must be a binary operator *)
Ltac2 rec join_constr (clist : constr list) (sep : constr) :=
  match clist with
  | [] => None
  | [c] => Some c
  | c :: crest => let r := Option.get (join_constr crest sep) in
   Some '($sep $c $r)
  end.

Ltac2 rec partition_index (l : 'a list) (ind : int list) (s : int) : 'a list * 'a list :=
  if (List.is_empty ind) then
    ([],l)
  else
    match l with
    | [] => ([], [])
    | x :: tl
      => match Int.equal (List.hd ind) s with
         | true => 
            let (g, d) := partition_index tl (List.tl ind) (Int.add s 1) in
            ((x::g), d)
         | false => 
           let (g, d) := partition_index tl ind (Int.add s 1) in
           (g, (x::d))
         end
    end.

Ltac2 Eval partition_index ["one";"two";"three";"four";"five"] [1] 1.

Ltac2 Eval sep_constr ['(1+(1*4+(2313+2^3)))] 'Qplus.
Ltac2 Eval sep_constr ['(-1-(1*4+(2313+2^3)))] 'Qplus.
Ltac2 Eval join_constr (sep_constr ['(-1+(1*4+(2313+2^3)))] 'Qplus) 'Qplus.

(* TODO : This tactic is a little slow. *)
Ltac2 pickaxe (ll : int list) (rl : int list) :=
  try (unfold Qminus);try (unfold Qminus);
  (* List start with 1 *)
  let st := 1 in
  let (sep,zero) := match! goal with 
  | [|- _ (_ + _) (_ + _)] => ('Qplus,'(0))
  | [|- _ (_ * _) (_ * _)] => ('Qmult,'(1))
  | [|- _ (_ * _) _] => ('Qmult,'(1))
  | [|- _ _ (_ * _)] => ('Qmult,'(1))
  | [|- _] => Control.throw Match_failure
  end in 
  let (lc,rc) := match! goal with 
  | [|- _ ?l ?r] => (l,r)
  | [|- _] => Control.throw Match_failure
  end in 
  let lls := sep_constr [lc] sep in
  let (lll,llr) := partition_index lls ll st in
  let rls := sep_constr [rc] sep in
  let (rll,rlr) := partition_index rls rl st in
  let (lsl,lsr) := (default zero (join_constr lll sep),default zero (join_constr llr sep)) in    
  let left_side := '($sep $lsl $lsr) in
  let (rsl,rsr) := (default zero (join_constr rll sep),default zero (join_constr rlr sep)) in 
  let right_side := '($sep $rsl $rsr) in
  (* printf "%t <= %t" left_side right_side; *)
  ltac1:(rc right_side|- assert (rc == right_side) as internalH_for_pickaxe_r by (ring)) (Ltac1.of_constr rc) (Ltac1.of_constr right_side);
  try (rewrite &internalH_for_pickaxe_r);
  ltac1:(lc left_side|- assert (lc == left_side) as internalH_for_pickaxe_l by (ring)) (Ltac1.of_constr lc) (Ltac1.of_constr left_side);
  try (rewrite &internalH_for_pickaxe_l);
  Std.clear [@internalH_for_pickaxe_l;@internalH_for_pickaxe_r]; 
  match! goal with
  | [|- (_ + _) <= (_ + _)] => refine (Qplus_le_compat $lsl $rsl $lsr $rsr _ _); try (proveeq; ring)
  | [|- (_ * _) <= (_ * _)] =>
  refine (Qmult_le_compat_nonneg $lsl $rsl $lsr $rsr _ _);
  constructor; try (apply Qabs_nonneg); try (provelt;apply inject_P_pos);
  try (proveeq; ring)
  | [|- _] => Control.throw Match_failure
  end.

Local Lemma pickaxe_test (a b c d e f : Q) (p : positive) :  Qabs b * inject_P p <= (d - f) * (e * a).
Proof.
  time (pickaxe [1] [2]).
Abort.

Local Lemma pickaxe_test (a b c d e f : Q) :  b + c <= (d - f) + (e + a).
Proof.
  time (pickaxe [1;2] [1;2;4]).
Abort.


