From PA Require Import ProgramAlgebra.
Import ProgramAlgebra.
Import Nat.
Import List.
Require Import String.
Import ListNotations.
Require Import FunctionalExtensionality.

Open Scope alg_scope.

Print Visibility.

Record MyVar := mkVar {
  id: string;
  val : nat;
}.

Definition eqbVar (x y : MyVar) := 
  andb (eqb x.(id) y.(id)) (PeanoNat.Nat.eqb x.(val) y.(val)).

Lemma eqbVar_sym : forall x y, eqbVar x y = eqbVar y x.
Proof. intros. unfold eqbVar. destruct x. destruct y. simpl.
  assert ((id0 =? id1) % string = (id1 =? id0) %string) by apply eqb_sym.
  assert ((val0 =? val1) = (val1 =? val0)) by apply PeanoNat.Nat.eqb_sym.
  rewrite H. rewrite H0. auto. Qed.

Lemma eqbVar_refl : forall x, eqbVar x x = true. 
Proof. intros. unfold eqbVar. destruct x. simpl. 
  apply Bool.andb_true_iff. split.
  apply eqb_refl. apply PeanoNat.Nat.eqb_refl.
Qed.

Variable GLOBVARS : list MyVar.

Definition Constraint : Prop := exists a b, GLOBVARS = [a;b] /\
  eqbVar a b = false.

Definition UNDEF := mkVar "Undefined" 0.

Instance myParams : UserParams :=
  Build_UserParams MyVar GLOBVARS eqbVar Constraint.

Definition hdeqz : Boolexp :=
 fun l =>
  match (hd_error l) with
  | None => false
  | Some x => x.(val) =? 0
  end.

Definition skip := @{ empty_assn }.

Definition GCDFunc (l : list Var)  : list Var := 
  let a := hd UNDEF l in let b := hd UNDEF (tl l) in
  [(mkVar a.(id) (b.(val) mod a.(val)));(mkVar b.(id) a.(val))].

Definition GCDAssn := @{ makeAssign GLOBVARS GCDFunc}.

Definition GCDStep (a : Alg) : Alg :=
  (skip <| hdeqz |> (GCDAssn ;; a)).

Definition GCDStr := Recur GCDStep (_|_).

Definition GCDRes := (_|_) <| (fun x => negb (orb (hdeqz x) (Assign_over_Boolexp hdeqz GCDAssn))) |>
 @{ GLOBVARS :== exp_Cond refl_exp GCDFunc hdeqz}.

Lemma GcdBase : FNFPres (_|_) (GCDStep (_|_)).
Proof.
  unfold FNFPres. exists (Normal (_|_)). exists (Normal (GCDStep (_|_))).
  split;split;try split;pauto. unfold Normal. simpl. unfold Refine.
  do 4 eexists. assert (forall x, @{x} = |-|[@{x}]) by auto.
  split;split;try split;auto. rewrite H. auto. unfold CH. intros.
  destruct H0;try contradiction. rewrite <- H0. eexists. split;pauto.
  pose (H (Assign_comb_CDC_help (extends_assign (extends_assign empty_assn))
  (extends_assign (Assign_comb_Seq_help (extends_assign (extends_assign (GLOBVARS :== GCDFunc)))
  (extends_assign empty_assn))) hdeqz)). rewrite e. auto. unfold CH. intros.
  destruct H0;try contradiction. rewrite <- H0. eexists. split;pauto.
  intros. right. auto.
Qed.

Hypothesis GcdStable : forall x, FNFPres (GCDStep x) (GCDStep (GCDStep x)).

(*  intros. unfold GCDStep. unfold FNFPres. assert (skip = |-|[skip]) by auto.
  assert (CH [@{ GLOBVARS :== GCDFunc}]). CH_check. destruct H0;try contradiction.
  rewrite <- H0. eexists;split;pauto. assert (CH [skip]). CH_check. unfold skip in *.
  destruct H1;try contradiction. rewrite <- H1. eexists;split;pauto. 
  destruct x.
  - destruct a.
    + pose (Chaos_zero_Seq_r GCDAssn).
      pose (rwt_comb _ _ _ _ (CDC hdeqz) (rwt_refl skip) r).
      pose (Cond_rev skip (_|_) hdeqz).
      pose (rwt_trans _ _ _ r0 r1). 
      do 2 eexists. split; split. 3 : split. apply r2.
      unfold FNF. rewrite H. do 2 eexists; split; pauto.
      unfold GCDAssn in r2. unfold GCDAssn.
      pose (Assign_to_NF GLOBVARS GCDFunc). rewrite H in r2.
      rewrite H. pose (rwt_comb _ _ _ _ Seq r3 r2).
      pose (NF_over_Seq [@{ GLOBVARS :== GCDFunc}] [skip] false_stat 
        (fun g => negb (hdeqz g))). apply r5 in H0 as H2;auto.
      pose (rwt_trans _ _ _ r4 H2). clear r5.
      pose (Seq_over_Choice [@{ GLOBVARS :== GCDFunc}] [skip]).
      apply r5 in H1 as H3;auto. clear r5.
      pose (rwt_comb _ _ _ _ (CDC (fun g : list Var =>
        (false_stat g || CH_over_Boolexp [@{ GLOBVARS :== GCDFunc}]
        (fun g0 : list Var => negb (hdeqz g0)))%bool)) (rwt_refl (_|_)) H3).
      pose (rwt_trans _ _ _ r6 r5).
      assert (|-| [skip] <--> (_|_) <| false_stat |> |-| [skip]).
      rewrite <- H. unfold skip. unfold empty_assn. 
      pose (Assign_to_NF GLOBVARS refl_exp). apply (rwt_trans _ _ _ r8).
      apply rwt_comb;pauto. pose (rwt_comb _ _ _ _ (CDC hdeqz) H4 r7).
      apply (rwt_trans _ _ _ r8). clear r8 r7 r6 r5 r4 r3 r2 r1 r0 r.
      clear H4 H3 H2. simpl. pose (NF_over_Cond [skip] [@{ GLOBVARS :== GCDFunc};; skip].
      CH_check. destruct H0;try contradiction. rewrite <- H0.
      unfold skip. eexists;split;pauto. 
*)

(*Proof.
  intros. unfold FNFPres. pose (FNF_closure x).
  pose (FNF_closure (GCDStep x)). destruct e. destruct e0.
  exists x0. exists x1. split;auto.
Qed.*)

Lemma GcdStrPres : AlgPres GCDStr.
Proof. apply AlgPresInd. apply GcdBase. apply GcdStable. Qed.

(* functions in this example are supposed to be already extended *)
Hypothesis no_extends : forall x:Exp, extends_mapping GLOBVARS x = x.

Lemma GcdReachRes : SthExists GCDRes GCDStr.
Proof. unfold SthExists. unfold GCDStr. do 2 apply Streams.Further.
apply Streams.Here. unfold Recur. unfold GCDStep. simpl.
unfold GCDRes. unfold SthStep. simpl. apply rwt_comm.
assert (GCDAssn ;; _|_ <--> _|_) by apply Chaos_zero_Seq_r.
apply (rwt_trans _ (skip <| hdeqz |> GCDAssn;; (skip <| hdeqz |> _|_))).
do 3 (apply rwt_comb;pauto). clear H.
apply (rwt_trans _ (Normal (skip <| hdeqz |> GCDAssn;; (skip <| hdeqz |> _|_)))).
apply NormalRWT. simpl. unfold extends_assign. simpl.
repeat rewrite (no_extends GCDFunc). repeat rewrite (no_extends refl_exp).
rewrite (no_extends (exp_Cond refl_exp refl_exp hdeqz)).
rewrite (no_extends (fun x0 : list MyVar => exp_Cond refl_exp refl_exp hdeqz (GCDFunc x0))).
unfold Assign_comb_CDC_help. simpl.
assert (exp_Cond refl_exp refl_exp hdeqz = refl_exp).
unfold exp_Cond. unfold refl_exp. apply functional_extensionality.
intros. destruct (hdeqz x);auto. rewrite H.
assert ((fun x0 => refl_exp (GCDFunc x0)) = GCDFunc).
unfold GCDFunc. unfold refl_exp. simpl. auto.
simpl in H0. rewrite H0. 
assert ((fun g =>
if hdeqz g then false_stat g
else CH_over_Boolexp [@{ GLOBVARS :== GCDFunc}] 
(fun g0 : list MyVar =>
    if hdeqz g0 then false_stat g0 else true_stat g0)) =
(fun x => negb (hdeqz x || hdeqz (GCDFunc GLOBVARS)))).
simpl. apply functional_extensionality. intros. destruct (hdeqz x).
simpl. auto. unfold CH_over_Boolexp. simpl. 
repeat rewrite (no_extends GCDFunc). destruct (hdeqz (GCDFunc GLOBVARS));auto.
simpl in H1. rewrite H1. pauto. Qed.

Definition falg := |-| [skip;GCDAssn] <| hdeqz |> (_|_).

Lemma refinegcd : exists r s, (r <--> falg /\ FNF r) /\ 
   (s <--> GCDRes /\ FNF s) /\ Refine r s.
Proof.
  exists ((_|_) <| fun g => negb (hdeqz g) |> |-| [skip;GCDAssn]).
  exists GCDRes. split;split.
  - unfold falg. apply rwt_comm. apply Cond_rev.
  - unfold FNF. do 2 eexists. split. auto. unfold CH. intros.
    destruct H. unfold skip in H. rewrite <- H. eexists;split;pauto.
    destruct H. unfold GCDAssn in H. rewrite <- H. eexists;split;pauto.
    destruct H.
  - split. apply rwt_refl. unfold FNF. unfold GCDRes. do 2 eexists.
    assert (@{ GLOBVARS :== exp_Cond refl_exp GCDFunc hdeqz} =
    |-| [@{ GLOBVARS :== exp_Cond refl_exp GCDFunc hdeqz}]) by auto.
    rewrite H. split;auto. unfold CH. intros. destruct H0. rewrite <- H0.
    eexists;split;pauto. destruct H0.
  - unfold GCDRes. unfold Refine. do 4 eexists. split. split;auto.
    unfold CH. intros.
    destruct H. unfold skip in H. rewrite <- H. eexists;split;pauto.
    destruct H. unfold GCDAssn in H. rewrite <- H. eexists;split;pauto.
    destruct H. split. assert (@{ GLOBVARS :== exp_Cond refl_exp GCDFunc hdeqz} =
    |-| [@{ GLOBVARS :== exp_Cond refl_exp GCDFunc hdeqz}]) by auto.
    rewrite H. split;auto. unfold CH. intros. destruct H0. rewrite <- H0.
    eexists;split;pauto. destruct H0. simpl. unfold Constraint. intros.
    do 3 destruct H. rewrite H. unfold hdeqz. simpl. rewrite (eqbVar_refl x).
    destruct x. destruct x0. simpl in *. remember (negb ((val0 =? 0) || (val1 mod val0 =? 0))).
    apply eq_sym in Heqb. destruct b. right. rewrite Bool.negb_true_iff in *.
    apply Bool.orb_false_elim in Heqb. destruct Heqb. auto.
    left. split;auto. unfold RefineCH. intros. destruct H1;try contradiction.
    remember (val0=?0). apply eq_sym in Heqb0. destruct b.
    eexists;split. left. auto. rewrite <- H1. unfold subAssn. simpl.
    unfold subEval. unfold exp_Cond. simpl. rewrite Heqb0. rewrite H. auto.
    eexists;split. right. left. auto. rewrite <- H1. unfold subAssn. simpl.
    unfold subEval. unfold exp_Cond. simpl. rewrite Heqb0. rewrite H. auto.
Qed.

