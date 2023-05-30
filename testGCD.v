From PA Require Import ProgramAlgebraAlt.
Import ProgramAlgebraAlt.
Import Nat.
Import List.
Require Import String.
Import ListNotations.

Open Scope alg_scope.

Print Visibility.

Record MyVar := mkVar {
  id: string;
  val : nat;
}.

Definition eqVarb (x y : MyVar) := 
  andb (eqb x.(id) y.(id)) (PeanoNat.Nat.eqb x.(val) y.(val)).

Variable GLOBVARS : list MyVar.

Definition Constraint : Prop := forall a b, GLOBVARS = [a;b].

Definition UNDEF := mkVar "Undefined" 0.

Instance myParams : UserParams :=
  Build_UserParams MyVar GLOBVARS eqVarb Constraint.

Search "eqb".

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
(**TODO*)

Definition GCDStr := Recur GCDStep (_|_).

Ltac CH_check := unfold CH;intros;try contradiction.

Ltac pauto := auto with palg.

Definition GCDRes := let a := hd UNDEF GLOBVARS in
  let b := hd UNDEF (tl GLOBVARS) in
  @{ GLOBVARS :== fun x => [(mkVar a.(id) 0);(mkVar b.(id) (PeanoNat.Nat.gcd a.(val) b.(val)))]}.

Lemma GcdBase : FNFPres (_|_) (GCDStep (_|_)).
Proof.
  unfold FNFPres. do 2 eexists. assert (skip = |-|[skip]) by auto.
  split;try split. apply (Chaos_to_NF []).
  unfold FNF. do 2 eexists. split;auto. CH_check.
  unfold GCDStep. split. pose (Chaos_zero_Seq_r GCDAssn).
  pose (rwt_comb _ _ _ _ (CDC hdeqz) (rwt_refl skip) r ).
  apply (rwt_trans _ _ _ r0). apply Cond_rev. unfold FNF.
  do 2 eexists. rewrite H. split;auto. CH_check.
  destruct H0; try contradiction. rewrite <- H0. unfold skip.
  eexists;split;pauto. unfold Refine. do 4 eexists. split; try split.
  3:split. 3: rewrite H. 1,3:reflexivity. 1,2 : CH_check.
  destruct H0;try contradiction. rewrite <- H0.
  unfold skip. eexists;split;pauto. intros. right. auto.
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

Lemma GcdReachRes : SthExists GCDRes GCDStr.
Abort.
(*
Proof.
  unfold Lub. split.
  - apply AlgPresInv;auto. apply GcdPres.
  - unfold FixExists. apply Streams.Further. apply Streams.Here.
    unfold GCDStep. simpl. unfold FixStep. unfold GCDRes.
    split;simpl. all : apply rwt_comm; unfold GCDAssn.
    + pose (Assign_Seq GLOBVARS GCDFunc refl_exp).
      pose (rwt_comb (@{ GLOBVARS :== refl_exp}) _ _ _ (CDC hdeqz)
       (rwt_refl (@{ GLOBVARS :== refl_exp})) r).
      apply (rwt_trans _ _ _ r0). clear r r0.
      pose (Assign_Cond GLOBVARS refl_exp (fun x : list Var =>
       refl_exp (GCDFunc x)) hdeqz). apply (rwt_trans _ _ _ r).
      clear r. apply eval_equiv. unfold eqEval. simpl. auto.
    + pose (Assign_Seq GLOBVARS GCDFunc refl_exp).
      pose (rwt_comb (@{ GLOBVARS :== refl_exp}) _ _ _ (CDC hdeqz)
       (rwt_refl (@{ GLOBVARS :== refl_exp})) r).
      pose (Assign_Cond GLOBVARS refl_exp (fun x : list Var =>
       refl_exp (GCDFunc x)) hdeqz).
      pose (rwt_trans _ _ _ r0 r1).
      pose (rwt_comb _ _ _ _ Seq (rwt_refl (@{ GLOBVARS :== GCDFunc}))
       r2). pose (Assign_Seq GLOBVARS GCDFunc (exp_Cond refl_exp (fun x 
       => refl_exp (GCDFunc x)) hdeqz)). pose (rwt_trans _ _ _ r3 r4).
      pose (rwt_comb _ _ _ _ (CDC hdeqz) r2 r5).
      apply (rwt_trans _ _ _ r6). clear r r0 r1 r2 r3 r4 r5 r6.
      pose (Assign_Cond GLOBVARS (exp_Cond refl_exp (fun x=> refl_exp (GCDFunc x)) hdeqz)
        (fun x => exp_Cond refl_exp (fun x0 : list Var => refl_exp (GCDFunc x0))
         hdeqz (GCDFunc x)) hdeqz). apply (rwt_trans _ _ _ r).
      clear r. apply eval_equiv. unfold eqEval. simpl. auto.
Qed.*)

Definition falg := (_|_).

Lemma refinegcd : exists r s, (r <--> falg /\ FNF r) /\ 
   (s <--> GCDRes /\ FNF s) /\ Refine r s.
Abort.
Proof.
  do 2 eexists. split;try split;try split.
  - apply rwt_comm. unfold GCDRes. apply (Assign_to_NF _ _ false_stat).
    auto.
  - unfold FNF. do 2 eexists. split;eauto. unfold CH. intros.
    destruct H; try contradiction. rewrite <- H. eexists;split;try apply rwt_refl.
    unfold Total_Assign. auto. 
  - apply rwt_comm. unfold altGcd. apply (Assign_to_NF _ _ false_stat).
    auto.
  - unfold FNF. do 2 eexists. split;eauto. unfold CH. intros.
    destruct H;try contradiction. rewrite <- H. eexists;split;try apply rwt_refl.
    unfold Total_Assign. auto. 
  - unfold Refine. do 4 eexists; eauto. split;try split;try split;try reflexivity.
    1,2 : unfold CH;intros;destruct H;try contradiction; rewrite <- H; eexists;split;
    try apply rwt_refl;unfold Total_Assign; auto. left. split;auto.
    unfold RefineCH. intros. destruct H; try contradiction. rewrite <- H.
    eexists. split. unfold In. left. reflexivity. unfold eqAssn. unfold eqEval.
    simpl.  auto.
Qed.

