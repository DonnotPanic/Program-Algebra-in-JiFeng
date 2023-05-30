From PA Require Import ProgramAlgebraAlt.
Import ProgramAlgebraAlt.
Require Import Lia.
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

Definition eqbVar (x y : MyVar) := 
  andb (eqb x.(id) y.(id)) (PeanoNat.Nat.eqb x.(val) y.(val)).

Variable GLOBVARS : list MyVar.

Definition Constraint := exists a b c, (PeanoNat.Nat.leb a.(val) 10 = true)
 /\ (eqbVar a b = false) /\ (eqbVar a c = false) /\ (eqbVar b c = false) /\ GLOBVARS = [a;b;c].

Lemma eqbVar_sym : forall x y, eqbVar x y = eqbVar y x.
Proof. intros. unfold eqbVar. destruct x. destruct y. simpl.
  assert ((id0 =? id1) % string = (id1 =? id0) %string) by apply eqb_sym.
  assert ((val0 =? val1) = (val1 =? val0)) by apply PeanoNat.Nat.eqb_sym.
  rewrite H. rewrite H0. auto. Qed.

Definition UNDEF := mkVar "Undefined" 0.

Instance myParams : UserParams :=
  Build_UserParams MyVar GLOBVARS eqbVar Constraint.

Fixpoint ascending (l : list Var) : list Var :=
  match l with
  | [] => []
  | h :: tl => (mkVar h.(id) (h.(val) + 1)) :: ascending tl
  end.

Fixpoint descending (l : list Var) : list Var :=
  match l with
  | [] => []
  | h :: tl => (mkVar h.(id) (h.(val) - 1)) :: descending tl
  end.

Definition dscassn := makeAssign GLOBVARS descending.

Definition ascassn := makeAssign GLOBVARS ascending.

Definition hdge2 : Boolexp :=
 fun l =>
  match (hd_error l) with
  | None => false
  | Some x => if (PeanoNat.Nat.leb 20 x.(val)) then true else false
  end.

Definition testAlg := (@{ascassn}) ;;
  ((@{ascassn}) <| hdge2  |> (@{dscassn})).

Definition testAlg2 := (_|_) <| hdge2 |>
  (@{ascassn}) ;; ((|-|[@{ascassn};@{dscassn}])).

Definition testassn := Lift (Assn
  {|
    ids := GLOBVARS;
    values :=
      fun x =>
       exp_Cond ascending descending hdge2
       (ascending x)
  |}).

Definition testnf :=
 (_|_) <| false_stat |> (|-| [testassn]).

Ltac rwt_step := apply rwt_comb;auto;try apply rwt_refl.

Lemma nf : testAlg <--> testnf.
Proof.
  unfold testAlg. unfold testnf. unfold ascassn. unfold dscassn.
  apply (rwt_trans _ (@{ ProgramAlgebraAlt.GLOBVARS :== ascending } ;;
     (@{ ProgramAlgebraAlt.GLOBVARS :== exp_Cond ascending descending hdge2 }))).
  rwt_step. apply Assign_Cond.
  pose (Assign_Seq GLOBVARS ascending (exp_Cond ascending descending hdge2)).
  simpl in r. apply (rwt_trans _ _ _ r). clear r.
  pose (Assign_to_NF GLOBVARS (fun x => exp_Cond ascending descending hdge2
       (ascending x))). simpl in r.
  assert(|-|[testassn] = testassn) by auto. rewrite H.
  unfold testassn. apply r.
Qed.

Definition testassn2_1 := Lift (Assn
  {|
    ids := GLOBVARS;
    values :=
      fun x  => ascending (ascending x)
  |}).

Definition testassn2_2 := Lift (Assn
   {|
     ids := GLOBVARS;
     values := fun x => descending (ascending x)
   |}).

Definition testnf2 :=
  (_|_) <| hdge2 |> (|-|[testassn2_1;testassn2_2]).

Lemma nf2 : testAlg2 <--> testnf2.
Proof.
  unfold testAlg2. unfold testnf2. unfold ascassn. unfold dscassn.
  rwt_step. assert (GLOBVARS = ProgramAlgebraAlt.GLOBVARS) by auto.
  repeat rewrite H. remember (|-| [@{ ProgramAlgebraAlt.GLOBVARS :== ascending};
     @{ ProgramAlgebraAlt.GLOBVARS :== descending}]). rewrite <- H.
  assert (@{ GLOBVARS :== ascending} = |-| [@{ GLOBVARS :== ascending}]) by auto.
  rewrite H0. rewrite Heqa. repeat rewrite <- H. clear Heqa. clear H0.
  pose (Seq_over_Choice [@{ GLOBVARS :== ascending}]
   [@{ GLOBVARS :== ascending};@{ GLOBVARS :== descending}]).
  apply (rwt_trans _ (|-|(map (fun g : Alg * Alg => fst g;; snd g) (list_prod
    [@{ ProgramAlgebraAlt.GLOBVARS :== ascending}]
    [@{ ProgramAlgebraAlt.GLOBVARS :== ascending};
    @{ ProgramAlgebraAlt.GLOBVARS :== descending}])))).
  apply r. 1,2 : unfold CH;intros; destruct H0. 2: destruct H0.
  all : try contradiction. all : try (eexists; rewrite H0; split; try apply rwt_refl;
  pauto). destruct H0; try contradiction. rewrite  <- H0.
  eexists;split;pauto. clear r. unfold list_prod. simpl. unfold testassn2_1.
  unfold testassn2_2. rwt_step;apply Assign_Seq.
Qed.

Example testrefine : Refine testnf2 testnf.
Proof. 
  unfold Refine. unfold testnf. unfold testnf2.
  do 4 eexists. split;split;try split. 
  - unfold CH. intros. destruct H.
    + unfold testassn2_1 in H. eexists. split. rewrite <- H. apply rwt_refl.
      unfold Total_Assign. auto.
    + destruct H;try contradiction. unfold testassn2_2 in H. eexists. split.
      rewrite <- H. all : pauto.
  - reflexivity.
  - unfold CH. intros. destruct H;try contradiction. unfold testassn in H.
    eexists. split;try rewrite <- H;pauto.
  - simpl in *. unfold Constraint. intros. do 4 destruct H. destruct H0.
    destruct H1. destruct H2. unfold false_stat. left. split;auto.
    unfold RefineCH. intros. destruct H4; try contradiction. rewrite <- H4.
    unfold testassn. exists testassn2_2. split.
    + unfold In. right. left. reflexivity.
    + assert (forall x, eqbVar x x = true). { intros. unfold eqbVar. destruct x3.
      simpl. apply Bool.andb_true_iff. split. apply eqb_refl. apply PeanoNat.Nat.eqb_refl. }
      unfold testassn2_1. unfold eqAssn. unfold eqEval. rewrite H3. simpl.
      unfold extends_mapping. unfold extends_mapping_help. simpl. rewrite H3.
      simpl. repeat rewrite H5. pose (eqbVar_sym x0 x). pose (eqbVar_sym x1 x).
      pose (eqbVar_sym x1 x0). rewrite H0 in e. rewrite H1 in e0. rewrite H2 in e1.
      rewrite e. rewrite e0. rewrite e1. unfold exp_Cond. unfold hdge2.
      pose (PeanoNat.Nat.leb_spec0 (val x) 10). apply Bool.reflect_iff in r.
      apply r in H. assert ((val x) + 1 < 20). lia. pose (PeanoNat.Nat.ltb_spec0 (val x + 1) 20).
      apply Bool.reflect_iff in r0. rewrite r0 in H6.
      rewrite PeanoNat.Nat.ltb_antisym in H6. rewrite Bool.negb_true_iff in H6.
      unfold hd_error. assert (val x + 1 = val {| id := id x; val := val x + 1 |}) by auto.
      rewrite <- H7. rewrite H6. simpl. auto. 
Qed.



