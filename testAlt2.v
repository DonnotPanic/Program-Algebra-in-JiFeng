From PA Require Import ProgramAlgebraAlt.
Import ProgramAlgebraAlt.
Import Nat List.
Require Import String.
Import ListNotations.

Open Scope alg_scope.

Print Visibility.

Record Position := mkPos {
  hor : nat;
  ver : nat;
}.

Record MyVar := mkVar {
  id: string;
  val : Position;
}.

Definition eqbPos (x y : Position) :=
  andb (PeanoNat.Nat.eqb x.(hor) y.(hor))
       (PeanoNat.Nat.eqb x.(ver) y.(ver)).

Definition eqbVar (x y : MyVar) := 
  andb (eqb x.(id) y.(id)) (eqbPos x.(val) y.(val)).

Definition GLOBVARS := [(mkVar "start" {|hor:=0;ver:=0|});
  (mkVar "mid" {|hor:=5;ver:=5|});(mkVar "end" {|hor:=10;ver:=10|})].

Definition UNDEF := mkVar "Undefined" {|hor:=0;ver:=0|}.

Instance myParams : UserParams :=
  Build_UserParams MyVar GLOBVARS eqbVar.

Fixpoint shift (l : list Var) : list Var :=
  match l with
  | [] => []
  | h :: tl => (mkVar h.(id) (mkPos (h.(val).(hor)+1) h.(val).(ver))) :: shift tl
  end.

Definition reverse (l : list Var) : list Var :=
  let h := hd UNDEF l in let k := nth 1 l UNDEF in
  let t := nth 2 l UNDEF in
  (mkVar h.(id) t.(val)) :: (k :: [mkVar t.(id) h.(val)]).

Fixpoint unshift (l : list Var) : list Var :=
  match l with
  | [] => []
  | h :: tl => (mkVar h.(id) (mkPos (h.(val).(hor)-1) h.(val).(ver))) :: unshift tl
  end.

Definition shassn := makeAssign GLOBVARS shift.

Definition revassn := makeAssign GLOBVARS reverse.

Definition unshassn := makeAssign GLOBVARS unshift.



Definition testAlg := (@{ascassn}) ;;
  ((@{ascassn}) <| hdge2  |> (@{dscassn})).

Definition testAlg2 := (_|_) <| hdge2 |>
  ((|-|[@{ascassn};@{dscassn}]) ;; (@{ascassn})).

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
       (ascending x)) false_stat). simpl in r.
  assert(|-|[testassn] = testassn) by auto. rewrite H.
  unfold testassn. apply r. auto.
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
     values := fun x => ascending (descending x)
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
  pose (Seq_over_Choice [@{ GLOBVARS :== ascending};@{ GLOBVARS :== descending}]
    [@{ GLOBVARS :== ascending}]).
  apply (rwt_trans _ (|-|(map (fun g : Alg * Alg => fst g;; snd g) (list_prod
    [@{ ProgramAlgebraAlt.GLOBVARS :== ascending};
    @{ ProgramAlgebraAlt.GLOBVARS :== descending}]
    [@{ ProgramAlgebraAlt.GLOBVARS :== ascending}])))).
  apply r. 1,2 : unfold CH;intros; destruct H0. 2: destruct H0.
  all : try contradiction. all : try (eexists; rewrite H0; split; try apply rwt_refl;
  unfold Total_Assign;auto). clear r. unfold list_prod. simpl. unfold testassn2_1.
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
      rewrite <- H. apply rwt_refl. unfold Total_Assign. auto.
  - reflexivity.
  - unfold CH. intros. destruct H;try contradiction. unfold testassn in H.
    eexists. split. rewrite <- H. apply rwt_refl. unfold Total_Assign. auto.
  - unfold false_stat. unfold GLOBVARS. simpl. left. split;auto.
    unfold RefineCH. intros. destruct H; try contradiction. rewrite <- H.
    unfold testassn. exists testassn2_1. split.
    + unfold In. left. reflexivity.
    + unfold testassn2_1. unfold eqAssn. unfold eqEval. simpl. intros. auto.
Qed.
