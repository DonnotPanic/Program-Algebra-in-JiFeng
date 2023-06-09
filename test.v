From PA Require Import ProgramAlgebra.
Import Nat.
Import List.
Require Import String.
Import ListNotations.

Variable bot : Type.

Record MyVar := mkVar {
  id: string;
  val : nat;
}.

Definition eqVarb (x y : MyVar) := 
  andb (eqb x.(id) y.(id)) (PeanoNat.Nat.eqb x.(val) y.(val)).

Definition tt := mkVar "a" 1.

Definition GLOBVARS := [tt;(mkVar "b" 2);(mkVar "c" 3)].

Definition UNDEF := mkVar "Undefined" 0.

Instance myParams : ProgramAlgebra.UserParams :=
  ProgramAlgebra.Build_UserParams MyVar GLOBVARS eqVarb.

Axiom equalGLOB : GLOBVARS = ProgramAlgebra.GLOBVARS.

Axiom equalB : eqVarb = ProgramAlgebra.eqb.

Notation "|-| l" := (ProgramAlgebra.Choice_of_Alg_List l)(at level 20).

Notation "_|_" := (ProgramAlgebra.Chaos)(at level 10).

Notation "@{ e }" := (fun x => ProgramAlgebra.Assn x e)(at level 10).

Fixpoint ascending (l : list (ProgramAlgebra.Var)) : list (ProgramAlgebra.Var) :=
  match l with
  | [] => []
  | h :: tl => (mkVar h.(id) (h.(val) + 1)) :: ascending tl
  end.

Definition cast (a : list MyVar) : list ProgramAlgebra.Var := a.

Definition fstassn := ProgramAlgebra.makeAssign (cast [tt]) ascending.

Definition allassn := ProgramAlgebra.makeAssign ProgramAlgebra.GLOBVARS ascending.

Definition hdge2 : ProgramAlgebra.Boolexp :=
 fun l =>
  match (hd_error l) with
  | None => false
  | Some x => if (PeanoNat.Nat.leb 2 x.(val)) then true else false
  end.

Definition testAlg := ProgramAlgebra.Seq bot (@{fstassn} bot)
  (ProgramAlgebra.Cond bot (@{allassn} bot) hdge2 (@{fstassn} bot)).

Definition testAlg2 := ProgramAlgebra.Cond bot
  (_|_ bot) hdge2
  (ProgramAlgebra.Seq bot
  (|-|[@{fstassn} bot;@{allassn} bot])
  (@{fstassn} bot)).

Definition testassn := ProgramAlgebra.Assn bot
  (ProgramAlgebra.extends_assign
  {|
    ProgramAlgebra.ids := ProgramAlgebra.GLOBVARS;
    ProgramAlgebra.values :=
      fun x =>
      ProgramAlgebra.extends_mapping 
        (cast [tt]) ascending
        (ProgramAlgebra.extends_mapping 
           (cast [tt]) ascending x)
  |}).

Definition testnf :=
 ProgramAlgebra.Cond bot (_|_ bot) ProgramAlgebra.false_stat (|-| [testassn]).

Lemma nf_assn : testAlg = testassn.
Proof. unfold testAlg. remember (ProgramAlgebra.Cond bot
     (ProgramAlgebra.Assn bot allassn) hdge2
     (ProgramAlgebra.Assn bot fstassn)).
  rewrite (ProgramAlgebra.Assign_extends fstassn) in *.
  unfold ProgramAlgebra.extends_assign in *.
  unfold allassn in Heqa.
  rewrite (ProgramAlgebra.Assign_Cond bot ProgramAlgebra.GLOBVARS ascending) in Heqa.
  rewrite Heqa. rewrite ProgramAlgebra.Assign_compose.
  unfold testassn. rewrite <- equalGLOB. unfold GLOBVARS.
  unfold hdge2. unfold tt. simpl. 
  rewrite <- ProgramAlgebra.Assign_extends. auto.
Qed.

Lemma nf : testAlg = testnf.
Proof. rewrite nf_assn. unfold testassn.
  rewrite <- ProgramAlgebra.Assign_extends.
  rewrite (ProgramAlgebra.Assign_to_NF _ _ ProgramAlgebra.false_stat);auto.
Qed.

Definition testassn2_1 := ProgramAlgebra.Assn bot
  {|
    ProgramAlgebra.ids :=
      ProgramAlgebra.GLOBVARS;
    ProgramAlgebra.values :=
      fun x : list ProgramAlgebra.Var =>
      ProgramAlgebra.extends_mapping
        (ProgramAlgebra.ids fstassn)
        (ProgramAlgebra.values fstassn)
        (ProgramAlgebra.extends_mapping
           (ProgramAlgebra.ids fstassn)
           (ProgramAlgebra.values fstassn) x)
  |}.

Definition testassn2_2 := ProgramAlgebra.Assn bot
   {|
     ProgramAlgebra.ids :=
       ProgramAlgebra.GLOBVARS;
     ProgramAlgebra.values :=
       fun x : list ProgramAlgebra.Var =>
       ProgramAlgebra.extends_mapping
         (ProgramAlgebra.ids fstassn)
         (ProgramAlgebra.values fstassn)
         (ascending x)
   |}.

Definition testnf2 :=
  ProgramAlgebra.Cond bot ((_|_) bot) hdge2 (|-|[testassn2_1;testassn2_2]).

Lemma nf2 : testAlg2 = testnf2.
Proof. unfold testAlg2.
  assert ((ProgramAlgebra.Assn bot fstassn) = |-| [(ProgramAlgebra.Assn bot fstassn)]).
  { unfold ProgramAlgebra.Choice_of_Alg_List. rewrite ProgramAlgebra.Choice_zero_r. auto. }
  remember (ProgramAlgebra.Seq bot
     (|-| [ProgramAlgebra.Assn bot fstassn;
           ProgramAlgebra.Assn bot allassn])).
  rewrite H. rewrite Heqa. rewrite ProgramAlgebra.Seq_over_Choice.
  unfold list_prod. simpl. all : rewrite (ProgramAlgebra.Assign_extends fstassn).
  all : unfold allassn. all: unfold ProgramAlgebra.extends_assign.
  do 2 (rewrite ProgramAlgebra.Assign_compose).
  unfold testnf2. unfold ProgramAlgebra.Choice_of_Alg_List.
  auto. all : unfold ProgramAlgebra.CH;intros;try destruct H0;eexists;split;auto.
  all : unfold ProgramAlgebra.Total_Assign. all : try rewrite H0; auto.
  all : try destruct H0;try rewrite e;auto.
  unfold In in i. contradiction. Unshelve. unfold In in H0. contradiction.
Qed.

Example testrefine : ProgramAlgebra.Refine testnf2 testnf.
Proof.
  unfold ProgramAlgebra.Refine. unfold testnf. unfold testnf2.
  do 6 eexists. split;split;try split.
  - reflexivity.
  - unfold ProgramAlgebra.CH. intros. destruct H.
    + eexists. split. rewrite <- H. reflexivity. unfold ProgramAlgebra.Total_Assign.
      auto.
    + destruct H;try contradiction. eexists. split. rewrite <- H. reflexivity.
      unfold ProgramAlgebra.Total_Assign. auto.
  - reflexivity.
  - split. reflexivity. unfold ProgramAlgebra.CH.
    intros. destruct H;try contradiction.
    rewrite <- H. eexists. split;try reflexivity. 
    unfold ProgramAlgebra.extends_assign.
    unfold ProgramAlgebra.Total_Assign. auto.
  - unfold ProgramAlgebra.false_stat. unfold ProgramAlgebra.GLOBVARS. simpl.
    left. split;auto. unfold ProgramAlgebra.RefineCH.
    intros. destruct H; try contradiction. eexists.
    split.
    + unfold In. left. reflexivity.
    + rewrite <- H. unfold ProgramAlgebra.eqAssn. unfold ProgramAlgebra.eqEval.
      simpl. intros. auto.
Qed.

Fixpoint hdge2inf {s} (x : ProgramAlgebra.Alg s) : bool :=
  match x with
  | ProgramAlgebra.Assn _ a => hdge2 (a.(ProgramAlgebra.values) a.(ProgramAlgebra.ids))
  | ProgramAlgebra.Choice _ P Q => orb (hdge2inf P) (hdge2inf Q)
  | _ => false
  end.

Fixpoint update {s} (x : ProgramAlgebra.Alg s) : ProgramAlgebra.Alg (ProgramAlgebra.Alg s) :=
  match x with
  | ProgramAlgebra.Assn _ a => @{ {|
      ProgramAlgebra.ids := ProgramAlgebra.GLOBVARS;
      ProgramAlgebra.values :=
        fun x =>
        ProgramAlgebra.extends_mapping 
          (cast [tt]) ascending
          (a.(ProgramAlgebra.values) x)
    |} } (ProgramAlgebra.Alg s)
  | ProgramAlgebra.Choice _ P Q =>
      ProgramAlgebra.Choice (ProgramAlgebra.Alg s) (update P) (update Q)
  | _ => |-|[]
  end.

Fixpoint mapid {s} (x : ProgramAlgebra.Alg s) :=
  match x with
  | ProgramAlgebra.Assn _ a => @{a} (ProgramAlgebra.Alg s)
  | ProgramAlgebra.Choice _ P Q =>
     ProgramAlgebra.Choice (ProgramAlgebra.Alg s) (mapid P) (mapid Q)
  | ProgramAlgebra.Chaos _ => _|_ (ProgramAlgebra.Alg s)
  | _ => |-|[]
  end.

Definition testIter {s} (x : ProgramAlgebra.Alg s) :=
  match x with
  | ProgramAlgebra.Cond _ p b t => if hdge2inf t then
         ProgramAlgebra.Cond (ProgramAlgebra.Alg s) (mapid p) b (mapid t)
         else ProgramAlgebra.Cond (ProgramAlgebra.Alg s) (mapid p) b (update t)
  | _ => ProgramAlgebra.Cond (ProgramAlgebra.Alg s)
         (_|_ (ProgramAlgebra.Alg s))
         ProgramAlgebra.false_stat
         (|-| [])
  end.

Definition testRec := ProgramAlgebra.Recur (ProgramAlgebra.Alg bot) testIter.

Search "fix_is_lub".

Variable lub : ProgramAlgebra.Closure -> ProgramAlgebra.Ualg.

Example testlim : testIter testnf = testRec .
Proof. unfold testRec. rewrite ProgramAlgebra.Recur_clos with (lub := lub).
rewrite ProgramAlgebra.fix_is_lub with (lub := lub);auto.
unfold ProgramAlgebra.RecurFix. unfold testnf. unfold testIter.
unfold hdge2inf. unfold testassn. unfold ProgramAlgebra.EqAlg.
unfold mapid. simpl. repeat split;auto.
unfold ProgramAlgebra.eqEval. intros. simpl in *. auto.
unfold ProgramAlgebra.eqEval. intros. auto.
Qed.





