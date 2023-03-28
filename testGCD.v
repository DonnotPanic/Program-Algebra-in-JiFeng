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

Definition GLOBVARS := [(mkVar "a" 10);(mkVar "b" 4)].

Definition UNDEF := mkVar "Undefined" 0.

Instance myParams : ProgramAlgebra.UserParams :=
  ProgramAlgebra.Build_UserParams MyVar GLOBVARS eqVarb.

Axiom equalGLOB : GLOBVARS = ProgramAlgebra.GLOBVARS.

Axiom equalB : eqVarb = ProgramAlgebra.eqb.

Notation "|-| l" := (ProgramAlgebra.Choice_of_Alg_List l)(at level 20).

Notation "_|_" := (ProgramAlgebra.Chaos)(at level 10).

Notation "@{ e }" := (fun x => ProgramAlgebra.Assn x e)(at level 10).

Definition eqz_b : ProgramAlgebra.Boolexp :=
  fun l =>
    match (find (fun x => eqb x.(id) "b") l) with
    | Some x => if (PeanoNat.Nat.eqb x.(val) 0) then false else true
    | _ => false
    end.

Definition gcd_step := ProgramAlgebra.makeAssign ProgramAlgebra.GLOBVARS
  (fun l =>
   match (find (fun x => eqb x.(id) "a") l),
    (find (fun x => eqb x.(id) "b") l) with
   | Some x, Some y => [(mkVar x.(id) y.(val));(mkVar y.(id) (modulo x.(val) y.(val)))]
   | _, _ => []
   end).

Definition skip := ProgramAlgebra.makeAssign ProgramAlgebra.GLOBVARS
  (fun l => l).

Fixpoint mapid {s} (x : ProgramAlgebra.Alg s) :=
  match x with
  | ProgramAlgebra.Assn _ a => @{a} (ProgramAlgebra.Alg s)
  | ProgramAlgebra.Choice _ P Q =>
     ProgramAlgebra.Choice (ProgramAlgebra.Alg s) (mapid P) (mapid Q)
  | ProgramAlgebra.Chaos _ => _|_ (ProgramAlgebra.Alg s)
  | ProgramAlgebra.Seq _ P Q =>
     ProgramAlgebra.Choice (ProgramAlgebra.Alg s) (mapid P) (mapid Q)
  | ProgramAlgebra.Cond _ P b Q =>
     ProgramAlgebra.Cond (ProgramAlgebra.Alg s) (mapid P) b (mapid Q)
  | ProgramAlgebra.Recur _ f => _|_ (ProgramAlgebra.Alg s)
  end.

Definition testIter {s} (x : ProgramAlgebra.Alg s) :=
  ProgramAlgebra.Seq (ProgramAlgebra.Alg s)
  (mapid x) (ProgramAlgebra.Cond (ProgramAlgebra.Alg s)
     (@{gcd_step} (ProgramAlgebra.Alg s)) eqz_b
     (@{skip} (ProgramAlgebra.Alg s))).

Definition testRec := ProgramAlgebra.Recur (ProgramAlgebra.Alg bot) testIter.

Definition testnf := @{ ProgramAlgebra.makeAssign ProgramAlgebra.GLOBVARS 
  (fun l => [(mkVar "a" 2);(mkVar "b" 0)]) } bot.

Variable lub : ProgramAlgebra.Closure -> ProgramAlgebra.Ualg.

Example testlim : testIter testnf = testRec .
Proof. unfold testRec. rewrite ProgramAlgebra.Recur_clos with (lub := lub).
rewrite ProgramAlgebra.fix_is_lub with (lub := lub);auto.
unfold ProgramAlgebra.RecurFix. unfold testnf. eexists. split.
unfold testIter. unfold skip. unfold gcd_step.
rewrite ProgramAlgebra.Assign_Cond. unfold mapid.
rewrite ProgramAlgebra.Assign_compose. reflexivity.
unfold eqz_b. unfold ProgramAlgebra.exp_Cond.
simpl. unfold ProgramAlgebra.eqEval. auto.
Qed.




