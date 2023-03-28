The definition of  intial program：

$X=_\text{def} \{a,b := 10,6\}$

The recursive program：

$F=_\text{def}\lambda X \bullet (X;(\{a,b := b,a \ \text{mod}\  b\}\triangleleft \  b \neq 0 \ \triangleright \text{skip}))$

This program cannot be directly translated because the type of $X$ is inconsistent with the program that will be generated. `mapid` needs to be used to lift one level, from `Alg s` to `Alg (Alg s)`.

```coq
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
```

$\{a,b := b,a \ \text{mod}\  b\}$ corresponds to `gcd_step` ：

```coq
Definition gcd_step := ProgramAlgebra.makeAssign ProgramAlgebra.GLOBVARS
  (fun l =>
   match (find (fun x => eqb x.(id) "a") l),
    (find (fun x => eqb x.(id) "b") l) with
   | Some x, Some y => [(mkVar x.(id) y.(val));(mkVar y.(id) (modulo x.(val) y.(val)))]
   | _, _ => []
   end).
```

$b\neq 0$ corresponds to  `eqz_b` :

```coq
Definition eqz_b : ProgramAlgebra.Boolexp :=
  fun l =>
    match (find (fun x => eqb x.(id) "b") l) with
    | Some x => if (PeanoNat.Nat.eqb x.(val) 0) then false else true
    | _ => false
    end.
```

$\text{skip}$ corrsesponds to  `skip` ：

```coq
Definition skip := ProgramAlgebra.makeAssign ProgramAlgebra.GLOBVARS
  (fun l => l).
```

$F$ is defined as `testIter` as follows:

```coq
Definition testIter {s} (x : ProgramAlgebra.Alg s) :=
  ProgramAlgebra.Seq (ProgramAlgebra.Alg s)
  (mapid x) (ProgramAlgebra.Cond (ProgramAlgebra.Alg s)
     (@{gcd_step} (ProgramAlgebra.Alg s)) eqz_b
     (@{skip} (ProgramAlgebra.Alg s))).
```

The fixed point of the program

$\mu_X =_\text{def} \{a,b:= 2,0 \}$

```coq
Definition testnf := @{ ProgramAlgebra.makeAssign ProgramAlgebra.GLOBVARS 
  (fun l => [(mkVar "a" 2);(mkVar "b" 0)]) } bot.
```

We hereby are able to prove $f(\mu_X)=_A \mu_X$.

```coq
Definition testRec := ProgramAlgebra.Recur (ProgramAlgebra.Alg bot) testIter.
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
```