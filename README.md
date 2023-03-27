testGCD.v

$a=_{def} \{a,b := 10,6\}$

$f=_{def}\mu x. (x;(\{a,b := b,a-b\}\triangleleft ~ a > b~\triangleright \{a,b:=a,b\}))$

$x=_{def} \{a,b := 2,2\}$

$f^n(a) =_A x =_A f(x)$.

```coq
Definition gcd_step := ProgramAlgebra.makeAssign ProgramAlgebra.GLOBVARS
  (fun l =>
   match (find (fun x => eqb x.(id) "a") l),
    (find (fun x => eqb x.(id) "b") l) with
   | Some x, Some y => [(mkVar x.(id) y.(val));(mkVar y.(id) (x.(val) - y.(val)))]
   | _, _ => []
   end).
Definition skip := ProgramAlgebra.makeAssign ProgramAlgebra.GLOBVARS
  (fun l => l).
Definition testIter {s} (x : ProgramAlgebra.Alg s) :=
  ProgramAlgebra.Seq (ProgramAlgebra.Alg s)
  (mapid x) (ProgramAlgebra.Cond (ProgramAlgebra.Alg s)
     (@{gcd_step} (ProgramAlgebra.Alg s)) gt_a_b
     (@{skip} (ProgramAlgebra.Alg s))).
```