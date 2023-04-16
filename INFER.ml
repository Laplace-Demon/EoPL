(*
inference rules

--------------------
type-of (const-exp num) tenv = int

--------------------
type-of (var-exp var) tenv = tenv(var)

type-of exp1 tenv = int
--------------------
type-of (zero?-exp exp1) tenv = bool

type-of exp1 tenv = int
type-of exp2 tenv = int
--------------------
type-of (diff-exp exp1 exp2) tenv = int

type-of exp1 tenv = t
--------------------
type-of (let-exp name exp1 body) tenv = type-of body [name=t]tenv

type-of exp1 tenv = bool
type-of exp2 tenv = t
type-of exp3 tenv = t
--------------------
type-of (if-exp exp1 exp2 exp3) tenv = t

type-of body [para=t_var] = t_res
--------------------
type-of (proc-exp para body) tenv = (t_var -> t_res)

type-of rator tenv = t1 -> t2
type-of rand tenv = t1
--------------------
type-of (call-exp rator rand) tenv = t2

type-of fun-body [para=t_var][name=(t_var->t_res)]tenv = t_res
--------------------
type-of (letrec-exp name para fun-body body) tenv = type-of body [name=(t_var->t_res)]tenv

type-of exp1 tenv = ty1
--------------------
type-of (newref exp1) tenv = refto ty1

type-of exp1 tenv = refto ty1
--------------------
type-of (deref exp1) tenv = ty1

type-of exp1 tenv = refto ty1
type-of exp2 tenv = ty1
--------------------
type-of (setref exp1 exp2) tenv = void

*)


"proc (f : ?) proc (x : ?) -((f 3),(f x))"

"letrec
  ? even(odd : ? x : ?) = if zero?(x) then 1 else (odd -(x,1))
  ? odd(x : ?) = if zero?(x) then 0 else ((even odd) -(x,1))
in (odd 13)"

"let x = newref 1
in let y = newref 2
in setref y deref x"