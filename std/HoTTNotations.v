Reserved Notation "p ^" (at level 1, format "p '^'").
Reserved Notation "p @ q" (at level 20).
Reserved Notation "p @@ q" (at level 20).
Reserved Notation "p @' q" (at level 21, left associativity,
  format "'[v' p '/' '@''  q ']'").
Reserved Notation "f == g" (at level 70, no associativity).
Reserved Notation "g 'o' f" (at level 40, left associativity).
Reserved Notation "x .1" (at level 1, left associativity, format "x '.1'").
Reserved Notation "x .2" (at level 1, left associativity, format "x '.2'").
Reserved Notation "A <=> B" (at level 70, no associativity, format "A  <=>  B").
Reserved Notation "A <--> B" (at level 70).
Reserved Notation "A <->> B" (at level 70).
Reserved Notation "n .+1" (at level 2, left associativity, format "n .+1").
Reserved Notation "n .+2" (at level 2, left associativity, format "n .+2").
Reserved Notation "n .+3" (at level 2, left associativity, format "n .+3").
Reserved Notation "n .+4" (at level 2, left associativity, format "n .+4").
Reserved Notation "n .+5" (at level 2, left associativity, format "n .+5").
Reserved Notation "n '.-1'" (at level 2, left associativity, format "n .-1").
Reserved Notation "n '.-2'" (at level 2, left associativity, format "n .-2").
Reserved Notation "m +2+ n" (at level 50, left associativity).
Reserved Infix "mod" (at level 40, no associativity).
Reserved Notation "p ~ 1" (at level 7, left associativity, format "p '~' '1'").
Reserved Notation "p ~ 0" (at level 7, left associativity, format "p '~' '0'").

Declare Scope fibration_scope.
Declare Scope path_scope.
Delimit Scope path_scope with path.

(* compatibility layer with HoTT *)
Open Scope fibration_scope.
Open Scope path_scope.


Notation pr1 := projT1.
Notation pr2 := projT2.

Notation paths := eq.
Notation "x = y" := (Logic.eq x y) : type_scope.

Notation idpath := eq_refl.
Notation inverse := eq_sym.
Notation concat := eq_trans.
Notation idmap := (fun x => x).
Notation Unit := unit.
Notation none := None.
Notation Bool := bool.
Notation Empty := False.
Notation "f == g" := (forall x, f x = g x).
Notation "g 'o' f" := ((fun g0 f0 x => g0 (f0 x)) g f).

Notation "( x ; y )" := (existT _ x y) : fibration_scope.
Notation "x .1" := (pr1 x) : fibration_scope.
Notation "x .2" := (pr2 x) : fibration_scope.
Notation "A <--> B" := ((A -> B) * (B -> A))%type : fibration_scope.
Notation "A <->> B" := {f : A -> B & { g : B -> A & forall x, g (f x) = x}} : fibration_scope.

Notation "1" := idpath : path_scope.
Notation "e ^" := (eq_sym e%path) : path_scope.
Notation "p @ q" := (eq_trans p q) : path_scope.
