From Trocq Require Import -(notations) Trocq.
From mathcomp Require Import all_ssreflect zify lra.
From monae Require Import preamble hierarchy monad_lib monad_model.

Set Implicit Arguments.

Fixpoint fibo n :=
  match n with
  | 0 => 0
  | 0.+1 => 0.+1
  | (m.+1 as n).+1 => fibo m + fibo n
  end.

Definition cache := nat -> option nat.
(*Definition state A := cache -> cache * A.
Definition ret A (x : A) : state A := fun c => (c, x).
Definition bind A B (x : state A) (f : A -> state B) :=
  fun c => let (c', a) := x c in f a c'.
Definition get : state cache := fun c => (c,c).
Definition set (n v : nat) : state unit :=
  fun c => ((fun x => if x == n then Some v else c x), tt).*)

Section with_cache.
Variable M : stateRunMonad cache idfun.
Local Open Scope do_notation.
Local Open Scope monae_scope.

Definition update n v : M unit :=
  do c <- get; let c' x := if x == n then Some v else c x in put c'.

Definition lookup_or_compute n (m : M nat) :=
  do c <- get; if c n is Some x then Ret x else m.

Fixpoint fibo_memo n : M nat :=
  lookup_or_compute n
    (do x <-
      match n with
      | 0 => Ret 0
      | 0.+1 => Ret 0.+1
      | (m.+1 as n).+1 =>
          do x <- fibo_memo m;
          do y <- fibo_memo n;
          Ret (x+y)
      end;
     do _ <- update n x; Ret x).

Definition fibo_trunc k n := if n < k then Some (fibo n) else None.

Definition goodcache k c := c = fibo_trunc k.

Definition fibocache k :=
  {c : cache | goodcache k c}.

Definition R {X} k1 k2 (s : M X) (n : (idfun : monad) X) : Type :=
  forall c, goodcache k1 c ->
            (runStateT s c).1 = n /\ goodcache k2 (runStateT s c).2.

Infix "=" := Logic.eq : type_scope.

Lemma Rget k : R k k get (fibo_trunc k).
Proof.
move=> c Hc.
by rewrite runStateTget.
Qed.

Lemma Rret k A (a : A) : R k k (Ret a) a.
Proof.
move=> c Hc.
by rewrite runStateTret.
Qed.

Lemma Rlookup_and_compute k n (m : M nat) :
  R k (maxn k n.+1) m (fibo n) ->
  R k (maxn k n.+1) (lookup_or_compute n m) (fibo n).
Proof.
move=> Rmm' c Hc.
rewrite /lookup_or_compute.
rewrite runStateTbind runStateTget bindretf /= Hc /fibo_trunc.
case: ltnP => nk.
  rewrite runStateTret /=.
  split => //. 
  apply: boolp.funext => x.
  by have -> : maxn k n.+1 = k by lia.
rewrite -/(fibo_trunc k) -Hc.
exact: Rmm'.
Qed.

Lemma Rupdate k : R k k.+1 (update k (fibo k)) tt.
Proof.
move=> c Hc.
rewrite /update runStateTbind runStateTget bindretf runStateTput /=.
split => //.
apply: boolp.funext => x.
rewrite Hc /fibo_trunc ltnS.
by case: ltngtP => // ->.
Qed.

Lemma Rbind k1 k2 k3 A B (m : M A) m' :
  R k1 k2 m m' -> forall (f : A -> M B) f',
      (forall a, R k2 k3 (f a) (f' a)) ->
      R k1 k3 (m >>= f) (m' >>= f').
Proof.
move=> Rmm' f f' Rff' c Hc.
rewrite runStateTbind.
case: (Rmm' _ Hc).
case: (runStateT m c) => n2 c2 /= -> /[dup] Hc2 ->.
rewrite bindretf /=.
case: (Rff' m' _ Hc2).
rewrite Hc2.
by move ->.
Qed.

Lemma cacheok : forall n k,
    R k (max k n.+1) (fibo_memo n) (fibo n).
Proof.
elim/ltn_ind => -[|n] IH k.
rewrite [fibo_memo _]/=.
  have -> : fibo 0 = (Ret (fibo_trunc k) >>= fun=> Ret 0 : (idfun : monad) nat).
    by [].
  apply: Rbind.
    exact: Rget.
  move=> c.
  
  apply: Rbind.
  rewrite runStateTbind runStateTget bindretf /=.
  move=>


Arguments runStateT : simpl never.
Opaque runStateT.

Lemma cacheok : forall n, R (fibo_memo n) (fibo n).
Proof.
elim/ltn_ind => -[|n] IH.
  move=> c Hc /=.
  rewrite runStateTbind runStateTget bindretf /=.
  move: (Hc 0).
  case: (c 0) => [a|] [] //.
    case => ->. by rewrite runStateTret.
  move=> _.
  rewrite /update.
  rewrite bindretf runStateTbind runStateTbind /=.
  rewrite runStateTget bindA bindretf runStateTput.
  rewrite bindretf runStateTret /=.
  by split => // -[|n] //=; right.
rewrite /=.



Fixpoint fibo' n :=
  match n with
  | 0 => (0, 0.+1)
  | m.+1 => let (a,b) := fibo' m in (b, a+b)
  end.

Eval compute 

Definition state
