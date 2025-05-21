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
      | (0 as n).+1 =>
          do _ <- fibo_memo n;
          Ret 0.+1
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

Lemma Rlookup_or_compute k n (m : M nat) :
  (k <= n -> R k (maxn k n.+1) m (fibo n)) ->
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
      (R k2 k3 (f m') (f' m')) ->
      R k1 k3 (m >>= f) (m' >>= f').
Proof.
move=> Rmm' f f' Rff' c Hc.
rewrite runStateTbind.
case: (Rmm' _ Hc).
case: (runStateT m c) => n2 c2 /= -> /[dup] Hc2 ->.
rewrite bindretf /=.
case: (Rff' _ Hc2).
rewrite Hc2.
by move ->.
Qed.

Lemma cacheok : forall n k,
    R k (maxn k n.+1) (fibo_memo n) (fibo n).
Proof.
elim/ltn_ind => -[|n] IH k.
  rewrite [fibo_memo _]/=.
  apply: Rlookup_or_compute.
  rewrite bindretf.
  have -> : fibo 0 = Ret tt >> Ret 0 :> (idfun : monad) nat by [].
  rewrite leqn0 => /eqP ->.
  apply: Rbind.
    exact: Rupdate.
  exact: Rret.
rewrite [fibo_memo _]/=.
case: n IH => [|n] IH.
  apply: Rlookup_or_compute => k1.
  rewrite bindA.
  have -> : fibo 1 = Ret 0 >> (Ret tt >> Ret (fibo 1))
          :> (idfun : monad) nat by [].
  apply: Rbind.
    exact: IH.
  rewrite (bindretf 1).
  apply: Rbind.
    have -> : maxn k 1 = 1 by lia.
    exact: Rupdate.
  have -> : maxn k 2 = 2 by lia.
  exact: Rret.
apply: Rlookup_or_compute => Hk.
rewrite bindA.
have -> : fibo n.+2 =
          Ret (fibo n) >> (Ret (fibo n.+1) >> (Ret tt >> Ret (fibo n.+2)))
        :> (idfun : monad) nat by [].
apply: Rbind.
  exact: IH.
rewrite bindA.
apply: Rbind.
  exact: IH.
rewrite (bindretf (_ + _)).
apply: Rbind.
  rewrite (_ : maxn _ _ = n.+2); last by lia.
  exact: Rupdate.
have -> : maxn k n.+3 = n.+3 by lia.
exact: Rret.
Qed.

End with_cache.

Fixpoint fibo' n :=
  match n with
  | 0 => (0, 0.+1)
  | m.+1 => let (a,b) := fibo' m in (b, a+b)
  end.
