(*****************************************************************************)
(*                            *                    Trocq                     *)
(*  _______                   *       Copyright (C) 2023 Inria & MERCE       *)
(* |__   __|                  *    (Mitsubishi Electric R&D Centre Europe)   *)
(*    | |_ __ ___   ___ __ _  *       Cyril Cohen <cyril.cohen@inria.fr>     *)
(*    | | '__/ _ \ / __/ _` | *       Enzo Crance <enzo.crance@inria.fr>     *)
(*    | | | | (_) | (_| (_| | *   Assia Mahboubi <assia.mahboubi@inria.fr>   *)
(*    |_|_|  \___/ \___\__, | ************************************************)
(*                        | | * This file is distributed under the terms of  *)
(*                        |_| * GNU Lesser General Public License Version 3  *)
(*                            * see LICENSE file for the text of the license *)
(*****************************************************************************)
Require Import ssreflect.
From Trocq Require Import HoTTNotations.

Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Lemma transport {A : Type} (P : A -> Type) {x y : A} : x = y -> P x -> P y.
Proof. move->; exact. Defined.

Lemma paths_rect (A : Type) (a : A) (P : forall a0 : A, a = a0 -> Type) :
  P a idpath -> forall (a0 : A) (p : a = a0), P a0 p.
Proof. by move=> pa b; case: _ /. Defined.


Definition inv_V {A : Type} {x y : A} (p : x = y) : (p^)^ = p :=
  match p with idpath => 1 end.

Definition ap := f_equal.
Arguments ap {A B} f {x y}.

(* relation for forall *)
Monomorphic Axiom Funext : Prop.
Existing Class Funext.
Definition apD10 {A} {B : A -> Type} {f g : forall x, B x} (h : f = g)
  : f == g
  := fun x => match h with idpath => 1 end.
Axiom path_forall : forall `{Funext} {A : Type} {B : A -> Type} (f g : forall x : A, B x),
  f == g -> f = g.
Axiom apD10_retr : forall `{Funext} {A: Type} {B : A -> Type} (f g : forall x : A, B x),
  apD10 o (path_forall f g) == idmap.
Axiom apD10_sect : forall `{Funext} {A: Type} {B : A -> Type} (f g : forall x : A, B x),
  (path_forall f g) o apD10 == idmap.
Axiom apD10_adj : forall `{Funext} {A: Type} {B : A -> Type} (f g : forall x : A, B x),
  forall x : f = g, apD10_retr f g (apD10 x) = ap apD10 (apD10_sect f g x).

Definition path_arrow `{Funext} {A B : Type} (f g : A -> B)
  : (f == g) -> (f = g)
  := path_forall f g.

Definition equiv_flip@{i k} (A B : Type@{i}) (P : A -> B -> Type@{k}) :
(forall (a : A) (b : B), P a b) <->> (forall (b : B) (a : A), P a b).
Proof. by do 2!exists (fun PAB b a => PAB a b). Defined.

Definition inverse2 {A : Type} {x y : A} {p q : x = y} : p = q -> p^ = q^.
Proof. exact: ap. Defined.

Lemma concat_p1 {A : Type} {x y : A} (p : x = y) : p @ 1 = p.
Proof. reflexivity. Defined.

Lemma concat_1p {A : Type} {x y : A} (p : x = y) : 1 @ p = p.
Proof. by case: _ / p. Defined.

Lemma moveL_1V {A : Type} {x y : A} (p : x = y) (q : y = x) :
  p @ q = 1%path -> p = q^.
Proof. by case: _ / q p. Defined.

Lemma moveR_pM {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : y = x) :
  r = q @ p^ -> r @ p = q.
Proof. by case: _ / p q r. Defined.

Lemma transport_1@{i j} {A : Type@{i}} (P : A -> Type@{j})
    {x : A} (u : P x) : transport P 1 u = u.
Proof. done. Defined.

Lemma transport_pp@{i j} {A : Type@{i}} (P : A -> Type@{j})
    {x y z : A} (p : x = y) (q : y = z) (u : P x) :
  transport P (p @ q) u = transport P q (transport P p u).
Proof.
case: _ / q.
done.
Defined.

Lemma concat_pV@{i} {A : Type@{i}} {x y : A} (p : x = y) : p @ p^ = 1%path.
Proof. by case: _ / p. Defined.

Lemma concat_Vp@{i} {A : Type@{i}} {x y : A} (p : x = y) : p^ @ p = 1%path.
Proof. by case: _ / p. Defined.

Lemma path_prod {A B : Type} (z z' : A * B) :
  fst z = fst z' -> snd z = snd z' -> z = z'.
Proof.
by case: z z' => [? ?] [? ?] /= -> ->.
Defined.

(* Below a copy-paste of transposed material from HoTT. 
   TODO : tidy. *)

(****)

Definition ap_compose {A B C : Type} (f : A -> B) (g : B -> C) {x y : A} (p : x = y) :
ap (g o f) p = ap g (ap f p)
:=
match p with idpath => 1 end.

Definition ap_pp {A B : Type} (f : A -> B) {x y z : A} (p : x = y) (q : y = z) :
ap f (p @ q) = (ap f p) @ (ap f q)
:=
match q with
  idpath =>
  match p with idpath => 1 end
end.

Definition concat_pp_p {A : Type} {x y z t : A} (p : x = y) (q : y = z) (r : z = t) :
  (p @ q) @ r = p @ (q @ r) :=
  match r with idpath =>
    match q with idpath =>
      match p with idpath => 1
      end end end.

  Definition concat_1p_p1 {A : Type} {x y : A} (p : x = y)
: 1 @ p = p @ 1
:= concat_1p p @ (concat_p1 p)^.

Definition concat_A1p {A : Type} {f : A -> A} (p : forall x, f x = x) {x y : A} (q : x = y) :
(ap f q) @ (p y) = (p x) @ q
:=
match q with
  | idpath => concat_1p_p1 _
end.

Definition ap_V {A B : Type} (f : A -> B) {x y : A} (p : x = y) :
ap f (p^) = (ap f p)^
:=
match p with idpath => 1 end. 

Definition apD10_path_forall_cancel `{Funext} :
  forall {A : Type} {B : A -> Type} {f g : forall x : A, B x} (p : forall x, f x = g x),
    apD10 (path_forall f g p) = p.
Proof. intros; by apply apD10_retr. Defined.

Definition transport_apD10 :
  forall {A : Type} {B : A -> Type} {a : A} (P : B a -> Type)
         {t1 t2 : forall x : A, B x} {e : t1 = t2} {p : P (t1 a)},
    transport (fun (t : forall x : A, B x) => P (t a)) e p =
    transport (fun (t : B a) => P t) (apD10 e a) p.
Proof.
  intros A B a P t1 t2 [] p; reflexivity.
Defined.

(****)

(* While `is_true` exists in Rocq's Stdlib, it defined differently: fun b => b = true
   To simplify the proofs, we'll redefine it. *)
Definition is_true: Bool -> Type :=
  fun b => match b with
    | true => Unit
    | false => Empty
    end.

