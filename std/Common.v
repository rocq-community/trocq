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
From Trocq Require Export Stdlib Hierarchy.

Set Universe Polymorphism.

Import HoTTNotations.

Definition graph@{i} {A B : Type@{i}} (f : A -> B) := paths o f.

Module Fun.
Section Fun.
Universe i.
Context {A B : Type@{i}} (f : A -> B) (g : B -> A).
Definition toParam : Param40.Rel@{i} A B :=
  @Param40.BuildRel A B (graph f)
     (@Map4.BuildHas@{i} _ _ _ _
       (fun _ _ => idmap) (fun _ _ => idmap) (fun _ _ _ => 1%path))
     (@Map0.BuildHas@{i} _ _ _).

Definition toParamSym : Param04.Rel@{i} A B :=
  @Param04.BuildRel A B (sym_rel (graph g))
     (@Map0.BuildHas@{i} _ _ _)
     (@Map4.BuildHas@{i} _ _ _ g (fun _ _ => idmap) (fun _ _ => idmap)
        (fun _ _ _ => 1%path)).
End Fun.
End Fun.

Module SplitInj.
Section SplitInj.
Universe i.
Context {A B : Type@{i}}.
Record type@{} := Build {
  section :> A -> B;
  retract : B -> A;
  sectionK : forall x, retract (section x) = x
}.

Definition fromParam@{} (R : Param2a2b.Rel@{i} A B) := {|
  section := map R;
  retract := comap R;
  sectionK x := R_in_comap R _ _ (map_in_R R _ _ 1%path)
|}.

Section to.
Variable (f : type).

Let section_in_retract b a (e : f a = b) : retract f b = a :=
  transport (fun x => retract f x = a) e (sectionK f a).

Definition toParam@{} : Param42b.Rel@{i} A B :=
  @Param42b.BuildRel A B (graph f)
     (@Map4.BuildHas@{i} _ _ _ _ (fun _ _ => idmap) (fun _ _ => idmap)
        (fun _ _ _ => 1%path))
     (@Map2b.BuildHas@{i} _ _ _ _ section_in_retract).

Definition toParamSym@{} : Param2b4.Rel@{i} B A :=
  @Param2b4.BuildRel B A (sym_rel (graph f))
     (@Map2b.BuildHas@{i} _ _ _ _ section_in_retract)
     (@Map4.BuildHas@{i} _ _ _ _ (fun _ _ => idmap) (fun _ _ => idmap)
        (fun _ _ _ => 1%path)).

End to.

End SplitInj.
End SplitInj.
Arguments SplitInj.Build {A B section retract}.

Module SplitSurj.
Section SplitSurj.
Universe i.
Context {A B : Type@{i}}.
Record type := Build {
  retract :> A -> B;
  section : B -> A;
  sectionK : forall x, retract (section x) = x
}.

Definition fromParam@{} (R : Param2b2a.Rel@{i} A B) := {|
  retract := map R;
  section := comap R;
  sectionK x := R_in_map R (comap R x) x (comap_in_R R x (comap R x) 1%path)
|}.

Section to.
Context (f : type).

Let section_in_retract b a (e : section f b = a) : f a = b :=
  transport (fun x => f x = b) e (sectionK f b).

Definition toParam@{} : Param42a.Rel@{i} A B :=
  @Param42a.BuildRel A B (graph f)
     (@Map4.BuildHas@{i} _ _ _ _ (fun _ _ => idmap) (fun _ _ => idmap)
        (fun _ _ _ => 1%path))
     (@Map2a.BuildHas@{i} _ _ _ _ section_in_retract).

Definition toParamSym@{} : Param2a4.Rel@{i} B A :=
  @Param2a4.BuildRel B A (sym_rel (graph f))
     (@Map2a.BuildHas@{i} _ _ _ _ (section_in_retract))
     (@Map4.BuildHas@{i} _ _ _ _ (fun _ _ => idmap) (fun _ _ => idmap)
        (fun _ _ _ => 1%path)).

End to.

End SplitSurj.
End SplitSurj.
Arguments SplitSurj.Build {A B retract section}.

Module Iso.
Section Iso.
Universe i.
Context {A B : Type@{i}}.
Record type@{} := Build {
  map :> A -> B;
  comap : B -> A;
  mapK : forall x, comap (map x) = x;
  comapK : forall x, map (comap x) = x
}.

Section to.
Variable (f : type).

Let mapK' x : comap f (f x) = x :=
  ap (comap f) (ap f (mapK f x)^) @ ap (comap f) (comapK f _) @ mapK f x.

Let comap_in_map b a (e : comap f b = a) : f a = b :=
  ap f e^ @ comapK f b.

Let map_in_comap b a (e : f a = b) : comap f b = a :=
  ap (comap f) e^ @ mapK' a.

Let map_in_comapK b a (e : f a = b) :
  comap_in_map b a (map_in_comap b a e) = e.
Proof. 
rewrite /map_in_comap /comap_in_map /mapK' /=.
dependent inversion e as [H] => {H}.
rewrite concat_1p eq_trans_sym_distr ap_pp !concat_pp_p.
rewrite [ap f (mapK f a)^]ap_V.
set p1 := ap f _. set p2 := comapK _ _.
rewrite eq_trans_sym_distr.
rewrite -2!ap_V inv_V -ap_pp -ap_compose.
set i := (X in ap X _).
rewrite concat_A1p.
by rewrite -concat_pp_p concat_pV concat_1p concat_Vp.
Defined.

Definition toParam@{} : Param44.Rel@{i} A B :=
  @Param44.BuildRel A B (graph f)
     (@Map4.BuildHas@{i} _ _ _ _ (fun _ _ => idmap) (fun _ _ => idmap)
        (fun _ _ _ => 1%path))
     (@Map4.BuildHas@{i} _ _ _ _ comap_in_map map_in_comap map_in_comapK).

Definition toParamSym@{} : Param44.Rel@{i} B A :=
  @Param44.BuildRel B A (sym_rel (graph f))
     (@Map4.BuildHas@{i} _ _ _ _ comap_in_map map_in_comap map_in_comapK)
     (@Map4.BuildHas@{i} _ _ _ _ (fun _ _ => idmap) (fun _ _ => idmap)
        (fun _ _ _ => 1%path)).

End to.

End Iso.
End Iso.
Arguments Iso.Build {A B map comap}.

(* Utility funcitons for tests *)

Definition mkParam00 {X Y : Type} : Param00.Rel X Y
  := Param00.BuildRel X Y (fun x y => True) (Map0.BuildHas X Y _) (Map0.BuildHas Y X _).

Definition mkParam10 {X Y : Type} (f : X -> Y) : Param10.Rel X Y
  := Param10.BuildRel X Y (fun x y => True) (Map1.BuildHas X Y _ f) (Map0.BuildHas Y X _).

Definition mkParam01 {X Y : Type} (f : X -> Y) : Param01.Rel Y X
  := Param01.BuildRel Y X (fun x y => True) (Map0.BuildHas Y X _) (Map1.BuildHas X Y _ f).

Definition mkParam11 {X Y : Type} (f : X -> Y) (g : Y -> X) : Param11.Rel X Y
  := Param11.BuildRel X Y (fun x y => True) (Map1.BuildHas X Y _ f) (Map1.BuildHas Y X _ g).

Definition mkParam2a0 {X Y : Type} (f : X -> Y) : Param2a0.Rel X Y
  := Param2a0.BuildRel X Y (fun x y => f x = y) (Map2a.BuildHas X Y _ f (fun _ _ e => e)) (Map0.BuildHas Y X _).

Definition mkParam2b0 {X Y : Type} (f : X -> Y) : Param2b0.Rel X Y
  := Param2b0.BuildRel X Y (fun x y => f x = y) (Map2b.BuildHas X Y _ f (fun _ _ e => e)) (Map0.BuildHas Y X _).

Definition mkParam30 {X Y : Type} (f : X -> Y) : Param30.Rel X Y
  := Param30.BuildRel X Y (fun x y => f x = y) (Map3.BuildHas X Y _ f (fun _ _ e => e) (fun _ _ e => e)) (Map0.BuildHas Y X _).
