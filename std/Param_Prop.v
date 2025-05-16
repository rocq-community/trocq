(*****************************************************************************)
(*                            *                    Trocq                     *)
(*  _______                   *           Copyright (C) 2023 MERCE           *)
(* |__   __|                  *    (Mitsubishi Electric R&D Centre Europe)   *)
(*    | |_ __ ___   ___ __ _  *       Cyril Cohen <cyril.cohen@inria.fr>     *)
(*    | | '__/ _ \ / __/ _` | *       Enzo Crance <enzo.crance@inria.fr>     *)
(*    | | | | (_) | (_| (_| | *   Assia Mahboubi <assia.mahboubi@inria.fr>   *)
(*    |_|_|  \___/ \___\__, | ************************************************)
(*                        | | * This file is distributed under the terms of  *)
(*                        |_| * GNU Lesser General Public License Version 3  *)
(*                            * see LICENSE file for the text of the license *)
(*****************************************************************************)

From elpi Require Import elpi.
Require Import ssreflect.
Require Import Stdlib Hierarchy Database.

From Trocq.Elpi Extra Dependency "class.elpi" as class.
From Trocq.Elpi.generation Extra Dependency "param-prop.elpi" as param_prop_generation.

Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Local Open Scope param_scope.

(* generate MapM_PropNP@{i} :
    MapM.Has Prop@{i} Prop@{i} ParamNP.Rel@{i},
  for all N P, for M = map2a and below (above, NP is always 44)
  + symmetry MapM_Prop_symNP *)

Elpi Command genmapprop.
Elpi Accumulate Db trocq.db.
Elpi Accumulate File class.
Elpi Accumulate File param_prop_generation.

Elpi Query lp:{{
  % cannot have only one binder in the declaration because this line creates a fresh level:
  map-class.all-of-kind all Classes,
  map-class.all-of-kind low LowClasses,
  std.forall LowClasses (m\
    std.forall Classes (n\
      std.forall Classes (p\
        generate-map-prop m (pc n p)
      )
    )
  ).
}}.
