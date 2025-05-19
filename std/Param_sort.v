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
From Trocq.Elpi.generation Extra Dependency "param-type.elpi" as param_type_generation.

Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Local Open Scope param_scope.

(* generate MapM_TypeNP@{i} :
    MapM.Has Type@{i} Type@{i} ParamNP.Rel@{i},
  for all N P, for M = map2a and below (above, NP is always 44)
  + symmetry MapM_Type_symNP *)

Elpi Command genmaptype.
Elpi Accumulate Db trocq.db.
Elpi Accumulate File class.
Elpi Accumulate File param_type_generation.

Elpi Query lp:{{
  map-class.all-of-kind all Classes,
  map-class.all-of-kind low LowClasses,
  std.forall LowClasses (m\
    std.forall Classes (n\
      std.forall Classes (p\
        generate-map-type m (pc n p) U L L1
      )
    )
  ).
}}.

Elpi Command genparamtype.
Elpi Accumulate Db trocq.db.
Elpi Accumulate File class.
Elpi Accumulate File param_type_generation.

Elpi Query lp:{{
  coq.univ.new U,
  coq.univ.variable U L,
  coq.univ.alg-super U U1,
  % cannot have only one binder in the declaration because this line creates a fresh level:
  coq.univ.variable U1 L1,
  map-class.all-of-kind all AllClasses,
  map-class.all-of-kind low Classes__,
  std.forall Classes__ (m\
    std.forall Classes__ (n\
      std.forall AllClasses (p\
        std.forall AllClasses (q\
          generate-param-type (pc m n) (pc p q) U L L1
        )
      )
    )
  ).
}}.

(* generate MapM_PropNP@{i} :
    MapM.Has Prop@{i} Prop@{i} ParamNP.Rel@{i},
  for all N P, for M = map2a and below (above, NP is always 44)
  + symmetry MapM_Prop_symNP *)

Elpi Command genmapprop.
Elpi Accumulate Db trocq.db.
Elpi Accumulate File class.
Elpi Accumulate File param_prop_generation.

Elpi Query lp:{{
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
