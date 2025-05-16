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

From elpi Require Import elpi.
From Trocq Require Import Param.

From Trocq.Elpi Extra Dependency "util-rocq.elpi" as util_rocq.
From Trocq.Elpi Extra Dependency "annot.elpi" as annot.
From Trocq.Elpi Extra Dependency "param-class-util.elpi" as param_class_util.
From Trocq.Elpi.constraints Extra Dependency "simple-graph.elpi" as simple_graph.
From Trocq.Elpi.constraints Extra Dependency "constraint-graph.elpi" as constraint_graph.
From Trocq.Elpi.constraints Extra Dependency "constraints.elpi" as constraints.
From Trocq.Elpi Extra Dependency "vernac.elpi" as vernac.

Elpi Command Trocq.
Elpi Accumulate Db trocq.db.
Elpi Accumulate File util_rocq.
Elpi Accumulate File annot.
Elpi Accumulate File param_class_util.
Elpi Accumulate File simple_graph.
Elpi Accumulate File constraint_graph.
Elpi Accumulate File constraints.
Elpi Accumulate File vernac.
Elpi Export Trocq.
