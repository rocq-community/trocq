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
From Trocq Require Import Trocq.
From Trocq.Elpi Extra Dependency "util-rocq.elpi" as util_rocq.

Elpi Command Test.
Elpi Accumulate File util_rocq.
Elpi Accumulate lp:{{

main _ :- std.spy-do! [
  util.uvar-to-evar UVar1 EVar1_,
  var EVar1_,
  util.uvar-to-evar UVar1 EVar1',
  var EVar1',
  % When called on the same uvar, the same Rocq evar is returned
  same_term EVar1_ EVar1',

  util.uvar-to-evar UVar2_ EVar2_,
  var EVar2_,
  % But when called on a different uvar, a different Rocq evar is returned
  not (same_term EVar1_ EVar2_),

  % Assigning to a uvar should not assign the evar
  UVar1 = 2,
  var Evar1_,

  % Calling uvar-to-evar on something else than a uvar raises an error
  do-not-fail => not (util.uvar-to-evar 2 Evar3_),
].

}}.

Elpi Test.