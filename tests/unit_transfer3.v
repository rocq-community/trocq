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

From Trocq Require Import Stdlib Trocq.

Set Universe Polymorphism.

Section Transfer.

    Variable (I I' : Type) (f : I' -> I) (f' : I -> I').

    Definition Rf := mkParam2a0 f.
    Trocq Use Rf.
    Definition Rf' := mkParam2a0 f'.
    Trocq Use Rf'.

    Variable (pe : I -> I -> Prop) (pe' : I' -> I' -> Prop).
    Definition Rpe (m : I) (m' : I') (rm : (Rf') m m')
        (n : I) (n' : I') (rn : (Rf') n n')
        : Param2a1.Rel (pe n m) (pe' n' m').
        admit.
    Admitted.
    Trocq Use Rpe.

    Variable (p : I -> I -> I) (p' : I' -> I' -> I').

    Definition Rg (m : I) (m' : I') (rm : (Rf) m' m)
        (n : I) (n' : I') (rn : (Rf) n' n)
        : (Rf') (p n m) (p' n' m').
        admit.
    Admitted.
    Trocq Use Rg.

    Goal forall m : I, forall n : I, pe m (p n n) -> pe m n.
        trocq.
        enough (forall m' : I', forall n' : I', pe' m' (p' n' n') -> pe' m' n') by exact x.
    Abort.

End Transfer.
