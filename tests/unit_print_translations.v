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

Section PrintTranslations.
    Variable (A A' A'' : Type).
    Variable (B : A -> Type) (B' : A' -> Type) (B'' : A'' -> Type).
    Variable (C C' C'' : Type -> Type).
    
    Variable (RA1 : Param2a4.Rel A A').
    Variable (RA2 : Param33.Rel A A'').

    Variable (RB1 : forall a : A, forall a' : A', RA1 a a' -> Param32b.Rel (B a) (B' a')).
    Variable (RB2 : forall a : A, forall a'' : A'', RA2 a a'' -> Param14.Rel (B a) (B'' a'')).

    Variable (RC1 : forall X X' : Type, Param2a3.Rel X X' -> Param02b.Rel (C X) (C' X')).
    Variable (RC2 : forall X X'' : Type, Param2a2b.Rel X X'' -> Param43.Rel (C X) (C'' X'')).

    Trocq DB Register RA1.

    Trocq Use RA1 RA2 RB1 RB2 RC1 RC2 : RA1.
    
    Trocq Print DB *.

    Trocq Print Translations A.

    Trocq Print Translations B.

    Trocq Print Translations C.

End PrintTranslations.
