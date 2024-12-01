(* begin hide *)
(*
This file is part of the "Initiation aux preuves formelles " course in
Villetaneuse, France.

Copyright (C) Kerjean, Mayero, Rousselin

This library is free software; you can redistribute it and/or
modify it under the terms of the GNU Lesser General Public
License as published by the Free Software Foundation; either
version 3 of the License, or (at your option) any later version.

This library is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
COPYING file for more details.
*)
(* end hide *)
From Coq Require Import PeanoNat.
Import Nat.

Section ExercicesPredicat.

(** Dans cette section on étudie les prédicats à deux variables. *)
Context {X Y : Type} (R : X -> Y -> Prop).
  
(** **** Exercice : Un raisonnement valide et un autre qui ne l'est pas. *)

Theorem exists_forall :
  (exists x, forall y, R x y) -> (forall y, exists x, R x y).
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** L'implication inverse est fausse :
    - si une personne est amie avec tout le monde, alors tout le monde a au
      moins un ami ;
    - mais même si tout le monde a au moins un ami, ça ne signifie pas qu'une
      personne est amie avec tout le monde.
*)

(** Allez, il nous faut un contre-exemple formel ! *)
(** On va dire que deux entiers naturels sont "liés" si l'un est le successeur
    de l'autre. En gros, un entier naturel est ami avec son successeur et son
    prédécesseur. *)
Definition linked_nat (n n' : nat) := (n' = S n) \/ (n = S n').

(** La conclusion du théorème précédent est vraie : *)

(** **** Exercice : Prouver le théorème suivant. *)
Theorem all_nats_linked_to_a_nat :
  forall (n' : nat), (exists (n : nat), (linked_nat n n')).
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** Mais pas son hypothèse : *)

(** **** Exercice : Prouver le théorème suivant. *)
(** indice : à un moment, il faut spécialiser une hypothèse avec deux valeurs
    différentes bien choisies. *)
Theorem not_all_nat_linked_to_same_nat :
  ~(exists n, (forall n', (linked_nat n n'))).
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** Par contre, on peut échanger l'ordre de plusieurs connecteurs [forall]
    consécutifs. *)
Theorem forall_forall :
  (forall x, (forall y, R x y)) -> (forall y, (forall x, R x y)).
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** Ou bien de plusieurs connecteurs [exists] consécutifs. *)
Theorem exists_exists :
  (exists x, (exists y, R x y)) -> (exists y, (exists x, R x y)).
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


End ExercicesPredicat.

Section Multiples.

(** **** Exercice : Tous les multiples de (a * b) sont multiples de a. *)
Definition incl {A : Type} (E F : A -> Prop) := forall (a : A), (E a -> F a).
Definition multiple_de (k : nat) (n : nat) := exists m, n = k * m.

(* Prouver le théorème suivant.
   Vous pouvez utiliser le théorème suivant : *)
Check mul_assoc.
Theorem mult_a_b_mult_a (a b : nat) :
  incl (multiple_de (a * b)) (multiple_de a).
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** **** Exercice plus difficile :
         Tous les multiples de 2 ne sont pas multiples de 4. *)

(* On commence par montrer que 2 est multiple de 2. *)
Theorem mult_2_2 : multiple_de 2 2.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(* Ensuite une formule sur la multiplication par 4. *)
Theorem mul_4_S : 
  forall (n : nat), 4 * (S n) = 4 + 4 * n.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(* Enfin que 2 n'est pas multiple de 4. *)
Theorem nmult_4_2 : ~multiple_de 4 2.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


Theorem non_mul_4_2 : ~ (incl (multiple_de 2) (multiple_de 4)).
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


End Multiples.
