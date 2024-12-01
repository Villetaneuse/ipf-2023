(* begin hide *)
(*
  This file is part of the "Initiation aux preuves formelles" course in
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

Set Keyed Unification. (* rewrite plus prévisible *)
From Coq Require PeanoNat.
Import PeanoNat.Nat.

(** * Exercices supplémentaires sur les entiers naturels *)

(** Pour résoudre ces exercices, vous pouvez utiliser les théorèmes suivants
    (déjà prouvés dans Naturels) :
    - [add_0_l : ∀ n : nat, 0 + n = n]
    - [add_0_r : ∀ n : nat, n + 0 = n]
    - [add_1_l : ∀ n : nat, 1 + n = S n]
    - [add_1_r : ∀ n : nat, n + 1 = S n]
    - [add_succ_l : ∀ n m : nat, S n + m = S (n + m)]
    - [add_succ_r : ∀ n m : nat, n + S m = S (n + m)]
    - [add_comm : ∀ n m : nat, n + m = m + n]
    - [add_assoc : ∀ n m p : nat, n + (m + p) = (n + m) + p]
    - [mul_0_l : ∀ n : nat, 0 * n = 0]
    - [mul_0_r : ∀ n : nat, n * 0 = 0]
    - [mul_1_l : ∀ n : nat, 1 * n = n]
    - [mul_1_r : ∀ n : nat, n * 1 = n]
    - [mul_succ_l : ∀ n m : nat, S n * m = n * m + m]
    - [mul_succ_r : ∀ n m : nat, n * S m = n * m + n]
    - [mul_comm : ∀ n m : nat, n * m = m * n]
    ainsi, bien sûr, que les théorèmes prouvés précédemment dans ce sujet.

    Pour vous souvenir de l'énoncé, vous pouvez utiliser la commande [Check].
*)
Check mul_comm.
(** **** Exercice : Prouver le théorème suivant.

    Indice pour le sens direct :
    faire une preuve par cas sur la nullité ou non de [n] ou de [m] (utiliser
    la tactique [destruct]).
*)
Theorem mul_eq_0 : forall (n m : nat), n * m = 0 <-> n = 0 \/ m = 0.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** **** Exercice : Prouver le théorème suivant. *)
Theorem mul_add_distr_r : forall n m p : nat, (n + m) * p = n * p + m * p.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** **** Exercice : Prouver le théorème suivant, sans induction. *)
(** Utiliser [rewrite] et les théorèmes précédents. *)
Theorem mul_add_distr_l : forall n m p : nat, n * (m + p) = n * m + n * p.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** **** Exercice : Prouver le théorème suivant. *)
Theorem mul_assoc : forall n m p : nat, (n * m) * p = n * (m * p).
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)

