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

(** * Logique classique et principe du tiers-exclu *)
Lemma PNNP (P : Prop) : P -> ~ ~ P.
Proof. intros H1 H2. apply H2. exact H1. Qed.

(** ** L'axiome du tiers-exclus *)

(** La différence entre ce que nous avons fait en Coq et votre cours de
    mathématiques classique est que Coq n'est pas équipé par défaut du principe
    du tiers exclu qui dit qu'une proposition est soit vraie, soit fausse.
    Donc, jusqu'à présent, nous n'avons pas pu faire de preuve par l'absurde, ni
    de raisonnement par contraposition.
*)

(** Voici l'axiome du tiers-exclu :*)
Axiom classic : forall P : Prop, P \/ ~ P.

(** Attention, un axiome n'est pas un théorème. En ajoutant un axiome on prend
    le risque énorme que la théorie devienne incohérente, c'est-à-dire permette
    de prouver [False].
    Dans notre cas, un théorème difficile montre que si Coq est correct
    (c'est-à-dire ne permet pas de prouver [False]), alors il l'est encore avec
    le tiers exclu.
*)

(** ** Conséquences en logique propositionnelle *)

(** Avec cet axiome, on peut prouver, par exemple, que le raisonnement par
    l'absurde est correct. *)

Theorem NNPP : forall P : Prop, ~ ~ P -> P.
Proof.
  (* Soit P une proposition quelconque. *)
  intros P. unfold not.
  (* On suppose (hyp. (H)) que P est non contradictoire. *)
  intros H.
  (* Par le principe du tiers exclu appliqué à P, on a
     (HP) : P
     ou
     (HnP) : ~ P *)
  destruct (classic P) as [HP | HnP].
  - (* cas 1 : (HP) *)
  exact HP.
  - (* cas 2 : (HnP) *)
  (* On va ici utiliser le principe d'explosion : ce cas est contradictoire. *)
  exfalso.
  unfold not in HnP.
  apply H.
  exact HnP.
Qed.

(** Remarquer [destruct (classic P) as [HP | HnP].]. Ici,
    [classic] est un axiome qui prend une proposition en argument et 
    [(classic P)] est une preuve de [(P \/ ~P)]. Avec [destruct], on
    peut donc la détruire et faire une preuve par cas. *)

(** **** Exercice : 
    En utilisant le tiers exclu ou l'une de ses conséquences, prouver le
    théorème suivant : *)

Theorem de_morgan_not_and : forall P Q : Prop, ~ (P /\ Q) -> (~ P) \/ (~ Q).
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)

(** Remarque (voir les exercices à faire à la maison) :
    - les trois autres lois de de Morgan sont prouvables en logique intuitionniste.
    - celle-ci ne l'est pas, on a absolument besoin du tiers exclu. *)

(** **** Exercice : *)

(** En utilisant le tiers exclu ou l'une de ses conséquences, prouver le
    théorème suivant : *)

Theorem classical_imp : forall P Q : Prop, (P -> Q) <-> (Q \/ ~ P).
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)

  
(** **** Exercice : *)

(** En utilisant le tiers exclu ou l'une de ses conséquences, prouver le
    théorème suivant : *)

Theorem Peirce_law : forall P Q : Prop, ((P -> Q) -> P) -> P.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


Theorem contrapose :
  forall P Q : Prop, (~Q -> ~P) -> (P -> Q).
Proof.
  intros P Q H HP.
  apply NNPP.
  intros HnQ.
  apply H.
  - exact HnQ.
  - exact HP.
Qed.

(** ** Conséquences en calcul des prédicats *)
(** On va voir qu'en logique classique (comme dans vos cours de mathématique),
    la négation d'un "il existe" est un "pour tout" et la négation d'un
    "pour tout" est un "il existe". *)

(** Les deux prochains théorèmes n'ont pas besoin de l'axiome du tiers exclu. *)
Theorem all_not_not_ex :
  forall (U : Type) (P : U -> Prop),
  (forall n : U, ~ P n) -> ~ (exists n : U, P n).
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


Theorem ex_not_not_all :
  forall (U : Type) (P : U -> Prop),
  (exists n : U, ~ P n) -> ~ (forall n : U, P n).
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** Mais à partir d'ici, il y en a besoin. Remarquez que ce n'est pas toujours
    facile de deviner à quelle proposition il faut l'appliquer.
    Ici, il faut [destruct (classic (P n))] pour raisonner par cas sur [P n].
*)
Theorem not_ex_not_all :
  forall (U : Type) (P : U -> Prop),
  ~ (exists n : U, ~ P n) -> forall n : U, P n.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


Theorem not_ex_all_not :
  forall {U : Type} (P : U -> Prop),
  ~ (exists n : U, P n) -> forall n : U, ~ P n.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


Theorem not_all_ex_not :
  forall {U : Type} {P : U -> Prop},
  ~ (forall n : U, P n) -> exists n : U, ~ P n.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


Theorem not_all_not_ex :
  forall (U : Type) (P : U -> Prop),
  ~ (forall n : U, ~ P n) -> exists n : U, P n.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)

