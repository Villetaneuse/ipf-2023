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
From Coq Require Import Rbase Classical.
Open Scope R_scope.

(** * Nombres réels 1 : la structure de corps des réels *)

(** ** Les propriétés fondamentales du corps des réels *)

(** Les nombres réels de Coq sont définis d'une certaine manière dont on ne se
    souciera pas (bon, en fait avec les coupures de Dedekind, mais ce n'est
    qu'une façon parmi d'autre de les construire et ce que nous ferons n'en
    dépend pas).

    Ce qui faut retenir est :
    - les réels forment un corps : il y a une addition et une multiplication
      qui sont telles que
      - l'addition est commutative, associative et a pour élément neutre 0
      - tout réel a un opposé
      - la multiplication est commutative, associative et a pour élément neutre 1
      - tout réel _non nul_ a un inverse
      - la multiplication est distributive sur l'addition
      - 1 et 0 sont différents
    - les réels forment un corps ordonné : il y a un ordre, noté [<], qui est
      total, compatible avec l'addition et la multiplication par un réel positif
    - les réels satisfont la propriété de la borne supérieure

    Une fois qu'on a ces propriétés, on est sûr qu'on a affaire aux réels dont
    on a l'habitude. En effet, ces propriété caractérisent entièrement les
    nombres réels, il n'y a pas d'autre corps qui a ces propriétés (par exemple
    le corps des rationnels n'a pas la propriété de la borne supérieure et le 
    corps des complexes n'est pas un corps ordonné).

    Ces propriétés sont réduites à 16 briques de bases que nous allons admettre.

    Dans ce document, on s'intéresse uniquement à la structure de _corps_ des
    réels, c'est-à-dire aux propriétés de l'addition et de la multiplication.

    Enfin, on n'hésitera pas à utiliser le tiers exclu lorsqu'on en a besoin.
*)

(** ** [R] est un corps commutatif
    
    En mathématiques, on appelle corps un ensemble muni de deux opérations,
    l'une qu'on appelle addition et note généralement [+] et l'autre appelée
    multiplication, notée généralement [*], ces deux opérations satisfaisant
    quelques propriétés (voir plus loin). *)

(** *** Addition des réels *)

(** Dans les réels de Coq, l'addition s'appelle Rplus et est notée [+] *)
Check Rplus.

(** L'addition doit être commutative, associative, et avoir un élément neutre
    noté [0] *)

Check Rplus_comm. (* commutativité, brique 1 *)
Check Rplus_assoc. (* associativité, brique 2 *)
Check Rplus_0_l. (* 0 est élément neutre à gauche, brique 3 *)

(** On en déduit facilement que [0] est aussi neutre à droite : *)
(** **** Exercice : Prouver le théorème suivant. *)
Theorem Rplus_0_r : forall (r : R), r + 0 = r.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** Un opposé d'un réel [x] est un réel [y] tel que x + y = 0.
    En fait, on peut prouver que l'opposé, quand il existe, est unique.  *)
(** **** Exercice : Prouver le théorème suivant. *)
Theorem oppose_unique : forall x y z : R, x + y = 0 /\ x + z = 0 -> y = z.
(* Avant de se lancer tête baissée, voici une preuve mathématique
   Soient x, y et z trois réels tels que
   (Hy) x + y = 0 et
   (Hz) x + z = 0.
   On veut montrer y = z.
   Il suffit de montrer y = z + 0, donc d'après Hy, de montrer
   y = z + (x + y).
   Or, z + (x + y) = (x + z) + y = 0 + y d'après Hz.
   CQFD.
*)
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** Cet opposé, étant unique, peut avoir sa propre notation et vous la
    connaissez bien sûr, l'opposé de [x] est noté [-x] et notre 4ème "brique"
    dit que tout réel en a un. *)
Check Ropp.
Check Rplus_opp_l. (* brique 4 *)

(** On en déduit facilement : *)
(** **** Exercice : Prouver le théorème suivant. *)
Theorem Rplus_opp_r : forall (r : R), r + (- r) = 0.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** On peut alors "simplifier" les équations. *)
(** **** Exercice : Prouver le théorème suivant. *)
Theorem Rplus_eq_reg_l: forall r r1 r2 : R, r + r1 = r + r2 -> r1 = r2.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** En guise d'application, une petite équation du premier degré : *)
(** **** Exercice : Prouver le théorème suivant. *)
(** Indice : attention, avec tous ces [rewrite], on a tendance à oublier que
    [apply] existe. *)
Theorem double_fixpoint_0 : forall (x : R), x + x = x -> x = 0.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** On utilise l'opposé pour définir la soustraction : *)
Print Rminus.

(** La multiplication doit également être associative, commutative 
    et avoir un élément neutre, ici, évidemment noté [1]. *)
Check Rmult_assoc. (* associativité, brique 5 *)
Check Rmult_comm. (* commutativité, brique 6 *)
Check Rmult_1_r. (* 1 est neutre à droite, brique 7 *)

(** On en déduit facilement : *)
(** **** Exercice : Prouver le théorème suivant. *)
Theorem Rmult_1_l : forall (r : R), 1 * r = r.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** De plus, la multiplication doit être distributive sur l'addition. *)
Check Rmult_plus_distr_l. (* brique 8 à gauche *)

(** On en déduit : *)
(** **** Exercice : Prouver le théorème suivant. *)
Theorem Rmult_plus_distr_r : forall (r1 r2 r3 : R), 
  (r1 + r2) * r3 = r1 * r3 + r2 * r3.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** On peut maintenant montrer que 0 est absorbant pour la multiplication. *)
(** **** Exercice : Prouver le théorème suivant. *)
Theorem Rmult_0_r : forall r : R, r * 0 = 0.
(** Avant de se lancer sur la preuve formelle, on cherche une preuve en
    mathématiques plus informelles. *)
(* Preuve mathématique (arrière):
Pour prouver r * 0 = 0, d'après, [double_fixpoint_0], il suffit de prouver que
r * 0 + r * 0 = r * 0.
Or, par distributivité, r * 0 + r * 0 = r * (0 + 0) = r * 0. CQFD. *)
Proof. (* Maintenant la preuve formelle. *)
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** Beaucoup plus facile maintenant qu'on a le premier : *)
(** **** Exercice : Prouver le théorème suivant. *)
Theorem Rmult_0_l : forall (r : R), 0 * r = 0.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** Dans un corps, 0 et 1 doivent être distincts. *)
Check R1_neq_R0. (* brique 9 *)
 
(** Et enfin tout élément x _non nul_ a un inverse.
    Cet inverse est unique (même preuve que pour l'unicité de l'opposé et c'est
    normal...) et est noté en mathématiques 1 / x, en Coq / x.*)
Check Rinv.
Check Rinv_l. (* brique 10 *)

(** On en déduit immédiatement : *)

(** **** Exercice : Prouver le théorème suivant. *)
Theorem Rinv_r : forall (r : R), r <> 0 -> r * / r = 1.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** L'existence d'un inverse permet de simplifier les produits dans les
    égalités. *)
(** **** Exercice : Prouver le théorème suivant. *)
Theorem Rmult_eq_reg_l :
  forall r r1 r2 : R, r * r1 = r * r2 -> r <> 0 -> r1 = r2.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** **** Exercice papier-crayon. *)
(** Le théorème précédent est-il encore vrai sans la condition sur [r] ?
    Si oui, le prouver, si non, trouver un contre-exemple.

*)

(** Puis on montre que pour qu'un produit soit nul, il faut qu'un de ses
    facteurs soit nuls. Mais pour ça on a besoin du théorème disant qu'on peut
    raisonner par cas sur l'égalité ou non de deux réels avec le tiers exclu. *)

(** **** Exercice : Prouver le théorème suivant. *)
Theorem Rmult_integral: forall r1 r2 : R, r1 * r2 = 0 -> r1 = 0 \/ r2 = 0.
Proof.
  (* Indice : considérer les cas r1 = 0 et r1 <> 0 avec le tiers exclu :
     [destruct (classic (r1 = 0)) as [H1 | H1]] *)
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** Maintenant, l'inverse d'un réel non nul est non nul : *)
(** **** Exercice : Prouver le théorème suivant. *)
Theorem Rinv_neq_0_compat: forall r : R, r <> 0 -> / r <> 0.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** Ce théorème a un nom barbare pour quelque chose de très simple...
    Le produit de deux réels non nuls est non nul. *)
(** **** Exercice : Prouver le théorème suivant. *)
Theorem Rmult_integral_contrapositive_currified :
  forall (r1 r2 : R), r1 <> 0 -> r2 <> 0 -> r1 * r2 <> 0.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** **** Exercice : Prouver le théorème suivant. *)
Theorem Rinv_inv' : forall (r : R), r <> 0 -> / / r = r.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


Theorem Rinv_mult' :
  forall (r1 r2 : R), r1 <> 0 -> r2 <> 0 -> / (r1 * r2) = / r2 * / r1.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** La division est définie à partir de la multiplication et de l'inverse : *)
Print Rdiv.
(** Enfin, l'inverse de (x / y) vaut (y / x) à condition que ces réels soient
    non nuls. *)
(** **** Exercice : Prouver le théorème suivant. *)
Theorem Rinv_div' :
  forall x y : R, x <> 0 -> y <> 0 -> / (x / y) = y / x.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)

