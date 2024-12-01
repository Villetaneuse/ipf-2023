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
From Coq Require Import Rbase Rfunctions.
Open Scope R_scope.

(** * Nombres réels 3 : La valeur absolue et la distance sur les réels *)

(** On introduit dans ce sujet les nouveaux ingrédients fondamentaux pour
    l'analyse que sont la valeur absolue sur R et la distance sur R. *)

(** ** La valeur absolue : [Rabs] *)
(** Vous connaissez certainement la valeur absolue.
    Dans un cours de mathématiques, la valeur absolue d'un réel x est le réel
    noté |x| défini par :
    |x| = -x  si x < 0
          x si x >= 0.
*)
(** En fait il y a certainement mille façon de définir la valeur absolue, mais
    ce qui importe ici, c'est que cette fonction s'appelle [Rabs] et qu'on admet
    les deux théorèmes suivants : *)
Check Rabs_pos_eq.
Check Rabs_left.

(** Pour prouver des choses sur Rabs, le plus souvent on raisonne par cas.
    Voici un exemple important :
    remarquer [(Rlt_or_le x 0) : x < 0 \/ 0 <= x]. *)

Theorem Rabs_pos : forall x : R, 0 <= Rabs x.
Proof.
  intros x.
  destruct (Rlt_or_le x 0) as [I | I].
  - (* x < 0 *)
    left.
    rewrite Rabs_left.
    (* On utilise le fait que l'opposé est une fonction strictement
       décroissante. *)
    + rewrite <-Ropp_0.
      apply Ropp_lt_contravar.
      exact I.
    + exact I.
  - (* 0 <= x *)
    rewrite Rabs_pos_eq by (exact I). exact I.
Qed.

(** Deux remarques importantes sur la preuve précédente :
    - Nous avons utilisé [rewrite] avec un énoncé du type :
      [x < 0 -> Rabs x = - x].

      Ce qui se passe alors est :
      - dans le but, [Rabs x] est remplacé par [-x];
      - vous continuez votre preuve;
      - à la fin, Coq vous demande de prouver que [x < 0].
    - la deuxième fois on a fourni directment la preuve que [0 <= x] avec

      [rewrite Rabs_pos_eq by (exact I)].
*)

(** La preuve de x < 0 -> 0 < -x va nous servir souvent, en fait c'est : *)
(** **** Exercice : Prouver le théorème suivant. *)
Theorem Ropp_gt_lt_0_contravar : forall r : R, r < 0 -> - r > 0.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** **** Exercice : Prouver le théorème suivant. *)
Theorem Rle_abs : forall x : R, x <= Rabs x.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** **** Exercice : Prouver le théorème suivant. *)
Theorem Rabs_R0 : Rabs 0 = 0.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** ** Petit détour par la fonction carré *)

(** La fonction carré s'appelle [Rsqr] dans la bibliothèque [Reals]. Le carré
    d'un réel [x] est noté [x²].
    Le plus simple est encore d'utiliser [unfold Rsqr].
*)

(** **** Exercice : Prouver le théorème suivant. *)
Theorem Rsqr_neg (x : R) : x² = (- x)².
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** **** Exercice : Prouver le théorème suivant. *)
(** Indications : *)
Check Rmult_gt_0_lt_compat.
Check Rmult_gt_0_compat.
Theorem Rsqr_incrst_1 : forall x y : R, x < y -> 0 <= x -> 0 <= y -> x² < y².
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** **** Exercice : Prouver le théorème suivant. *)
(** La fonction carré est injective sur les réels positifs. *)
Theorem Rsqr_inj : forall x y : R, 0 <= x -> 0 <= y -> x² = y² -> x = y.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** Valeur absolue et carré *)

(** **** Exercice : Prouver le théorème suivant. *)
(** On se souvient qu'un carré est toujours positif : *)
Check Rle_0_sqr.
(** et que le carré est invariant par opposé : *)
Check Rsqr_neg.
Theorem Rabs_sqr (x : R) : Rabs (x²) = (Rabs x)².
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** **** Exercice : Prouver le théorème suivant. *)
Theorem Rabs_Ropp : forall x : R, Rabs (- x) = Rabs x.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** Pour le prochain exercice, il y a deux stratégies différentes :
    - séparer en 4 cas suivant le signe de x et de y
    - ou bien passer par la fonction carré
*)
(** Dans ma solution, j'utilise : *)
Check Rmult_le_pos.
Check Rsqr_mult.
(** mais ce n'est pas obligé. *)
(** **** Exercice : Prouver le théorème suivant. *)
Theorem Rabs_mult : forall x y : R, Rabs (x * y) = Rabs x * Rabs y.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** Dans le prochain exercice, et les suivants, vous pourrez utiliser : *)
Check double.
(** **** Exercice : Prouver le théorème suivant. *)
(** Bon... celui-ci est assez pénible à la main, vous avez le droit de le
    passer. *)
Theorem Rsqr_plus: forall x y : R, (x + y)² = x² + y² + 2 * x * y.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** Ici, vous pourrez utiliser : *)
Check Rlt_0_2.
Check Rsqr_incr_0_var.
Check Rplus_le_compat.
(** **** Exercice : Prouver le théorème suivant. *)
Theorem Rabs_triang : forall a b, Rabs (a + b) <= Rabs a + Rabs b.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** ** Distance usuelle sur les réels *)

(** La distance usuelle sur R est notée Rdist dans cette bibliothèque. *)
Print Rdist.
(** Dans un cours de mathématique, elle est définie par
    d(x, y) = |y - x|. *)

(** Remarque culturelle au passage : généralement, en mathématiques, une
    distance sur un ensemble E est une fonction d de E * E dans l'ensemble des
    réels positifs ou nuls qui satisfait :
    - symétrie : d(x, y) = d(y, x)
    - séparation : d(x, y) = 0 <-> x = y
    - inégalité triangulaire : d(x, z) <= d(x, y) + d(y, x).
*)

(** Nous concluons cette partie par une preuve de ces faits. *)

(** **** Exercice : Prouver le théorème suivant. *)
(** Ici, c'est juste [Reals] qui nous embête avec [>=].

    Pour passer de [<=] à [>=] facilement (et réciproquement), on a: *)
Check Rle_ge.
Check Rge_le.
Theorem Rdist_pos (x y : R) : Rdist x y >= 0.
Proof.
  (** Penser à [unfold Rdist] *)
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** **** Exercice : Prouver le théorème suivant. *)
Theorem Rdist_sym (x y : R) : Rdist x y = Rdist y x.
Proof.
  (** Penser à [unfold Rdist] et [unfold Rminus] *)
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** Pour faciliter la preuve de la réflexivité, on a : *)
(** **** Exercice : Prouver le théorème suivant. *)
Theorem Rabs_eq_0 : forall x, Rabs x = 0 <-> x = 0.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** **** Exercice : Prouver le théorème suivant. *)
Theorem Rdist_refl (x y : R) : Rdist x y = 0 <-> x = y.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** **** Exercice : Prouver le théorème suivant. *)
(** Vous pourrez utiliser la tactique [replace] *)
(** La tactique [replace A with B] remplace tous les A par B dans le but
    puis vous demande de prouver que [A = B]. *)
Theorem Rdist_tri : forall x y z : R, Rdist x y <= Rdist x z + Rdist z y.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


Close Scope R_scope.
