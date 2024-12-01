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
From Coq Require Import Rbase.
Open Scope R_scope.

(** * Nombre réels 2 : les réels comme corps ordonné *)

(** ** Ordre total strict < *)

(** Une des choses qui distinguent R de l'ensemble des nombres complexes par
    exemple est qu'il dispose d'une relation d'ordre strict [<] qui est totale
    (ça veut dire qu'on peut toujours comparer deux réels) et compatible avec
    l'addition et la multiplication par un nombre positif.

    Comme dans RCorps, il y a certaines propriétés qu'on suppose acquise par
    construction qu'on appellera "Briques" et que vous pouvez considérer
    comme des axiomes.

    L'ordre "inférieur strictement", noté [<] est appelé [Rlt] dans la
    bibliothèque standard ("lt" pour "less than").
*)

(** Une relation d'ordre strict est par définition asymétrique : *)
Check Rlt_asym. (* Brique 11 *)
(** Une conséquence directe et importante est l'irréflexivité : *)
(** **** Exercice : Prouver le théorème suivant. *)
Theorem Rlt_irrefl : forall (x : R), ~(x < x).
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)

(** Une relation d'ordre strict est par définition transitive : *)
Check Rlt_trans. (* Brique 12 *)
(** Noter qu'en général, coq ne peut pas deviner avec quel [r2]
  (valeur "du milieu") appliquer la transitivité, alors que pour le [r1] et le
  [r3] (valeurs "au bord"), il sait souvent le faire.

  Donc, le plus souvent, pour prouver une inégalité par transitivité, ça donne
  [apply (Rlt_trans _ bidule)].
  avec [bidule] à remplacer.

  Voici une petite application (à but purement pédagogique) :
*)
(** **** Exercice : Prouver le théorème suivant. *)
Theorem exercice_trans :
  forall x y z, x < y -> y < z -> z < x -> False.
Proof.
  (* Indication : pour prouver False, il suffit de prouver x < x *)
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** On pourrait munir R d'une infinité de relations d'ordre strict. Mais ce qui
    rend vraiment l'ordre usuel unique est qu'il est compatible avec
    l'addition et la multiplication par un nombre strictement positif. *)

(** On suppose maintenant acquis (Brique 13) que la construction des réels
    fournit la compatibilité avec l'addition à gauche :*)
Check Rplus_lt_compat_l. (* Brique 13 *)

(** **** Exercice : Prouver le théorème suivant. *)
Theorem Rplus_lt_compat_r : forall r r1 r2, r1 < r2 -> r1 + r < r2 + r.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** **** Exercice : Prouver le théorème suivant. *)
Theorem Rplus_lt_reg_l : forall r r1 r2 : R, r + r1 < r + r2 -> r1 < r2.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** **** Exercice : Prouver le théorème suivant. *)
Theorem Ropp_lt_contravar : forall r1 r2 : R, r2 < r1 -> - r1 < - r2.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** Ensuite, passons à la compatibilité avec la multiplication par un réel
    positif. *)
Check Rmult_lt_compat_l. (* Brique 14 *)

(** **** Exercice : Prouver le théorème suivant. *)
Theorem Rmult_lt_compat_r :
  forall r r1 r2, 0 < r -> r1 < r2 -> r1 * r < r2 * r.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** Certaines propriétés font intervenir [>] mais [y > x] est la même chose que
    [x < y]. *)
Print Rgt. (* gt pour "greater than", supérieur à *)

(** Pour s'en convaincre, voir l'exemble suivant : *)
Theorem Rgt_lt : forall r1 r2, r1 > r2 -> r2 < r1.
Proof.
  intros r1 r2 H.
  (* En fait, le type de H est _convertible_ avec celui du but, il n'y a
     même pas besoin d'unfold
     (mais rien ne vous interdit d'unfold si vous voulez). *)
  exact H.
Qed.

(** **** Exercice : Prouver le théorème suivant. *)
Theorem Rmult_gt_0_compat :
  forall r1 r2 : R, r1 > 0 -> r2 > 0 -> r1 * r2 > 0.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)

(** On peut multiplier des inégalités entres elles, sous conditions de
   positivité. *)
(** **** Exercice : Prouver le théorème suivant. *)
Theorem Rmult_gt_0_lt_compat : forall r1 r2 r3 r4,
  r3 > 0 -> r2 > 0 -> r1 < r2 -> r3 < r4 -> r1 * r3 < r2 * r4.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** La dernière propriété que l'on admet sur l'ordre [<] est
    que c'est un ordre total (brique 15) : pour deux réels
    x et y, on a 
    soit [x < y]
    soit [x = y]
    soit [y < x].
*)
    
Check Rtotal_order. (* Brique 15 *)

(** ** Ordre non strict [<=] *)

(** L'ordre [<=] (inférieur ou égal) est défini très simplement de la façon
   suivante : *)

Print Rle. (* le pour "less or equal to" *)

(** Quelques exercices rapides : penser à [unfold Rle]. *)

(** **** Exercice : Prouver le théorème suivant. *)
(** L'ordre non strict est (comme tous les ordres non stricts) réflexif : *)
Theorem Rle_refl : forall r, r <= r.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** **** Exercice : Prouver le théorème suivant. *)
Theorem Rlt_or_le : forall r1 r2 : R, r1 < r2 \/ r2 <= r1.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** **** Exercice : Prouver le théorème suivant. *)
Theorem Rlt_le : forall r1 r2, r1 < r2 -> r1 <= r2.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** L'ordre [<=] est aussi (comme tous les ordres non stricts) antisymétrique :
*)
(** **** Exercice : Prouver le théorème suivant. *)
Theorem Rle_antisym : forall r1 r2 : R, r1 <= r2 -> r2 <= r1 -> r1 = r2.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** Enfin, l'ordre [<=] est transitif. *)
(** **** Exercice : Prouver le théorème suivant. *)
Theorem Rle_trans : forall r1 r2 r3, r1 <= r2 -> r2 <= r3 -> r1 <= r3.
Proof.
  intros r1 r2 r3 [H1 | H1].
  - intros [H2 | H2].
    + left; apply (Rlt_trans _ r2).
      * exact H1.
      * exact H2.
    + rewrite <-H2. left. exact H1.
  - intros H2. rewrite H1. exact H2.
Qed.

(** **** Exercice : Prouver le théorème suivant. *)
Theorem Rle_lt_trans : forall r1 r2 r3 : R, r1 <= r2 -> r2 < r3 -> r1 < r3.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** ** Tous les carrés sont positifs *)

(** Le but de cette partie est de montrer que tous les carrés sont positifs.
    Cela va faire intervenir une bonne partie des résultats précédents. *) 

(** Le carré d'un réel [x] est noté [x²]. La fonction associée est Rsqr ("sqr"
    pour "square" qui signifie carré en anglais). *)
Print Rsqr. (* Nom de la fonction *)

(** Un petit exemple en fait bien utile : *)
Theorem Rsqr_mult_diag : forall r, r² = r * r.
Proof.
  intros r. unfold Rsqr. reflexivity.
Qed.

(** On a besoin d'un certain nombre de résultats intermédiaires. *)
(** **** Exercice : Prouver le théorème suivant. *)
Theorem Ropp_involutive : forall r : R, - - r = r.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** **** Exercice : Prouver le théorème suivant. *)
Theorem Ropp_mult_distr_r : forall r1 r2 : R, - (r1 * r2) = r1 * - r2.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** **** Exercice : Prouver le théorème suivant. *)
Theorem Rmult_opp_opp : forall r1 r2 : R, - r1 * - r2 = r1 * r2.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** **** Exercice : Prouver le théorème suivant. *)
Theorem Rle_0_sqr: forall r : R, 0 <= r².
Proof.
  (* Indice : unfold Rsqr et raisonner par cas sur l'ordre entre 0 et r. *)
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** Comme jolie et importante application : 1 est plus grand que 0 :D *)
(** C'est l'occasion d'introduire une nouvelle tactique et un petit théorème
    utile. *)
(** Le théorème [eq_sym] permet, avec [apply] de changer le sens d'une égalité.
*)

Theorem eq_sym : forall (A : Type) (x y : A), x = y -> y = x.
Proof.
  intros A x y H. rewrite H. reflexivity.
Qed.

(** La tactique [assert] permet (dans cet ordre)
    1. d'énoncer une nouvelle hypothèse
    2. de la prouver dans le contexte actuel
    3. de l'utiliser dans la suite de la preuve.

    Elle est typique du raisonnement "vers l'avant" souvent utilisé
    en mathématiques.

    Voici un exemple idiot. *)

Theorem exemple_assert : forall x y, 3 <= x -> x <= 3 -> y = 3 -> x = y.
Proof.
  intros x y H1 H2 H3.
  assert (x = 3) as H. {
    (* preuve de l'assertion *)
    apply Rle_antisym.
    - exact H2.
    - exact H1.
  }
  (* suite de la preuve : on peut utiliser H *)
  rewrite H.
  apply eq_sym.
  exact H3.
Qed.

Theorem Rlt_0_1: 0 < 1.
Proof.
  (* Indice : 1 est un carré, et la propriété [R1_neq_R0] dit que 1 n'est pas
     égal à 0. *)
  (* On commence par prouver que [0 <= 1]. *)
  assert (0 <= 1) as I.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)

Close Scope R_scope.
