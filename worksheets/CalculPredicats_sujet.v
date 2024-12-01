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
From Coq Require Import PeanoNat.
Import Nat.

(** * Calcul des prédicats *)

(** Ce sujet contient trois parties :
    - La première reprend et approfondit le travail entamé sur le quantificateur
      universel [forall].
    - La seconde introduit le quantificateur existentiel [exists], ainsi que les
      tactiques nécessaires pour _utiliser_ une hypothèse ainsi quantifiée
      ([destruct] comme toujours...) et pour _prouver_ ou introduire
      une formule du type « il existe ... ».
    - La troisième fait travailler sur les notions importantes de surjectivité
      et d'injectivité.
*)

(** ** Prédicats et connecteur [forall] *)

Section Forall.

(** Un prédicat sur un certain type [X] est une fonction de [X] vers [Prop],
    donc une proposition qui dépend d'une variable à valeur dans un certain 
    type.

    Par exemple, on peut définir le prédicat [est_pair : nat -> Prop] qui est
    satisfait uniquement par les entiers naturels pairs.

    On peut donc voir un prédicat comme une certaine propriété des éléments
    d'un type.

    Comme premier prédicat très simple, définissons [est_nul] sur [nat].
*)

Definition est_nul : nat -> Prop := fun n => n = 0.

(** Bien sûr on prouve facilement que [0] est nul : *)
Theorem est_nul_0 : est_nul 0.
Proof.
  unfold est_nul.
  reflexivity.
Qed.

(** On peut même aller plus loin : *)
Theorem est_nul_carac : forall (n : nat), (est_nul n <-> n = 0).
Proof.
  intros n. split.
  - intros H.
    unfold est_nul in H.
    exact H.
  - intros H.
    rewrite H.
    exact est_nul_0.
Qed.

(** **** Exercice : Prouver le théorème suivant. *)
(** N'oubliez pas [discriminate H], si H est est une preuve d'un égalité
    fausse. *)
Theorem non_est_nul_S : forall (n : nat), ~(est_nul (S n)).
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** On se donne maintenant un type abstrait, noté [X] (penser, par exemple
    au type [nat]) et deux prédicats sur [X]. *)
Context {X : Type} (P : X -> Prop) (Q : X -> Prop).

(** Le quantificateur « pour tout » s'écrit [forall] ou [forall] en Coq :
    [forall x : X, P x]
    est la proposition qui dit que pour tout [x] de type [X], la proposition
    [P x] est vraie.
    Avec le point de vue « prédicat », cela signifie qu'une certaine propriété
    est satisfaite par tous les habitants d'un type.
*)
(** L'énoncé [forall x : X, (P x)] est encore une proposition. *)
Check (forall x : X, (P x)).

(** La tactique [specialize] n'est jamais indispensable mais souvent pratique.
    L'idée est de fournir des arguments à une hypothèse universellement 
    quantifiée de façon à en avoir une version spécialisée.

    On peut voir [specialize] comme la tactique qui "utilise le [forall]".

    Voyons tout de suite des exemples :
*)

Lemma specialize_example_1 (R : nat -> Prop) :
  (forall (n : nat), R n) -> R 0.
Proof.
  intros H.
  specialize (H 0). (* remarquer que l'ancien H général a disparu *)
  exact H.
Qed.

Lemma specialize_example_2 (R : nat -> Prop) :
  (forall (n : nat), R n) -> (R 1 /\ R 2).
Proof.
  intros H.
  specialize (H 1) as K. (* avec "as" la version générale ne disparaît plus *)
  specialize (H 2). (* sans elle a disparu *)
  split.
  - exact K.
  - exact H.
Qed.

(** On peut utiliser des "intro patterns" dans la partie "as ..." *)
Lemma specialize_example_3 (R : nat -> Prop) :
  (forall (n : nat), (R n \/ R (S n))) -> (R 1 \/ R 2).
Proof.
  intros H.
  specialize (H 1) as [K | L].
  - left. exact K.
  - right. exact L.
Qed.

(** Un exemple de tautologie du calcul des prédicats est le suivant. *)
(** **** Exercice : Prouver le théorème suivant. *)

Theorem forall_and_forall :
  (forall x : X, P x) /\ (forall y : X, Q y) <-> (forall x, (P x /\ Q x)).
Proof.
  (* Indice pour le sens réciproque : penser à spécialiser avant de [destruct]. *)
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** Il faudrait vraiment connaître et comprendre intuitivement le théorème
    précédent. En fait, on peut voir le quantificateur [forall] comme
    _une généralisation du [/\]_.

    Par exemple, pour un prédicat [P : nat -> Prop], dire que
    [forall n : nat, (P n)] signifie qu'on a
    [(P 0) /\ (P 1) /\ (P 2) /\ (P 3) /\ ...]
*)

(** Avec la disjonction, en revanche, les choses sont différentes. *)

(** **** Exercice : Prouver le théorème suivant. *)
(** Prenez bien le temps de comprendre l'énoncé de façon intuitive avant de
    commencer la preuve. *)
Theorem forall_or_forall :
  (forall x, (P x)) \/ (forall x, (Q x)) -> forall x, (P x \/ Q x).
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** La réciproque est-elle vraie ?
    Non, et c'est très important que vous le compreniez.

    Dans un premier temps, on peut essayer de voir ce qui bloque dans la
    preuve.
*)

(** **** Exercice : essayer d'avancer dans la preuve du théorème suivant. *)

(** Voir où vous êtes bloqué et pourquoi. Laisser [Abort.] (abandonner) à la
    fin, le théorème est faux de toute façon. *)

Theorem forall_p_or_q_false :
  forall x, (P x \/ Q x) -> (forall x : X, P x) \/ (forall y : X, Q y).
Proof.
Abort. (* Abandonner la preuve (le théorème est faux de toute façon). *)

(** Dans un second temps, c'est important de se convaincre que c'est faux
    avec un contre-exemple.

    Pour le type [X], on va prendre [nat], pour [P], notre prédicat
    [est_nul] et pour [Q] un nouveau prédicat [est_non_nul].
*)

Definition est_non_nul : nat -> Prop := (fun n => ~(n = 0)).

(** La prémisse du faux théorème précédent est bien sûr satisfaite. *)

(** **** Exercice : Prouver le théorème suivant. *)
Theorem nul_ou_non_nul : forall n, (est_nul n \/ est_non_nul n).
Proof.
  (* Penser à faire une preuve par cas sur [n] avec [destruct]. *)
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** Mais sa conclusion est fausse. *)
(** **** Exercice : Prouver le théorème suivant. *)
(** Indices : 
    - dans le premier cas, vous aurez à trouver une contradiction
      depuis une hypothèse du type [H1 : forall (n : nat), n = 0].
      Vous pouvez spécialiser cette hypothèse avant d'utiliser [discriminate].
    - dans l'autre cas, vous aurez à prouver [False] en utilisant une 
      hypothèse du type [H2 : forall (n : nat), n = 0 -> False].
      Encore une fois, vous pouvez spécialiser cette hypothèse.
*)
Theorem non_tous_nul_ou_non_nul :
  ~((forall n, est_nul n) \/ (forall n, est_non_nul n)).
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** Vous devriez vraiment vous arrêter deux minutes pour bien noter qu'en
    général il est FAUX que 
    [(forall x, (P x \/ Q x)) -> (forall x, P x) \/ (forall x, Q x)].
    et noter le contre-exemple.
*)

End Forall.

(** ** Le quantificateur [exists] *)

Section Exists.

(** Le quantificateur « il existe » s'écrit [exists] 
    ou [exists] dans des mathématiques en Coq.
    Il se lit « il existe » : [exists x : X, P x] est la proposition qui dit
    qu'il y a (au moins) un [x] de type [X] tel que la proposition [P x]
    est vraie.
*)

(** *** Prouver un "il existe" : la tactique [exists] *)

(** En logique intuitionniste, pour prouver une proposition du type
    « il existe un élément ayant telle propriété »,
    la seule possibilité est
    _d'exhiber un tel élément_ (appelé témoin). La tactique [exists], suivie de
    ce témoin pressenti permet d'éliminer le quantificateur [exists]. *)

Theorem exists_n_p_3_eq_8 : exists n : nat, n + 3 = 8.
Proof.
  (** Pour montrer qu'il existe [n] tel que [n + 3 = 8],
      _il suffit_ de montrer que [5 + 3 = 8]
      (c'est une intuition géniale qui m'a fait penser à [5]). *)
  exists 5.
  (* Par définition de [+], [5 + 3 = 8]. *)
  simpl.
  (* Les deux membres de l'égalité sont les mêmes, la preuve est terminée. *)
  reflexivity.
Qed.

(** **** Exercice : Prouver le théorème suivant. *)
Theorem exists_double_eq : exists (n : nat), n + n = n.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** *** Quelques tautologies (ou non) avec [exists]. *)

(** On se donne de nouveau un type [X] quelconque et deux prédicats
    sur [X]. *)
Context {X : Type} (P : X -> Prop) (Q : X -> Prop).

(** La formule [exists x, P x] est encore de type [Prop]. *)
Check (exists x, P x).

(** Pour un type habité (c'est-à-dire ayant au moins un élément), on a le
    résultat très intuitif suivant.  *)
Lemma forall_imp_exists :
  forall y : X, (forall x : X, P x) -> (exists x, P x).
Proof.
  (* Soit [y] de type [X] (ça n'a l'air de rien, mais on est en train de
     supposer que [X] a au moins un élément). *)
  intros y.
  (* On suppose (hypothèse ([H])) que tout [x] de type [X] satisfait [P]. *)
  intros H.
  (* On doit exhiber un témoin. On n'a que [y] sous la main. *)
  exists y.
  (* D'après ([H]) appliquée à [y], on a bien [P y]. *)
  exact (H y).
Qed.

(** **** Exercice : Prouver le théorème suivant. *)
Lemma nat_0_ou_S : forall n : nat, n = 0 \/ (exists k : nat, n = S k).
Proof.
  (* Indice: faire une preuve par cas sur la nullité de [n]. *)
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** Attention, une erreur très courante en mathématiques (ou même dans la
    logique de tous les jours) consiste à penser qu'avec un ou quelques exemples
    (donc des preuves de « il existe »), on montre « pour tout » :
    - Le polynôme [X^2 - 4] a des racines réelles donc tous les polynômes en ont.
    - Les entiers impairs 3, 5 et 7 sont premiers donc tous les nombres impairs
      le sont.
    - Cet étudiant est nul en maths, la preuve, il a eu 3 au dernier contrôle.
    - Beaucoup d'autres exemples sortent constamment de la bouche des dirigeants
      politiques...
*)

(** *** Utiliser un « il existe » : tactique [destruct] *)

(** Pour utiliser une proposition avec [exists], on utilise de nouveau
    la tactique [destruct]. Noter la syntaxe [as [y H]], où y est la
    variable pour laquelle la propriété va être vraie, et [H] la preuve que
    cette propriété est vraie pour [y]. *)

Lemma exP_imp_exQ :
  (forall x, P x -> Q x) -> (exists x, P x) -> (exists x, Q x).
Proof.
  (* On suppose :
     ([H1]) : [forall x, P x -> Q x]
     ([H2]) : [exists x, P x.] *)
  intros H1 H2.
  (* L'hypothèse ([H2]) fournit un certain [y] de type [X] qui vérifie
     ([H']) : [P y]. *)
  destruct H2 as [y H'].
  (* Pour prouver qu'il existe [x] tel que [Q x], il suffit de prouver [Q y]. *)
  exists y.
  (* D'après ([H1]) appliquée à [y],
     pour prouver [Q y], il suffit de prouver [P y]. *)
  apply (H1 y).
  (* Or, d'après H', on a bien [P y]. *)
  exact H'.
Qed.

(** On peut aussi [destruct] immédiatement une hypothèse avec un
    « _intro pattern_ ».
    On remplace [intros H2] par [intros [y H']] directement. *)
Lemma exP_imp_exQ' :
  (forall x, P x -> Q x) -> (exists x, P x) -> (exists x, Q x).
Proof.
  intros H [y H'].
  exists y.
  apply (H y).
  (* apply H. marche aussi, Coq unifie silencieusement avec [apply]. *)
  exact H'.
Qed.

(** **** Exercice : Prouver le théorème suivant. *)
Theorem exists_or :
  (exists x, P x \/ Q x) <-> (exists x : X, P x) \/ (exists y : X, Q y).
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** Le théorème précédent est important et intéressant.
    Si on y réfléchit, le quantificateur [exists] est d'une certaine façon une
    généralisation de la disjonction [\/].
    Par exemple, sur [nat], on peut penser à la proposition
    [exists (n : nat), P n] 
    comme
    [(P 0) \/ (P 1) \/ (P 2) \/ (P 3)  \/ ...]
*)

(** **** Exercice : Prouver le théorème suivant. *)
Lemma exists_and :
  (exists x, P x /\ Q x) -> (exists y : X, P y) /\ (exists z : X, Q z).
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** **** Exercice : essayer d'avancer dans la preuve du théorème suivant. *)

(** Voir où vous êtes bloqué et pourquoi. Laisser [Abort.] (abandonner) à la
    fin, le théorème est faux de toute façon. *)

Theorem exists_and_faux :
  (exists x : X, P x) /\ (exists y : X, Q y) -> (exists x, P x /\ Q x).
Proof.
Abort. (* Abandonner la preuve (le théorème est faux de toute façon). *)

(** Comme pour la propriété analogue avec [forall] et [\/], nous allons
    construire un contre-exemple pour montrer qu'il est _faux_ que
    [(exists x : X, P x) /\ (exists y : X, Q y) -> (exists x, P x /\ Q x)].
    On va encore prendre [X = nat], [P = est_nul] et [Q = est_non_nul].
*)

(** La prémisse du faux théorème précédent est satisfaite par [nat], [est_nul]
    et [est_non_nul]. *)

(** **** Exercice : Prouver le théorème suivant. *)
Theorem exists_nul_and_exists_non_nul :
  (exists n : nat, est_nul n) /\ (exists m : nat, est_non_nul m).
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** Mais la conclusion est évidemment fausse. *)
(** **** Exercice : Prouver le théorème suivant. *)
Theorem non_exists_nul_et_non_nul :
  ~(exists n : nat, (est_nul n /\ est_non_nul n)).
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)

End Exists.

(** ** Négation et quantificateurs *)
Section Neg.
Context {X : Type} (P : X -> Prop).

(** Les deux résultats suivants ont une réciproque en logique classique
   (c'est-à-dire une fois qu'on a ajouté le tiers exclu). *)

(** **** Exercice : Prouver le théorème suivant. *)
Lemma fa_not_ex_not :
  (forall x, P x) -> ~(exists x, ~(P x)).
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** Remarquer la similitude avec l'une des lois de de Morgan : *)
Lemma and_imp_not_or_not (A B : Prop) : (A /\ B) -> ~(~A \/ ~B).
Proof.
  intros [HA HB] [HA' | HB'].
  - apply HA'. exact HA.
  - apply HB'. exact HB.
Qed.

(** Le lemme suivant dit en substance qu'un contre-exemple permet de nier une
    formule universellement quantifiée. *)

(** **** Exercice : Prouver le théorème suivant. *)
Lemma ex_not_not_fa :
  (exists x, ~ (P x)) -> ~(forall x, P x).
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** Encore une fois, remarquer la similitude avec : *)
Lemma or_not_not_and (A B : Prop) : ((~ A) \/ (~ B)) -> ~(A /\ B).
Proof.
  intros [H | H] [HA HB].
  - apply H. exact HA.
  - apply H. exact HB.
Qed.

End Neg.

(** ** Fonctions injectives, surjectives, bijectives *)
Section InjSurj.
  (** On considère maintenant deux types quelconques [X] et [Y]. *)
  Context {X Y : Type}.

  (** Une fonction injective de [X] vers [Y] est telle que chaque élément [y] de
      [Y] a au plus un antécédent. *)
  Definition injective (f : X -> Y) :=
    forall (x x' : X), f x = f x' -> x = x'.

  (** Une fonction surjective de [X] vers [Y] est telle que chaque élément [y]
      de [Y] a au moins un antécédent. *)
  Definition surjective (f : X -> Y) :=
    forall (y : Y), exists (x : X), y = f x.

End InjSurj.

(** Voyons tout de suite des exemples : *)

(** On va commencer par la fonction S (successeur) et une nouvelle fonction
    appelée « prédécesseur ». *)

Definition pred (n : nat) :=
  match n with
    0 => 0 (* pred 0 = 0 : choix arbitraire... mais pratique *)
  | (S n') => n' (* pred (S n') = n' *)
  end.

(** Cette fonction est définie par un petit programme qui raisonne _par cas_ sur
    la nullité ou non de son argument. *)

(** Les valeurs sont bien celles qu'on attend : *)
Compute pred 43.
Compute pred 1.
(** Sauf que c'est une fonction totale, le prédécesseur de 0 est (de façon un
    peu arbitraire) 0. *)
Compute pred 0.

(** Comme il se doit, on définit deux petits lemmes pour ne pas avoir à se
    reposer entièrement sur [simpl]. *)
Lemma pred_0 : pred 0 = 0.
Proof. simpl. reflexivity. Qed.

Lemma pred_succ : forall n, pred (S n) = n.
Proof. intros n. simpl. reflexivity. Qed.

(** En fait, le lemme [pred_succ] est assez fondamental : il dit que _la
    composée_ des fonctions [pred] et [S] est l'identité, autrement dit,
    que [pred] est réciproque à gauche de [S]. *)

(** On va maintenant étudier l'injectivité et la surjectivité (ou non) des
    fonctions [S] et [pred]. *)

(** **** Exercice : Prouver le théorème suivant. *)
(** Indice : utiliser [pred_succ] pour réécrire dans le but. *)
Lemma succ_inj : injective S.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** **** Exercice : Prouver le théorème suivant. *)
Lemma pred_surj : surjective pred.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** **** Exercice : Prouver le théorème suivant. *)
Lemma not_succ_surj : ~(surjective S).
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** En fait, on peut être plus précis: *)
Lemma neq_0_succ : forall (n : nat), 0 <> S n.
Proof.
  intros n H. discriminate H.
Qed.

(** **** Exercice : Prouver le théorème suivant. *)
Lemma not_pred_inj : ~(injective pred).
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** Passons à des résultats généraux sur la composition des fonctions *)
Section Composition.
  Context {X Y Z : Type}.

  Lemma inj_comp (f : X -> Y) (g : Y -> Z) :
    injective f -> injective g -> injective (fun x => g (f x)).
  Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


  Lemma surj_comp (f : X -> Y) (g : Y -> Z) :
    surjective f -> surjective g -> surjective (fun x => g (f x)).
  Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


  Lemma comp_inj (f : X -> Y) (g : Y -> Z) :
    injective (fun x => g (f x)) -> injective f.
  Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


  Lemma comp_surj (f : X -> Y) (g : Y -> Z) :
    surjective (fun x => g (f x)) -> surjective g.
  Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)

End Composition.
