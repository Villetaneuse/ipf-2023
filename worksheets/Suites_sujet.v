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
From Coq Require Import Rbase Rfunctions SeqProp Rseries Lra Lia PeanoNat.
From Coq Require Import Classical.
Import Nat.
Open Scope nat_scope.
Open Scope R_scope.

(** * Nombres réels : les suites convergentes *)

(** ** Première partie : égalité en analyse

    En analyse, prouver que deux choses sont égales s'obtient souvent par
    des moyens détournés qui peuvent surprendre le débutant.
*)

(** Voici le résultat sans doute le plus fréquemment utilisé en
    analyse (mais souvent implicitement) : pour prouver qu'un réel est nul, il
    suffit de montrer que sa valeur absolue (c'est-à-dire sa distance à 0) est
    inférieure à tout réel strictement positif.

    Si vous voulez, vous pouvez (mais ce n'est pas obligé) utiliser :
*)
Check Rabs_pos_lt.
Lemma small_zero: forall x,
  (forall eps, eps > 0 -> (Rabs x) < eps) -> x = 0.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** Deux réels sont égaux lorsque leur distance peut être rendue aussi petite
    qu'on veut. Pensez à [unfold R_dist, Rminus].
*)
Lemma small_dist_equal: forall x y,
  (forall eps, eps > 0 -> (R_dist x y) < eps) -> x = y.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** ** Deuxième partie : les suites convergentes (1) *)
    
(** Une suite réelle n'est rien d'autre qu'une fonction de nat vers R.
    La définition de la convergence d'une suite vers une limite l (finie)
    par Weierstrass a fait entrer l'analyse dans son ère moderne.
    Dans cette bibliothèque, cette propriété se note [Un_cv].
*)

Print Un_cv.

(** Il s'agit bien de la définition usuelle : une suite Un converge vers une
    limite l si la distance entre Un et l devient aussi
    petite que l'on veut à partir d'un certain rang. *)

(** En guise d'exemple, nous allons donner la preuve de l'unicité d'une telle
    limite, lorsqu'elle existe.
    
    Mais avant, nous devons parler de l'ordre sur les entiers naturels car
    ils sont aussi de la partie.
*)

(** Nous ne pouvons pas définir l'ordre <= sur nat dans ce cours pour des
    raisons pédagogiques. Par contre nous pouvons l'utiliser et utiliser les
    théorèmes déjà prouvés dessus. *)

(* Il y a une grande quantité de théorèmes déjà prouvés dans la bibliothèque : *)
Search "<="%nat inside PeanoNat. (* Le %nat sert à définir la portée
          du symbole <= car ici, nous sommes dans celles des réels. *)

(* En particulier, <= est bien une relation d'ordre. *)
Check le_trans. (* le pour "lesser than or equal to", transitivité *)
Check le_refl. (* réflexivité *)
Check le_antisymm. (* antisymétrie *)

(** Pour des inégalités "évidentes" dans nat, il y a la tactique automatique
    très puissante [lia]. Un exemple (très utile) : *)
Lemma le_succ_r (n m : nat) : (n <= (S m) -> n <= m \/ n = (S m))%nat.
Proof.
  intro H. lia.
Qed.

(** Enfin, on a souvent à utiliser les lemmes sur le maximum de deux entiers. *)
Check max_l.
Check max_r.
Check le_max_l.
Check le_max_r.
Check max_lub_l.
Check max_lub_r.
Search max%nat.

(* On s'attaque maintenant à l'unicité de la limite : *)
Theorem UL_sequence (Un : nat -> R) (l1 l2 : R) :
  Un_cv Un l1 -> Un_cv Un l2 -> l1 = l2.
Proof.
  unfold Un_cv.
  intros Hl1 Hl2.
  (* On va montrer que la distance entre l1 et l2 est aussi petite qu'on veut.*)
  apply small_dist_equal.
  (* Soit eps > 0. *)
  intros eps Heps.
  (* Soit n1 tel que pour tout n >= n1, |Un - l1| < eps / 2. *)
  destruct (Hl1 (eps / 2)) as [n1 Hn1]. lra.
  (* Soit n2 tel que pour tout n >= n2, |Un - l2| < eps / 2. *)
  destruct (Hl2 (eps / 2)) as [n2 Hn2]. lra.
  (* Soit n3 = max(n1, n2). *)
  remember (max n1 n2) as n3 eqn:n3_max.
  (* Il suffit de montrer (par transitivité de l'ordre) que
    |l1 - l2| <= |l1 - Un3| + |Un3 - l2| et
    |l1 - Un3| + |Un3 - l2| < eps *)
  apply (Rle_lt_trans _ (R_dist (Un n3) l1 + R_dist (Un n3) l2) _).
  - (* La première inégalité est l'inégalité triangulaire. *)
    rewrite (R_dist_sym (Un n3)).
    apply R_dist_tri.
  - (* La seconde est la somme des inégalités Hn1 et Hn2 appliquées à n3. *)
    replace eps with (eps/2 + eps/2) by lra.
    apply Rplus_lt_compat.
    + apply Hn1. lia.
    + apply Hn2. lia.
Qed.

(** Remarques sur l'importante preuve précédentes
    - On essaie de déléguer au maximum les preuves évidentes annexes à [lra]
      pour les réels et [lia] pour les naturels.
    - La tactique
      [replace terme1 with terme2]
      remplace un terme par un autre dans le but. Coq va nous demander ensuite
      une preuve de l'égalité [terme1 = terme2].
      Ici, on la donne directement après le mot-clé [by] car [lra] sait le
      faire.
      Il y a bien sûr une variante
      [replace terme1 with terme2 in hypothèse]
      qui permet de remplacer un terme par un autre dans une hypothèse.
    - La tactique [remember] permet d'introduire dans le contexte un nouvel
      objet (ou même un théorème, une hypothèse).
      Ici on aurait pu s'en passer et simplement écrire [exists (max n1 n2)]
      mais ça correspondait mieux à la démonstration mathématique.
    - Le coeur de l'activité de l'analyste est de manipuler des inégalités. Ici
      on a utilisé (et vous utiliserez encore beaucoup) :
      [Rplus_lt_compat]
      [Rle_lt_trans]
      [Rdist_tri]
*)

(** À vous ! En vous inspirant de la preuve de [UL_sequence], prouvez
    que la somme de deux suites convergentes converge vers la somme des limites.

    Il est indispensable que la preuve mathématique soit déjà claire pour vous.
 *)

Theorem CV_plus (An Bn : nat -> R) (l1 l2 : R) :
  Un_cv An l1 -> Un_cv Bn l2 -> Un_cv (fun n => An n + Bn n) (l1 + l2).
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** Maintenant, on prouve qu'en multipliant une suite convergente vers l par une
    constante K, on obtient une suite qui converge vers K * l.
    Attention, il y a deux cas K = 0 ou non.
    Faire un [destruct Req_dec K 0] pour séparer ces deux cas.
    Quelques théorèmes, qui peuvent être utiles :
*)

Check Req_dec.
Check R_dist_eq.
Check Rabs_pos_lt.
Check Rdiv_lt_0_compat.
Check Rmult_lt_compat_l.
Check R_dist_mult_l.

(** Assurez-vous, avant de vous lancer dans la preuve formelle de savoir le
    faire en maths. *)
Lemma CV_mult_const_l (Un : nat -> R) (K : R) (l : R) :
  Un_cv Un l -> Un_cv (fun n => K * Un n) (K * l).
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** Résultat intermédiaire facile pour prouver la convergence de Un * K en
    utilisant le théorème précédent. *)
Theorem CV_eq_compat_l (Un Vn : nat -> R) (l : R) :
  (forall n, Vn n = Un n) -> Un_cv Un l -> Un_cv Vn l.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


Lemma CV_mult_const_r (Un : nat -> R) (K : R) (l : R) :
  Un_cv Un l -> Un_cv (fun n => Un n * K) (l * K).
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** ** Partie 3 : Un exemple de suite qui diverge vers l'infini *)
    
(** Il n'y a pas que les suites convergentes dans la vie. Il y a aussi
    - des suites qui divergent vers + l'infini;
    - des suites qui divergent vers - l'infini;
    - des suites qui divergent tout court (n'admettent ni limite finie ni limite
      infinie).

    On va ici prouver la suite définie par Un = n pour tout n diverge vers
    l'infini.
    D'abord la définition. Dans cette bibliothèque, cela s'écrit [cv_infty].
*)
Print cv_infty.

(** En fait, cette définition n'est pas très pratique. On va plutôt utiliser *)
Definition cv_infty' (Un : nat -> R) :=
  forall A : R, A > 0 ->
    exists N : nat, forall n : nat, (n >= N)%nat -> Un n > A.
  
(** Avec la preuve (à lire) que les deux propositions sont équivalentes *)

Theorem cv_infty_cv_infty' (Un : nat -> R) :
  cv_infty Un <-> cv_infty' Un.
Proof.
  (* On va prouver les deux implications. *)
  split; intros H.
  - (* Celle de gauche à droite est évidente. *)
    intros A _; apply H.
  - intros A.
    (* Pour la seconde, on raisonne par cas selon le signe de A *)
    destruct (total_order_T A 0) as [H' | H'].
    + (* On suppose A <= 0.
         L'hypothèse (H) fournit N tel que (Un n) > 1 dès que n >= N. *)
      destruct (H 1) as [N HN]. 
        lra.
      (* On peut choisir ce N. *)
      exists N; intros n Hn.
      (* Soit n >= N. Alors Un > 1 > A car A <= 0. *)
      apply (Rgt_trans _ 1).
      * apply HN, Hn.
      * destruct H'; lra.
    + (* Si A > 0, le résultat est évident. *)
      now apply H.
Qed.

(** En mathématiques, on fait souvent (et pour de bonnes raisons) l'abus que
    l'ensemble des naturels est inclus dans l'ensemble des réels. En coq, ce
    n'est pas possible : nat et R sont deux types différents.
    La fonction INR (pour injection de N dans R) permet de passer du naturel n
    au réel 1 + 1 + ... + 1 (n fois). *)
Print INR.

(** Nous allons prouver que la suite INR diverge vers l'infini. Pour ceci, nous
    aurons besoin de la propriété suivante des réels : ils forment un corps
    archimédien : *)
Axiom archimed' :
  forall eps A : R, eps > 0 -> A > 0 -> exists n : nat, (INR n) * eps > A.
(** Cet axiome dit en substance que
    - pour un [eps > 0] aussi petit qu'on veut;
    - pour un [A > 0] aussi grand qu'on veut;
    On peut toujours trouver un entier naturel [n] tel que [n * eps] est plus grand
    que [A].
    
    Remarque : l'axiome [archimed] de cette bibliothèque est différent, car plus
    puissant, mais plus difficile, dans un premier temps, à utiliser.
*)

(** À vous maintenant, vous aurez à
    [destruct (archimed' preuve1 preuve2 val_eps val_A)]
    avec :
    - [val_eps] : ce que vous avez choisi comme eps (n'allez pas chercher trop
    loin...)
    - [val_A] : ce que vous avez choisi comme A
    - preuve1 : une preuve que votre [eps > 0]
    - preuve2 : une preuve que votre [A > 0]

    Enfin, vous aurez sans doute besoin de résultats sur INR.
*)

Search "INR".
Check le_INR.
Theorem n_to_infty :
  let Un n := INR n in cv_infty Un.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** Une suite qui tend vers l'infini est toujours positive à partir d'un certain
    rang. *)
Theorem cv_infty_pos (Un : nat -> R) :
  cv_infty Un -> exists N, forall n, (n >= N)%nat -> Un n > 0.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)

(** Deux théorèmes pratiques qui ne sont pas dans la bibliothèque : *)
Check Rinv_lt_contravar.
Theorem Rinv_lt_contravar' (x y : R) :
  x > 0 -> y > 0 -> x < y -> / y < / x.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


Theorem Rinv_left_lt (x y : R) :
  y > 0 -> x > / y -> / x < y.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** Maintenant on peut prouver que l'inverse d'une suite qui diverge vers
    l'infini converge vers 0. *)
Theorem cv_infty_cv_0 (Un : nat -> R) :
  cv_infty Un -> Un_cv (fun n => / Un n) 0.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** En particulier, la suite (fun n => 1 / (INR n)) tend vers 0. *)

Theorem inv_n_to_0 : Un_cv (fun n => / (INR n)) 0.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** ** Partie 4 : Majorant, minorant, borne supérieure et borne inférieure *)

(** Rappel : en coq, une partie de R est une fonction de R vers Prop.
    Un majorant (en anglais upper bound) est une valeur qui est supérieure ou
    égale à tous les éléments de l'ensemble. *)
Print is_upper_bound. (* en français : est majorant de *)
(** On rappelle qu'il faut ici comprendre (E x) comme "x appartient à E", donc
    [is_upper_bound E m] dit que pour tout x appartenant à E, x <= m. *)

(** Un minorant d'une partie est défini de la même manière. *)
Definition is_lower_bound (E : R -> Prop) (l : R) :=
  forall x : R, E x -> l <= x.

(** On va montrer que l'ensembles des inverses des entiers naturels est minoré
    par 0. *)
Definition ens_inverses (x : R) := exists n : nat, x = / ((INR n) + 1).

Check pos_INR.
Theorem inverses_min : is_lower_bound ens_inverses 0.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** La borne supérieure d'un ensemble, lorsqu'elle existe est le plus petit
    majorant de cet ensemble (en anglais least upper bound), ici, [is_lub]. *)
Print is_lub.

(** Même chose pour la borne inférieure (en anglais greatest lower bound). *)
Definition is_glb (E : R -> Prop) (l : R) :=
  is_lower_bound E l /\ (forall b : R, is_lower_bound E b -> b <= l).

(** À vous, maintenant, prouvez que la borne inférieure des inverses des entiers
    naturels est 0. *)
Theorem inverses_glb : is_glb ens_inverses 0.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** ** Partie 5 : Compléments sur les suites convergentes. *)

(** On va d'abord vers un résultat très important : les suites convergences
    sont bornées. Pour ce faire on a besoin de l'opération suivante : *)
Fixpoint running_max (Un : nat -> R) (n : nat) :=
  match n with
    0%nat => (Un 0%nat)
  | S n => Rmax (running_max Un n) (Un (S n))
  end.
(** En français, [running_max Un n] est le maximum des n + 1 premiers termes de la
    suite Un. *)

Lemma Un_le_running_max (Un : nat -> R) (n : nat) :
  forall i, (i <= n)%nat -> Un i <= (running_max Un n).
Proof.
(* N'oubliez pas que sur les entiers nat, l'induction existe! *)
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** Voici une définition possible de "suite bornée" : *)
Definition bounded (Un : nat -> R) :=
  exists m, forall n, Rabs (Un n) <= m.

(** On peut prendre le majorant aussi grand qu'on veut *)
Theorem bounded_choose_ub (A : R) (Un : nat -> R) :
  bounded Un -> (exists m, m > A /\ forall n, Rabs (Un n) <= m).
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** Le suites convergentes sont bornées. *)
Theorem CV_impl_bounded (Un : nat -> R) (l : R) :
  Un_cv Un l -> bounded Un.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


Lemma CV_l_CV_0 (Un : nat -> R) (l : R) :
  Un_cv Un l <-> Un_cv (fun n => (Un n - l)) 0.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** On voudrait montrer que le produit de deux suites convergentes est une suite
    convergente.

    On commence par le cas où l'une des suites converge vers 0 et l'autre
    est bornée. *)

Theorem CV_mult_0 (An Bn : nat -> R) :
  let Cn (n:nat) := (An n * Bn n) in
  bounded An -> Un_cv Bn 0 -> Un_cv Cn 0.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


Theorem CV_mult (An Bn : nat -> R) (a b : R) :
  let Cn (n : nat) := (An n * Bn n) in
  Un_cv An a -> Un_cv Bn b -> Un_cv Cn (a * b).
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)

