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

(** * Entiers naturels et induction *)

(** ** Définition inductive des entiers naturels *)

(* Le type [nat] est un type inductif : il est fait de constantes et de
constructeurs, qui peuvent être récursifs, c'est à dire faire
référence au type lui-même. *)

Print nat.
Check O.
Check S.

(** Pour Coq, un entier naturel est soit
    - O (la lettre O qui représente l'entier 0),
    - soit l'image par la fonction S (pour "successeur") d'un entier naturel.

    Ainsi :
    - O représente zéro
    - S O est le successeur de zéro donc un
    - S (S O) est le successeur de un donc deux
    - ...

    Heureusement Coq permet la notation usuelle (décimale) de ces
    entiers, mais ce n'est qu'une notation pratique !  *)

Check O.
Check S (S O).
Check S (S (S (S (S O)))).
Check 0. (* notation 0 pour zéro (O) *)

(** On dit que la constante O et la fonction S sont les
    _constructeurs_ du type nat. En Coq :

    - les résultats de constructeurs différents sont toujours
      différents,
    - deux termes composés uniquement de constructeurs ne peuvent être égaux
      _que_ s'ils s'écrivent de la même manière.
    
    À partir de maintenant, on utilisera la notation [0] (le chiffre zéro)
    pour zéro au lieu de _O_ (la lettre O).

    La tactique [discriminate H] demande à Coq de vérifier que la preuve [H]
    d'une égalité entre deux termes écrits uniquement avec des constructeurs
    est contradictoire, c'est-à-dire est une preuve de [False].
*)

Theorem deux_non_egal_a_trois : ~ (S (S 0) = S (S (S 0))).
Proof.
  (* En guise d'exemple, on prouve que 2 n'est pas égal à 3 dans [nat].
     Remarquer que Coq a écrit ≠ dans le but, en effet « différent de » est
     la même chose en Coq que _non égal_. *)
  unfold not.
  (* Supposons (hypothèse ([H])) que [2 = 3]. *)
  intros H.
  (* Comme [2 = S (S 0)] et [3 = S (S (S 0))], ils s'écrivent différemment donc
     [H] fournit une preuve de False. *)
  discriminate H.
Qed.

(** **** Exercice : Prouver le théorème suivant. *)

Theorem neq_0_succ : forall n : nat, ~ (0 = S n).
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** **** Exercice : Prouver le théorème suivant. *)

(** N'oubliez pas que de [False], on prouve n'importe quoi. *)
Theorem exo_discriminate2 : forall n : nat, (S (S 0)) = (S 0) -> n = S n.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** ** Addition des entiers naturels *)

(** Définissons maintenant l'addition des entiers relatifs. Dans un
    premier temps, on note add n m la somme de n et m. *)
Fixpoint add (n m : nat) : nat :=
  match n with (* "faire correspondre n avec" *)
    0 => m (* Si n = 0, alors n + m = m. *)
  | S p => S (add p m) (* (S p) + m = S (p + m). *)
  end.

(** Explications : add n m regarde si n vaut 0, si oui il renvoie m,
    sinon c'est que n = S p pour un certain p.
    On calcule alors (add p m) et on prend le successeur de ce nombre là.

    Cette définition de l'addition est _récursive_ (en Coq, "Fixpoint"
    pour une définition récursive) : la fonction add est elle-même
    utilisée dans sa définition. Pourtant il n'y a pas de raisonnement
    circulaire, cette définition permet bien de calculer (sinon, Coq
    ne nous aurait pas laissé faire de toute façon).
    
    Cette définition _est un programme_ : on a non seulement déclaré
    une fonction qui prend deux entiers et en retourne un, mais en plus on a dit
    _comment_ calculer le résultat.

    Ceci permet à Coq de faire les calculs lui-même :
*)

Compute (add 2 2).
Compute (add 12 30).

(** **** Exercice qui a l'air bête mais est très important :

    Calculer à la main (papier et crayon), en utilisant la définition
    de [add] :
    add (S (S 0)) (S (S (S 0))).
*)

(** En fait Coq dispose des notations usuelles pour l'addition (et la
    plupart des opérations usuelles. *)
Compute 2 + 5.

(** Nous allons maintenant devoir prouver des égalités.

    - La tactique [simpl] demande à Coq de _calculer_ dans le but en utilisant
      « bêtement » _la définition_ (et seulement la définition) d'une (ou
      plusieurs) fonctions, autant que possible. Elle n'est pas bien nommée,
      et devrait plutôt s'appeler « _compute_ » ou quelque chose comme ça.
    - La tactique [reflexivity] demande à Coq de conclure la preuve en
      constatant que les membres de gauche et de droite d'une égalité
      sont les mêmes.  *)

Theorem deux_et_deux_font_quatre : 2 + 2 = 4.
Proof.
  simpl. (* 2 + 2 = S (1 + 2) = S (S (0 + 2)) = S (S 2) = 4. *)
  reflexivity.
Qed.

(** **** Exercice : Prouver le théorème suivant. *)

Theorem add_0_l : forall n : nat, 0 + n = n.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** **** Exercice : Prouver le théorème suivant. *)

Theorem add_1_l : forall  n : nat, 1 + n = S n.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** **** Exercice : Prouver le théorème suivant. *)

Theorem add_succ_l : forall n m : nat, S n + m = S (n + m).
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** **** Exercice : Prouver le théorème suivant. *)

(* N'oubliez pas [discriminate] pour réfuter une égalité. *)
Theorem deux_et_deux_ne_font_pas_cinq : ~ (2 + 2 = 5).
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** ** La tactique [rewrite] *)

(** La tactique [rewrite] est une tactique très importante, probablement la plus
    utilisée de toutes !
    Elle permet de réécrire à l'aide d'une égalité.
    Si vous avez une hypothèse
    [H : a = b]
    alors [rewrite H] va transformer chaque [a] du but par un [b]. *)

(** *** Premiers exemples de [rewrite] *)

Theorem exemple_rewrite_hyp : forall n : nat, n = 42 -> n + 2 = 44.
Proof.
  intros n H.
  rewrite H.
  simpl.
  reflexivity.
Qed.

(** **** Exercice : Prouver le théorème suivant. *)
Theorem la_tete_a_toto : forall n : nat, n = 0 -> n + n = n.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** Comme avec [exact] (ou en fait avec toutes les autres tactiques), on peut
    utiliser des théorèmes déjà prouvés, dont la conclusion est une égalité,
    pour faire des réécritures avec [rewrite].
    On peut préciser à quels termes on applique ces théorèmes.

    Dans l'exemple important ci-dessous, tous les arguments sont précisés, on a
    aussi inséré des commandes [Check] pour que vous voyiez les énoncés précis
    utilisés, avant la réécriture (bien sûr, dans une vraie preuve on n'écrit
    pas ces [Check]).
*)

(* On va utiliser les théorèmes suivants : *)
Check add_1_l.
Check add_0_l.
Theorem exemple_rewrite_thm : forall n : nat, 0 + (1 + (1 + n)) = S (S n).
Proof.
  intros n.
  Check (add_1_l (1 + n)).
  rewrite (add_1_l (1 + n)).
  Check (add_1_l n).
  rewrite (add_1_l n).
  Check (add_0_l (S (S n))).
  rewrite (add_0_l (S (S n))).
  reflexivity.
Qed.

(** **** Exercice : sans utiliser [simpl], prouver le théorème suivant.

    C'est juste pour s'entraîner à rewrite et bien voir comment ça transforme le
    but).  Vous utiliserez les règles [add_0_l] et [add_1_l], ainsi que le
    « théorème » [deux_et_deux_font_quatre]. *)
Theorem exo_rewrite_theorems : (1 + 1) + ((0 + (0 + 1)) + 1) = 4.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** *** Unification, encore *)

(** En fait, il arrive souvent qu'il n'y ait pas tellement le choix pour les
    arguments des théorèmes utilisés dans [rewrite], ou bien, s'il y a le choix,
    que Coq décide pour vous de façon assez raisonnable.
    Alors, on peut omettre les arguments des théorèmes.

    Si on reprend l'exemple précédent en laissant Coq unifier/décider tout seul,
    ça donne : *)

Theorem exemple_rewrite_thm_unif : forall n : nat, 0 + (1 + (1 + n)) = S (S n).
Proof.
  intros n.
  rewrite add_1_l.
  rewrite add_1_l.
  rewrite add_0_l.
  reflexivity.
Qed.

(** En fait, avec [add_0_l] et [add_succ_l] on a deux résultats qui suffisent,
    avec [rewrite], à prouver tous les autres. On peut aussi utiliser [simpl],
    mais en fait [simpl] a un certain nombre de défauts :
    - souvent il en fait trop
    - pédagogiquement, cela ne correspond pas vraiment à quelque chose qu'on
      fait en mathématiques

    Donc à part dans le cas où de nouvelles opérations sont définies, il vaut
    mieux éviter de l'utiliser et faire des [rewrite] plus précis et
    prévisibles.
*)


(** **** Exercice : Prouver le théorème suivant sans [simpl].

    Utiliser uniquement les tactiques [intros], [rewrite] et [reflexivity] et
    les théorèmes [add_0_l], [add_succ_l] et [add_1_l].
    Dans un premier temps, vous donnerez dans les [rewrite] les arguments,
    dans un second temps, voir si vous pouvez les omettre et laisser Coq
    remplir tout seul les trous. *)
Theorem exo_rewrite_unif :
  forall n : nat, 0 + ((S 1) + S (1 + n))= S (S (S (S n))).
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** ** Preuve par cas : [destruct] (encore) *)

(** La façon dont sont construits les naturels en Coq fait apparaître deux
    _cas_ bien différents : un entier naturel, disons [n] vaut :
    - soit [0]
    - soit [(S n')] où [n'] est un autre entier.

    En Coq, la tactique [destruct] sur une variable de type entier (en général
    de n'importe quel type inductif) permet les preuves par cas. *)

Theorem double_eq_0_is_0 : forall n : nat, n + n = 0 -> n = 0.
Proof.
  (* Soit [n] un entier naturel. *)
  intros n.
  (* On suppose (hyp. ([H])) que [n + n = 0]. *)
  intros H.
  (* Preuve par cas : [n] est soit nul soit successeur d'un entier [n']. *)
  destruct n as [| n'].
  - (* Premier cas : [n = 0]. *)
    reflexivity.
  - (* Deuxième cas : [n = S n'] pour un certain [n' : nat]. *)
    (* Nous allons montrer que ce cas est impossible. *)
    exfalso.
    (* En réécrivant avec [add_succ_l], l'hypothèse [H] devient 
       [S (n' + S n') = 0]. *)
    rewrite add_succ_l in H.
    (* Noter la nouvelle syntaxe [rewrite règle in nom_hypothese]. *)
    (* Or, il est impossible que le successeur d'un naturel soit nul, par
       définition des entiers naturels. *)
    discriminate H.
Qed.

(** Dans la tactique [destruct n as [| n']] on retrouve la syntaxe
    [[quelque_chose | autre_chose]], qu'on avait vue lorsqu'on détruit les [\/].
    Ici :
    - [quelque_chose] est vide car c'est le cas n = 0, donc avec le constructeur
      sans argument
    - [autre_chose] est [n'] : on nomme l'entier n' tel que n = (S n').
      Bien sûr on aurait pu choisir n'importe quel autre nom que n'. *)

(** Remarque : on vient de voir qu'on peut aussi utiliser [rewrite] dans une
    hypothèse à l'aide de la syntaxe [rewrite règle in nom_hypothese]. *)

(** **** Exercice : Prouver le théorème suivant _avec une preuve par cas_. *)

Theorem npm_eq_0 : forall (n m : nat), n + m = 0 -> n = 0.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** **** Exercice : Prouver le théorème suivant _avec une preuve par cas_. *)

(** Indice : il faut faire une deuxième preuve par cas dans un des cas. *)
Theorem exo_destruct2 : forall n : nat, S (S (S n)) = 4 -> n = 1.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** ** Preuve par induction (ou récurrence) *)

(** Les tactiques [simpl], [destruct], [reflexivity] et [rewrite]
    ne suffisent pas toujours : *)

Theorem add_0_r : forall n : nat, n + 0 = n.
Proof.
  intros n.
  simpl. (* Aïe, [simpl] ne marche pas *)
  (* On peut essayer une preuve par cas : *)
  destruct n as [| n'].
  - (* le cas n = 0 se passe bien *)
    simpl. reflexivity.
  - (* mais là on va être bloqué... *)
    simpl.
    (* Il nous faudrait une preuve que [n' + 0 = 0]...
       On est bloqué. *)
Abort. (* La commande [Abort] abandonne une preuve. *)

(** Nous avons besoin de prouver ce théorème par induction. Une preuve
    par induction, aussi appelée preuve par récurrence sur entier naturel n a
    deux parties 
    - on prouve la proposition dans le cas où [n] vaut [0],
    - puis dans le cas où [n] s'écrit [S n'] pour un certain [n'], on prouve
      la propriété pour [n] _sous l'hypothèse qu'elle est vraie pour [n']_
      (on appelle cette hypothèse « hypothèse d'induction »). *)

Theorem add_0_r : forall (n : nat), n + 0 = n.
Proof.
  induction n as [|n' IH].
  - (* On suppose que n = 0. *)
    (* Par définition de [+], [0 + 0] vaut [0]. *)
    rewrite add_0_l.
    (* Les deux membres de l'égalité sont les mêmes, ce cas est terminé. *)
    reflexivity.
  - (* On suppose que [n = S n'] et que [n'] vérifie
       [(IH) : n' + 0 = n']. *)
    (* Par définition de [+], [S n' + 0] = [S (n' + 0)]. *)
    rewrite add_succ_l.
    (* On remplace, grâce à ([IH]), le terme ([n' + 0]) par [n']. *)
    rewrite IH.
    (* Les deux membres de l'égalité sont les mêmes, c'est terminé. *)
    reflexivity.
Qed.

(** Dans la tactique [induction n as [|n' IH]], il y a :
    - rien à gauche de la barre [|] car c'est le cas [0], sans argument
    - à droite de la barre [|] il y a [n'] car c'est le cas [n = (S n')] et
      il faut bien donner un nom à cette nouvelle variable et aussi un nom
      (ici [IH]) pour l'hypothèse que [n'] vérifie la propriété qu'on cherche à
      prouver. *)

(** Avec les tactiques [intros], [apply], [destruct], [simpl], [discriminate],
    [exfalso], [reflexivity], [induction] et [rewrite] vous pouvez écrire
    énormément de preuves *)

(** **** Exercice : Prouver le théorème suivant. *)
Theorem add_1_r : forall n : nat, n + 1 = S n.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** **** Exercice : Prouver le théorème suivant. *)

(** Remarque : le choix de la variable sur laquelle porte l'induction
    est important, il est guidé par la façon dont la fonction [add] a
    été écrite. Comme cette fonction sépare les cas suivant
    _son premier argument_, les preuves sur [+] se feront par induction sur
    l'opérande de gauche. *)

Theorem add_succ_r : forall n m, n + S m = S (n + m). 
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** **** Exercice : Prouver le théorème suivant. *)

(* Indice : utiliser les théorèmes précédents avec la tactique
   [rewrite]. Par exemple, si le but contient une expression du type
   [truc + S bidule], alors [rewrite add_succ_r] remplace cette expression
   par [S (truc + bidule)]. *)

Theorem add_comm : forall (n m : nat), n + m = m + n.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** **** Exercice : Prouver le théorème suivant. *)
Theorem add_assoc : forall (n m p : nat), n + (m + p) = (n + m) + p.
Proof. 
  (* Remarquez que Coq affiche naturellement [+] comme étant
     associatif à gauche *)
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** Pour finir cette partie sur l'addition, quelques remarques de qualité de vie
    sur [rewrite].

    Si vous avez suivi notre conseil sur [simpl] (ne pas trop l'utiliser), vous
    avez dû écrire beaucoup de [rewrite].
    En fait, on peut enchaîner les réécritures avec la syntaxe
    [rewrite regle_1, regle_2, ..., regle_n].

    Voici un exemple (avec de plus, un théorème qui sert souvent).
    Remarquer également qu'on a donné explicitement certains arguments.
*)

Theorem add_succ_comm : forall n m, n + S m = S n + m.
Proof.
  induction n as [| n' IH].
  - intros m. rewrite add_0_l, add_1_l. reflexivity.
  - intros m. rewrite (add_succ_l (S n')), add_succ_l.
    rewrite (IH m). reflexivity.
Qed.

(** ** La multiplication *)

(** La multiplication est aussi définie récursivement : *)
Fixpoint mul (n m : nat) :=
  match n with
  | 0 => 0
  | S p => m + mul p m
  end.

(** Avec des mots :
    - si [n = 0], alors [mul n m = 0].
    - sinon, [n = (S p)] pour un certain [p], et alors
      [mul (S p) m = m + (mul p m)].

   Réécrite avec les notations usuelles, la dernière égalité est bien
   compréhensible :
   [(p + 1) * m = p * m + 1 * m = p * m + m = m + p * m].

   Dans la bibliothèque de Coq, la notation [(n * m)] correspond à [(mul n m)].
*)
Compute (mul 2 3).
Compute (2 * 3).

(** **** Exercice papier-crayon :

    Évaluer à la main [(mul 2 3)]. Les évaluations de l'addition
    peuvent être faites directement. *)

(** Comme pour l'addition précédente, la définition de la multiplication
    est _constructive_, c'est-à-dire permet effectivement de calculer.
    On peut donc aussi utiliser la tactique [simpl] pour demander à Coq de
    calculer avec [mul].
    Voir les exemples suivants : *)

Theorem secret_of_the_universe : 6 * 7 = 42.
Proof.
  simpl.
  reflexivity.
Qed.

Theorem mul_0_l : forall n : nat, 0 * n = 0.
Proof.
  intros n.
  simpl.
  reflexivity.
Qed.

(** Comme la multiplication fait intervenir l'addition dans sa définition,
    vous aurez à utiliser les théorèmes déjà prouvés sur l'addition.
    Pour rappel, ceux-ci sont :
    - [add_0_l : ∀ n : nat, 0 + n = n]
    - [add_0_r : ∀ n : nat, n + 0 = n]
    - [add_1_l : ∀ n : nat, 1 + n = S n]
    - [add_1_r : ∀ n : nat, n + 1 = S n]
    - [add_succ_l : ∀ n m : nat, S n + m = S (n + m)]
    - [add_succ_r : ∀ n m : nat, n + S m = S (n + m)]
    - [add_comm : ∀ n m : nat, n + m = m + n]
    - [add_assoc : ∀ n m p : nat, n + (m + p) = (n + m) + p]
*)

(** **** Exercice : Prouver le théorème suivant. *)
(* begin hide *)
(* Dans le membre de droite, [m] n'est pas à la même place que dans la
   définition de [mul] Mais comme on va importer PeanoNat.Nat, il n'y a pas
   grand chose à faire... *)
(* end hide *)

Theorem mul_succ_l : forall n m : nat, (S n) * m = n * m + m.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** **** Exercice : Prouver le théorème suivant (sans induction). *)
Theorem mul_1_l : forall n : nat, 1 * n = n.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** Comme pour l'addition, nous avons maintenant avec [mul_succ_l] et [mul_0_l]
    tout ce qu'il faut pour calculer avec [rewrite], il vaut mieux éviter
    [simpl].
*)

(** **** Exercice : Prouver le théorème suivant (avec induction). *)
Theorem mul_0_r : forall n : nat, n * 0 = 0.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** **** Exercice : Prouver le théorème suivant (avec induction). *)

Theorem mul_1_r : forall n : nat, n * 1 = n.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** **** Exercice : Prouver le théorème suivant (sans induction). *)

Theorem mul_eq_0_rl : forall n m : nat,  (n = 0 \/ m = 0) -> n * m = 0.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** En général, les théorèmes et hypothèses sont écrits de façon à ce que le
    sens « naturel » de réécriture soit de gauche à droite (dans un certain
    sens, le membre de droite de l'égalité est « plus simple » que le membre de
    gauche). Il arrive toutefois qu'on doive réécrire en utilisant l'égalité
    de droite à gauche. Ceci se fait avec la syntaxe [rewrite <-regle], comme
    le montre l'exemple suivant. *)

Theorem exple_rewrite_rl : forall n, 6 = n -> n * (S n) = 42.
Proof.
  intros n H.
  rewrite <-H.
  simpl.
  reflexivity.
Qed.

(** Avant de passer à quelque chose de plus sérieux (et difficile) un petit
    exercice stupide pour s'exercer.
    Utiliser [add_assoc] et l'hypothèse de droite à gauche.
    N'utiliser [simpl] qu'à la toute fin, lorsqu'il n'y a que des nombres
    littéraux.
*)

(** **** Exercice : Prouver le théorème suivant. *)
Theorem exercise_rewrite_rl : forall n, 15 = 10 + n -> 27 + n + 10 = 42.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** **** Exercice : Prouver le théorème suivant par induction. *)

(** Celui ci est un peu embêtant... mais est un passage obligé pour prouver que
    la multiplication est commutative.
    Si vraiment, vous n'y arrivez pas après avoir beaucoup essayé, passez à la
    suite et revenez plus tard.
*)

Theorem mul_succ_r : forall n m : nat, n * S m = n * m + n.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** **** Exercice : Prouver le théorème suivant. *)
Theorem mul_comm : forall n m : nat, n * m = m * n.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** ** Bilan *)

(** Nous avons d'abord vu que les entiers naturels sont définis en Coq par 
    induction. Il y a [0], puis [S 0], puis [S (S 0)], ...
    Par définition, deux entiers naturels écrits uniquement avec des 
    constructeurs sont différents s'ils sont syntaxiquement différents.
    La tactique [discriminate nom_d'hypothese] permet de trouver une
    contradiction (donc de terminer la preuve) de ce type dans une égalité.
  
    Un aspect important de Coq est qu'il est capable de _calculer_. Nous
    avons vu qu'avec la tactique [simpl], il calcule autant qu'il peut en
    utilisant les définitions données.

    La tactique [reflexivity] permet de terminer une preuve d'une égalité
    en demandant à Coq de constater que les membres gauche et droit d'une
    égalité sont les mêmes.
    
    La tactique [rewrite preuve_egalite] utilise la preuve d'une égalité
    disons [a = b] pour changer tous les [a] du but en [b]. Nous avons vu
    qu'avec un théorème du type égalité universellement quantifiée, on peut
    laisser Coq unifier (remplir les trous) ou bien au contraire les remplir
    nous-mêmes. La variante [rewrite preuve_egalite in nom_d'hypothèse] permet
    de réécrire dans une hypothèse plutôt que dans le but. Il est possible
    d'enchaîner les réécritures en séparant les règles par des virgules.
    Enfin, il est possible de réécrire avec une égalité vue de droite à gauche
    avec la syntaxe [rewrite <-preuve_egalite].

    Ensuite, nous avons vu l'induction sur les entiers (la récurrence),
    avec la tactique
    [induction nom_var as [| autre_nom_var nom_hypothese].]

    Enfin, nous avons prouvé de nombreuses propriétés très utiles de l'addition
    et de la multiplication (mais inutile de les apprendre par coeur) :
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

    Les autres propriétés importante de la multiplication sont à prouver
    dans les exercices à faire à la maison. Ce sont :
    - [mul_add_distr_l : ∀ n m p : nat, n * (m + p) = n * m + n * p]
    - [mul_add_distr_r : ∀ n m p : nat, (n + m) * p = n * p + m * p]
    - [mul_assoc : ∀ n m p : nat, n * (m * p) = n * m * p]
    - [mul_eq_0: ∀ n m : nat, n * m = 0 ↔ n = 0 ∨ m = 0]

    Si vous avez vraiment bien assimilé tout ce sujet, vous avez sûrement
    beaucoup progressé en mathématiques et en informatique théorique !
    (Et on espère que c'était amusant !)
*)
