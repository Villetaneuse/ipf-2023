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

(** * Logique de base en Coq *)

(** ** La flèche ou implication *)

(** *** Type [Prop] et [->] *)
(** L'objet fondamental du système Coq est le _type_ (on dit qu'il est basé sur
    la _théorie des types_).
    Tous les objets que l'on manipule ont un certain type.
    Le type [Prop], parfois aussi noté ℙ dans certaines interfaces, est celui
    des propositions, c'est-à-dire des énoncés mathématiques que l'on peut
    chercher à prouver ou à réfuter.  *)

(** La commande [Check] permet d'imprimer le type d'un terme.
    Appuyer sur [Ctrl+↓] (si vous utilisez coqide) ou [Alt+↓]
    (si vous utilisez la version _web_) pour faire interpréter
    la prochaine ligne à Coq. Voir le résultat dans la fenêtre en bas à droite. *)
Check 2 + 2 = 4.
Check 2 + 2 = 5.

(** Les énoncés [2 + 2 = 4] et [2 + 2 = 5] sont tous deux de type [Prop], 
    peu importe qu'ils soient prouvables ou non. *)

(** Étant données deux propositions [P] et [Q], on peut en former une nouvelle,
    [P -> Q] (lire : « [P] flèche [Q] » ou « [P] implique [Q] »).

    Intuitivement, dans la logique de Coq,
    la proposition [P -> Q] signifie « si [P], alors [Q] » ou, plus précisément,
    « je sais construire une preuve de Q à partir d'une preuve de P. »

    Remarque : La notation usuelle des mathématiques pour « P implique Q » est
    [P ⇒ Q]. Continuez à l'utilisez lors de vos cours plus classiques de
    mathématiques.
*)

(** *** Première preuve *)

(** Nous allons maintenant énoncer et prouver un premier théorème. Exécuter pas
    à pas cette preuve pour bien voir les modifications dans le contexte et le
    but.
    En Coq, les commentaires sont écrits entre [(* ... *)].
    Ici, comme à beaucoup d'autres endroits de ce cours, ils sont destinés à
    vous montrer la preuve « mathématique » très détaillée correspondant à la
    preuve en Coq.
*)

(** Ce premier théorème énonce que, quelle que soit la proposition [P], on a
    [P -> P]. Cela peut paraître évident, mais en Coq il faut tout prouver ! *)
Theorem imp_refl : forall P : Prop, P -> P.
Proof.
  (* Soit [P] une proposition quelconque. *)
  intros P.
  (* Pour montrer une implication on suppose que ce qui est à gauche est prouvé.
     On doit prouver ce qui est à droite avec cette hypothèse supplémentaire. *)
  (* On suppose (hypothèse ([H])) que [P] est prouvée. *)
  intros H.
  (* On doit prouver [P], or ([H]) prouve exactement [P]. *)
  exact H.
Qed. (* Quod erat demonstrandum. Ce qu'il fallait démontrer. *)
(** Sans entrer dans tous les détails, quelques commentaires s'imposent :
    - [imp_refl] est le nom que nous avons choisi pour ce théorème.
    - La preuve se trouve entre les mots-clés [Proof.] et [Qed.]
    - Lorsque vous avez fait interpréter à Coq la ligne [Proof.], vous avez vu
      apparaître en haut à droite de l'écran une fenêtre qui décrit
      _l'état de la preuve_.
    - Cet état contient deux parties séparées par une ligne horizontale.
      En dessous de cette ligne se trouve le _but_ : c'est ce qu'il faut
      démontrer.
      Au-dessus de cette ligne se trouve le _contexte_ : un ensemble de
      variables et d'hypothèses qu'on peut utiliser pour prouver le but.
    - Les éléments de la preuve [intros] et [exact] sont appelés des
      _tactiques_ de preuve. Ils font évoluer l'état de la preuve.
    - Lorsque l'évaluation par Coq atteint [Qed.], Coq vérifie que la preuve est
      correcte et dans le cas contraire affiche un message d'erreur.
    - Petit point de syntaxe : en Coq, les commandes et les tactiques se
      terminent toujours par un point.

    Pour pouvoir passer à la suite, il faut avoir vraiment bien compris que
    - [intros nom_de_variable.] introduit une nouvelle variable dans le contexte
      en supprimant un quantificateur universel (un « pour tout » en français,
      [forall] en Coq ou le symbole [∀]).
    - [intros nom_d_hypothese.] introduit une nouvelle hypothèse dans le contexte
      en supprimant la première implication, à gauche, du but.
    - [exact nom_d_hypothese.] dit que l'hypothèse [nom_d_hypothese] est une
      preuve du but.
    Si besoin, exécuter de nouveau la preuve et bien regarder l'évolution de
    l'état de la preuve.
*)

(** **** Exercice : à vous de remplir la preuve suivante !
    Lorsque Coq vous indique que la preuve est terminée, vous devez remplacer
    la ligne [Admitted.] par [Qed.].
    C'est vraiment facile, on veut juste s'assurer que vous avez compris la
    preuve précédente et mémorisé ses tactiques. *)
Theorem imp_refl' : forall Q : Prop, Q -> Q.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** *** Plusieurs flèches à la suite *)
(** En Coq, lorsqu'on ne met pas de parenthèses dans une expression avec des
    [->], c'est comme s'il y en avait à droite : [P -> Q -> R] est la même
    proposition que [P -> (Q -> R)].
*)

(** **** Exercice : Prouver le théorème suivant. *)
Theorem imp_ex1 : forall P Q : Prop, P -> (Q -> P).
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** **** Exercice : Prouver le théorème suivant. *)

Theorem imp_ex2 : forall P Q : Prop, Q -> (P -> P).
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** Remarque importante :
    Après avoir introduit toutes les variables et toutes les hypothèses dans ces
    deux derniers exercices, les contextes sont exactement les mêmes. En fait,
    plutôt que de penser à [P -> Q -> R] comme ([P] implique que ([Q] implique
    [R])), il vaut mieux y voir « si [P] _et_ [Q], alors [R] », ou encore, « si
    j'ai une preuve de [P] et une preuve de [Q], alors je sais construire une
    preuve de [R] ».
*)

(** *** Appliquer une implication *)
(** Maintenant qu'on a vu comment _prouver_ (introduire) une implication, on va
  voir comment on _utilise_ (élimine, applique) une implication. *)

Theorem modus_ponens : forall P Q : Prop, P -> (P -> Q) -> Q.
Proof. (* Démonstration. *)
  (* Soient [P] et [Q] deux propositions quelconques.*)
  intros P Q.
  (* Supposons (hypothèse ([H])) que [P] est prouvée ... *)
  intros H.
  (* ... et (hypothèse ([H'])) que [(P -> Q)] est prouvée. *)
  intros H'.
  (* Comme, d'après [H'], [(P -> Q)] est prouvée,
     pour montrer [Q] _il suffit_ de montrer [P]. *)
  apply H'.
  (* Or, [P] est prouvée par l'hypothèse [H]. *)
  exact H.
Qed. (* CQFD. *)

(** Revenons sur la tactique [apply].
    Si la formule à prouver est [Q] et qu'une hypothèse [H] a la forme
    [P -> Q], alors l'utilisation de [apply H.] entraîne le changement du but en
    [P].
    Ceci est conforme à la règle appelée syllogisme ou _modus ponens_ qui dit
    que de [P -> Q] et [P], on peut déduire [Q].
    - Socrate est un homme. ([P])
    - Tous les hommes sont mortels. ([P -> Q])
    - Donc Socrate est mortel. ([Q])

    Pour passer à la suite, vous devez vraiment avoir compris comme la tactique
    [apply] agit sur le but, si besoin en exécutant de nouveau la preuve
    précédente.
*)

(** **** Exercice : Prouver le théorème suivant. *)

Theorem imp_trans : forall P Q R : Prop,
  (P -> Q) -> (Q -> R) -> (P -> R).
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** *** Les sous-buts *)

(** Il arrive très souvent qu'une tactique crée des _sous-buts_ (en anglais
    _subgoals_), comme dans cette preuve du théorème suivant. *)

Theorem imp3 : forall P Q R : Prop,
  (P -> Q -> R) -> P -> Q -> R.
Proof.
  (* Soient [P], [Q] et [R] trois propositions quelconques. *)
  intros P Q R.
  (* Supposons :
    ([H])  : [P -> Q -> R]
    ([H1]) : [P]
    ([H2]) : [Q] *)
  intros H H1 H2.
  (* D'après ([H]), pour prouver [R] il suffit d'avoir une preuve de [P] et une
     preuve de [Q]. *)
  apply H.
  (* Remarquer les deux sous-buts ici ! *)
  (* On peut utiliser les caractères [-] [+] et *
     pour mettre en évidence le fait qu'on travaille sur un sous-but *)
  - (* Preuve de [P]: *)
    exact H1.
  - (* Preuve de [Q]: *)
    exact H2.
Qed.

(** Remarque : la preuve de l'exemple précédent est volontaire idiote pour vous
    montrer comment des sous-buts peuvent être générés.
    Seriez-vous capable de trouver une preuve beaucoup plus courte ? *)

(** **** Exercice : Prouver le théorème suivant. *)

Theorem premisses_non_ordonnées1 : forall P Q R : Prop,
  (P -> Q -> R) -> (Q -> P -> R).
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** **** Exercice : Prouver le théorème suivant. *)
Theorem imp_trans2 : forall P Q R S : Prop,
  (P -> Q) -> (Q -> R) -> (R -> S) -> P -> S.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** ** Conjonction [/\] *)

(** Le « et logique » aussi appelé opérateur de conjonction est noté en Coq [/\].
    Si [P] et [Q] sont deux propositions, alors [P /\ Q] est une proposition dont
    une preuve est à la fois une preuve de [P] et une preuve de [Q].
*)

(** *** Utiliser une conjonction : [destruct] *)

(** Pour décomposer une preuve de [P /\ Q] en une preuve de [P] et une preuve de
    [Q], on utilise la tactique [destruct]. *)
Theorem proj1 : forall P Q : Prop, P /\ Q -> P.
Proof.
  (* Soient [P] et [Q] deux propositions quelconques. *)
  intros P Q.
  (* Supposons
     ([H]) : [P /\ Q] *)
  intros H.
  (* De [H] on déduit :
      ([H]) : [P]
      ([H']) : [Q] *)
  destruct H as [H H'].
  (* Alors [P] est prouvée par l'hypothèse [H]. *)
  exact H.
Qed.

(** Noter la syntaxe avec crochets pour [destruct] une proposition conjonctive :
    la tactique [destruct H as [H1 H2]] a détruit l'hypothèse [H]
    (elle n'est plus présente dans le contexte) et a ajouté les deux nouvelles
    hypothèses [H1] et [H2], qui sont, respectivement une preuve de [P] et
    une preuve de [Q]. *)

(** **** Exercice : Prouver le théorème suivant. *)

Theorem proj2 : forall P Q : Prop, P /\ Q -> Q.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** **** Les « _intro patterns_ »
    Les preuves pouvant être longues, les concepteurs de Coq essaient
    continuellement de nous faciliter la tâche avec des constructions qui font
    gagner du temps. Les _intro pattern_ sont des transformations que l'on
    peut faire dès l'introduction de nouvelles hypothèses.
    Ici, au lieu d'écrire [intros H] suivi directement de [destruct H as
    [H1 H2]] il est possible d'écrire simplement [intros [H1 H2]] et l'hypothèse
    est directement introduite et détruite.
    La preuve de [proj1] peut donc s'écrire en deux tactiques : *)
Theorem proj1' : forall P Q : Prop, P /\ Q -> P.
Proof.
  intros P Q [H1 H2].
  exact H1.
Qed.

(** **** Exercice : Prouver le théorème suivant en utilisant un « _intro pattern_ ». *)
Theorem proj2' : forall P Q : Prop, P /\ Q -> Q.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** *** Prouver une conjonction : [split] *)

(** Prouver [P /\ Q] se fait en deux étapes : il faut une preuve de [P]
    et une preuve de [Q]. Ceci se fait avec la tactique [split]. *)

Theorem conj : forall P Q : Prop, P -> Q -> P /\ Q.
Proof.
  (* Soient [P] et [Q] deux propositions quelconques. *)
  intros P Q.
  (* Supposons :
      ([H1]) : [P]
      ([H2]) : [Q]. *)
  intros H1 H2.
  (* Pour prouver [P /\ Q] on doit prouver [P] puis [Q]. *)
  split. (* Remarquer l'apparition de 2 sous-buts. *)
  - (* Preuve de [P] : *)
    (* [P] est prouvée par l'hypothèse [H1]. *)
    exact H1.
  - (* Preuve de [Q] : *)
    (* [Q] est prouvée par l'hypothèse [H2]. *)
    exact H2.
Qed.

(** **** Exercice : Prouver le théorème suivant. *)

Theorem and_comm1 : forall P Q : Prop, P /\ Q -> Q /\ P.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** Remarque : comme pour  [->] l'opérateur [/\] est "associatif à droite" en Coq,
    ce qui signifie que [P /\ Q /\ R] dénote en fait [P /\ (Q /\ R)].
    Comme on va le voir ci-dessous, ceci n'a pas tellement d'importance ici. *)

(** **** Exercice : Prouver le théorème suivant. *)

Theorem and_assoc1 : forall P Q R : Prop, (P /\ Q) /\ R -> P /\ Q /\ R.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** **** Exercice : Prouver le théorème suivant. *)

Theorem and_assoc2 : forall P Q R : Prop, P /\ Q /\ R -> (P /\ Q) /\ R.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** ** Disjonction [\/] *)

(** En Coq, le « ou logique »,
    aussi appelée opérateur de disjonction, est noté [\/].
    Une preuve de [P \/ Q] est une preuve de P ou une preuve de Q.
*)

(** *** Prouver une disjonction : [left] et [right] *)

(** Pour pouvoir prouver une disjonction (par exemple [P \/ Q]) en logique
    intuitionniste, il faut dire explicitement si l'on donne une preuve de 
    l'opérande de gauche (ici [P]) ou de celui de droite (ici [Q]).
    Ceci se fait avec les tactiques [left] et [right].
*)

Theorem or_introl : forall P Q : Prop, P -> P \/ Q.
Proof.
  (* Soient [P] et [Q] deux propositions quelconques. *)
  intros P Q.
  (* Supposons
     ([H]) : [P] *)
  intros H.
  (* Pour prouver [P \/ Q] il suffit de prouver [P]. *)
  left.
  (* Or [P] est vraie par l'hypothèse [H]. *)
  exact H.
Qed.
(**
    _Attention_ : Le fait de choisir [left] ou [right] est en général important
    et doit être fait le plus tard possible (lorsque vous avez tous les éléments
    pour choisir).  Si vous vous sentez bloqué dans la preuve, il peut être
    intéressant de revenir en arrière et d'essayer de prouver l'autre côté.
*)

(** **** Exercice : Prouver le théorème suivant. *)

Theorem or_intror : forall P Q : Prop, Q -> P \/ Q.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** **** Exercice : Prouver le théorème suivant. *)
Theorem and_imp_or : forall P Q : Prop, P /\ Q -> P \/ Q.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** *** Utiliser une disjonction : [destruct] *)

(** Pour utiliser une disjonction (par exemple une preuve de [P \/ Q]),
    on doit faire une preuve _par cas_ :
    - Dans un premier temps, on prouve le but sous l'hypothèse que l'opérande de
      gauche (ici [P]) est prouvée.
    - Dans un second temps, on prouve le but sous l'hypothèse que  l'opérande de
      droite (ici [Q]) est prouvée.
    Ceci se fait encore avec la tactique [destruct].
*)

Theorem or_comm1 : forall P Q : Prop, P \/ Q -> Q \/ P.
Proof.
  (* Soient [P] et [Q] deux propositions quelconques. *)
  intros P Q.
  (* Supposons
     ([H]) : [P \/ Q]. *)
  intros H.
  (* De ([H]) on déduit 
     ([H1]) : [P]
     ou
     ([H2]) : [Q] *)
  destruct H as [H1 | H2].
  (* Noter beaucoup de choses ici :
     - la syntaxe avec la barre verticale dans les crochets pour le « ou »
     - il y a maintenant deux sous-buts, un par cas. En fait ce ne sont pas les
       buts qui diffèrent, mais les contextes (hypothèses). *)
  - (* cas 1 : sous l'hypothèse ([H1]) que [P] est prouvée *)
    right.
    exact H1.
  - (* cas 2 : sous l'hypothèse ([H2]) que [Q] est prouvée *)
    left.
    exact H2.
Qed.

(** **** Exercice : Prouver le théorème suivant. *)

Theorem or_ind : forall P Q R: Prop, (P -> R) -> (Q -> R) -> P \/ Q -> R.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** De la même manière que pour [/\], on peut utiliser un « _intro pattern_ »
    pour détruire une disjonction directement. *)
Theorem or_comm1' : forall P Q : Prop, P \/ Q -> Q \/ P.
Proof.
  intros P Q [H1 | H2].
  - right.
    exact H1.
  - left.
    exact H2.
Qed.

(** On peut même mettre des « _intro patterns_ » dans des « _intro patterns_ » *)
Theorem or_and_dist : forall P Q R : Prop, P \/ (Q /\ R) -> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R [H1 | [H2 H3]].
  (* À vous de terminer ! *)
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** ** Négation [~] *)

(** La négation en Coq est un peu particulière par rapport à la négation d'un
    cours de mathématique usuel.
    En effet, on ne définit pas la négation d'une proposition par sa table de 
    vérité mais en ajoutant une nouvelle proposition appelée [False].
*)

(** *** La proposition [False] *)
Check False.
(** La proposition [False] 
    désigne le faux, l'absurde, souvent notée en mathématiques ⊥
    (symbole _bottom_). Elle est définie par la règle appelée _ex falso quod
    libet_ (du faux, on peut déduire n'importe quoi), aussi appelée _principe
    d'explosion_.
*)

(** Si [False] est dans les hypothèses, alors la tactique [destruct] appliquée à
    celle-ci permet simplement de terminer la preuve.  *)

Theorem ex_falso_quod_libet : forall P : Prop, False -> P.
Proof.
  (* Soit [P] une proposition quelconque. *)
  intros P.
  (* Supposons (hypothèse ([H])) que False est prouvée. *)
  intros H.
  (* Explosion : le faux fait partie des hypothèses, tout est prouvé. *)
  destruct H.
Qed.

(** **** Exercice : prouver le théorème suivant : *)
(** Indice : réfléchissez avant de tout introduire... *)

Theorem exo_false : forall P Q : Prop,
  P -> False -> (P -> P) -> (Q -> P -> P) -> (Q -> Q -> P) -> P -> Q.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)

  
(** La tactique [exfalso] remplace le but courant par False.
    En effet, si l'on prouve False on prouve tout de toute façon. *)

Theorem stupide : forall P Q : Prop, (P -> False) -> P -> (Q -> P -> Q).
Proof.
  (* Soient [P] et [Q] deux propositions quelconques. *)
  intros P Q.
  (* On suppose
    ([H1]) : [P -> False]
    ([H2]) : [P] *)
  intros H1 H2.
  (* Comme [False] implique n'importe quoi, il suffit de prouver [False]. *)
  exfalso. (* Remarquer que le but a été simplement changé en [False]. *)
  (* Par H1 il suffit de prouver P. *)
  apply H1.
  (* Or P est vrai par hypothèse. *)
  exact H2.
Qed.

(** **** Exercice : Prouver le théorème suivant en utilisant [exfalso]. *)
Theorem P_et_P_imp_False : forall P Q : Prop, P /\ (P -> False) -> Q.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** *** Réfuter une proposition *)
(** La _négation_ d'une proposition P, notée en Coq [~P], ou encore [not P],
    est en fait simplement une _notation_ pour [P -> False].
*)
Check not.
Print not.
Locate "~".

(** On peut _déplier_ une notation, c'est-à-dire la remplacer par ce qu'elle
    représente avec la tactique [unfold] (littéralement « déplier »).  *)

Theorem exemples_unfold : forall A B C : Prop, ~A -> ~B -> ~C -> ~A /\ ~C.
Proof.
  intros A B C H1 H2 H3.
  (* On peut préciser dans quelle hypothèse on souhaite déplier. *)
  unfold not in H1.
  (* Éventuellement, dans plusieurs hypothèses d'un coup. *)
  unfold not in H2, H3.
  (* Si on ne précise rien, c'est dans le but. *)
  unfold not.
  (* Fin de la preuve de ce théorème idiot : *)
  split.
  - exact H1.
  - exact H3.
Qed.

(** Le prochain théorème dit la chose suivante :
   - si de [C] on peut déduire le faux
   - et que [A -> C]
   - alors de [A] on peut aussi déduire le faux. *)

Theorem contraposée : forall A C : Prop, (A -> C) -> ~C -> ~A.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(* En fait, avec un peu d'habitude, on peut sauter l'étape [unfold not]. *)

Theorem contraposée' : forall A C : Prop, (A -> C) -> (~C -> ~A).
Proof.
  intros A C H H'.
  (* On peut se passer de unfold not si on a bien compris. *)
  (* On suppose ([K]) : [A]  et on cherche à prouver [False]. *)
  intros K. 
  (* Si on a compris que [~C] est en fait la même chose que [C -> False],
     on peut [apply] directement [H']. *)
  apply H'.
  apply H.
  exact K.
Qed.

(** **** Exercice : Prouver le théorème suivant. Pensez à [exfalso]. *)

Theorem absurd : forall A C : Prop, A -> ~A -> C.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** **** Exercice : Prouver le théorème suivant. *)

Theorem exo_neg : forall P Q : Prop,
  (P -> Q) -> (P -> ~Q) -> ~P.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** ** Équivalence [<->] *)
Locate "<->".
Print iff.
(** L'équivalence logique est notée en Coq [<->].
    Comme vous le voyez ci-dessus, pour toutes propositions [P] et [Q],
    [P <-> Q] est la même chose que [(P -> Q) /\ (Q -> P)].
    Pour _prouver_ [P <-> Q], il faut donc prouver les deux implications
    [P -> Q] et [Q -> P]. Ceci se fait avec la tactique [split].
    Pour _utiliser_ une équivalence, la tactique [destruct] fournira les deux
    implications, comme pour n'importe quelle conjonction.
*)

Theorem iff_sym : forall P Q : Prop, P <-> Q -> Q <-> P.
Proof.
  (* Soient [P] et [Q] deux propositions quelconques. *)
  intros P Q.
  (* On suppose ([H]) : [P <-> Q]. *)
  intros H.
  (* De ([H]) on déduit :
     ([H1]) : [P -> Q]
     ([H2]) : [Q -> P] *)
  destruct H as [H1 H2].
  (* Pour prouver [P <-> Q], il suffit de prouver [P -> Q] et [Q -> P]. *)
  split.
  - (* Preuve de [P -> Q] : *)
    exact H2.
  - (* Preuve de [Q -> P] : *)
    exact H1.
Qed.

(** **** Exercice : Prouver le théorème suivant. *)

Theorem iff_refl : forall P : Prop, P <-> P.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** **** Exercice : Prouver le théorème suivant. *)

Theorem iff_trans : forall P Q R : Prop, (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** ** Appliquer un théorème *)

(** On peut fournir des _arguments_ à un théorème pour produire des
    formules déjà prouvées. *)
Section ArgumentsThéorèmes.
(* Section pour ne pas polluer le reste du fichier avec les paramètres [A], [B]
   et [C]. *)
Parameters A B C : Prop.
(** Le théorème [and_comm1] a deux variables universellement quantifiées. *)
Check and_comm1.
(** On peut _appliquer_ le théorème [and_comm1] à deux propositions. *)
Check and_comm1 A B.
(** Ou bien à une seule, l'autre restant universellement quantifiée. *)
Check and_comm1 A.
(** On peut même donner en argument des propositions plus compliquées. *)
Check and_comm1 (A -> B) (B -> C).
End ArgumentsThéorèmes.

(** On peut alors utiliser dans des preuves des théorèmes déjà prouvés. *)
Theorem and_comm : forall P Q : Prop, (P /\ Q) <-> (Q /\ P).
Proof.
  intros P Q.
  split.
  - exact (and_comm1 P Q).
  - exact (and_comm1 Q P).
Qed.
(** Au passage, remarquer le parenthésage un peu particulier de Coq. La plupart
    des mathématiciens auraient écrit quelque chose comme [and_comm1(P, Q)],
    ici, on écrit simplement la fonction (ou le théorème) et ses arguments
    séparés par des blancs et si besoin on les entoure de parenthèses. *)

(** **** Exercice : *)

(** Prouver le théorème suivant en utilisant [premisses_non_ordonnées1] *)
Check premisses_non_ordonnées1.
Theorem premisses_non_ordonnées :
  forall P Q R : Prop, (P -> Q -> R) <-> (Q -> P -> R).
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)

  
(** **** Exercice : *)

(** Prouver le théorème suivant en utilisant [and_assoc1] et [and_assoc2] *)

Check and_assoc1.
Check and_assoc2.
Theorem and_assoc : forall P Q R, (P /\ Q) /\ R <-> P /\ (Q /\ R).
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** ** Unification : Coq travaille pour vous *)

(** En mathématiques, il est fréquent d'omettre les arguments que l'on donne à
    un théorème, d'autant plus lorsqu'il n'y a aucune ambigüité.
    En Coq, il faut souvent être beaucoup plus explicite. Mais il y a des
    mécanismes qui permettent d'éviter de tout préciser. L'un deux est
    _l'unification_ : Coq essaie de deviner quels arguments donner à une formule
    un ou théorème.
    Lorsqu'à la place d'un terme on écrit [_], on dit à Coq qu'il doit essayer
    de deviner ce qu'il y a à la place.
*)
Theorem and_comm' : forall P Q : Prop, (P /\ Q) <-> (Q /\ P).
Proof.
  intros P Q.
  split.
  - (* Vu le but, le théorème [and_comm1] ne peut être appliqué qu'aux arguments
       [P] et [Q] donc pas la peine de les expliciter. *)
    exact (and_comm1 _ _).
  - (* Vu le but, Le théorème [and_comm1] ne peut être appliqué qu'aux arguments
       Q et P donc pas la peine de les expliciter. *)
    exact (and_comm1 _ _).
Qed.

(** Parfois, Coq ne peut pas tout deviner, il a besoin de certains arguments. *)
Theorem iff_trans' : forall P Q R : Prop, (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
  (* On va en donner une nouvelle preuve avec [imp_trans]. *)
  intros P Q R [H1 H1'] [H2 H2'].
  split.
  - (* On veut utiliser le fait que [(P -> Q)] et [(Q -> R)] implique
       [(P -> R)]. *)
    Check imp_trans.
    (* Le théorème [imp_trans] a 3 arguments.
       Ici, Coq peut deviner, vu la forme du but
       et la conclusion de [imp_trans] :
       que le premier est [P] et que le troisième est [R], mais il n'a aucun
       moyen de savoir que le deuxième devrait être [Q] !
       On va donc lui fournir. *)
    apply (imp_trans _ Q _).
    + exact H1.
    + exact H2.
  - (* On recommence, pour prouver [R -> P], il suffit de prouver [R -> Q]
       et [Q -> P] (qu'on a déjà dans le contexte).
       Coq peut encore deviner, vu le but :
       que le premier argument est [R], le troisième est [P], mais il ne peut
       unifier sans qu'on lui donne le deuxième argument. *)
    apply (imp_trans _ Q _).
    + exact H2'.
    + exact H1'.
Qed.

(** **** Exercice : Prouver le théorème suivant en utilisant [or_comm1] et en laissant au maximum Coq unifier. *)
Theorem or_comm : forall P Q : Prop, P \/ Q <-> Q \/ P.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** **** Exercice : Prouver le théorème suivant en utilisant [imp_refl] et en laissant au maximum Coq unifier.

    Votre preuve doit utiliser seulement un [intros] et un [exact]. *)
Theorem imp3' : forall P Q R : Prop, (P -> Q -> R) -> (P -> Q -> R).
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** ** Bilan
    Vient la partie la plus importante, il faut que tout ce que vous avez
    appris cette semaine soit acquis pour les suivantes.
    Nous avons rencontré (dans cet ordre), les tactiques suivantes :
    - [intros] une variable universellement quantifiée dans le but
    - [intros] une hypothèse lorsque le but est une implication
    - [exact]
    - [apply] une preuve d'une implication
    - [destruct] une preuve d'une conjonction
    - [split]
    - [destruct] une preuve d'une disjonction
    - [left] et [right]
    - [unfold]
    (Remarque encourageante, nous avons vu la moitié environ des tactiques
    utilisées dans ce cours.)
    Vous devez écrire une fiche décrivant le rôle de chaque tactique, un exemple
    de syntaxe, et la façon dont elle modifie l'état de la preuve (contexte
    et/ou but).

    Nous avons aussi rencontré (dans cet ordre) des connecteurs logiques :
    - implication [->]
    - conjonction [/\]
    - disjonction [\/]
    - [False] et négation [~]
    - équivalence [<->]
    Vous devez écrire, pour chacun d'entre eux, son sens « intuitif », la façon
    dont on le _prouve_ et la façon dont on _l'utilise_ dans une preuve.

    Enfin, vous devez savoir utiliser un théorème déjà prouvé dans une autre
    preuve et comprendre qu'on peut laisser à Coq certains « trous » qu'il peut
    remplir avec l'unification.
*)
