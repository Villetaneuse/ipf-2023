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

(** * Logique : exercices à faire à la maison *)

(** Ces exercices d'entraînement sont à faire à la maison (ou en classe si vous
    avez terminé). Ils sont en général un peu plus difficiles que ceux vus en
    classe. Il est très important que vous preniez le temps de les faire. *)

(** ** Exercices sur l'implication *)

(** **** Exercice : Prouver le théorème suivant *)
(** Indice : en vérité, il n'y a pas tellement à réfléchir, mais à un moment,
    vous aurez l'impression d'avoir fait du surplace alors que non, un nouvel
    élément sera apparu dans le contexte. *)
Theorem weak_peirce : forall P Q : Prop,
  ((((P -> Q) -> P) -> P) -> Q) -> Q.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)

  
(** **** Exercice : Prouver le théorème suivant. *)

(** Rien de bien difficile ici, un [apply] fera juste apparaître deux
    sous-buts. *)
Theorem diamond : forall P Q R T : Prop,
  (P -> Q) -> (P -> R) -> (Q -> R -> T) -> P -> T.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** ** Exercices sur la disjonction *)

(** **** Exercice : Prouver le théorème suivant. *)

Theorem or_assoc : forall P Q R: Prop, (P \/ Q) \/ R <-> P \/ Q \/ R.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** ** Exercices sur la négation *)
  
(** *** La double négation *)
(** En logique classique (c'est-à-dire avec le tiers-exclus), pour toute
    proposition [A], [~~A] est
    équivalente à [A].  En logique intuitionniste (qui est celle de Coq sans
    axiome supplémentaire), ce n'est pas toujours le cas. La proposition [~A]
    signifie
    « [A] est contradictoire », c'est-à-dire
    « [A] fait tout exploser », [~~A] signifie
    « il est contradictoire d'affirmer que A est contradictoire »,
    autrement dit « [A] est non contradictoire », ou encore
    « A ne fait pas tout exploser ».

    La différence entre [A] et [~~A] est semblable à la différence entre
    « je dis que c'est vrai » et « je ne dit pas que c'est faux ». On
    peut décider par convention que les deux phrases veulent dire la
    même chose (c'est-à-dire se placer dans une logique classique),
    mais ce n'est pas obligatoire.
    En fait, dans beaucoup de cas en informatique, on préfère ne pas supposer
    le tiers-exclus.
    On rappelle que [~~A] est une notation pour [(A -> False) -> False].  *)

(** Une proposition prouvée est toujours non contradictoire. *)

(** **** Exercice : prouver le théorème suivant. *)

Theorem A_imp_NNA : forall A : Prop, A -> ~~A.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** **** Exercice : prouver le théorème suivant *)
(** On peut prouver (pour deux propositions données) que le raisonnement par
   contraposition est non contradictoire. *)

Theorem contraposee2 : forall A C : Prop,
  ~~((~C -> ~A) -> (A -> C)).
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** **** Exercice *)

(** Dans la même veine, on a le théorème suivant. *)

Theorem contraposee3 : forall A C : Prop,
  (~C -> ~A) -> ~~(A -> C).
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)

  
(** ** Lois de de Morgan *)
(** Les "lois" de de Morgan sont un résultat très connu (et très utile !) de
    logique classique. Que se passe-t-il en logique intuitionniste ? *)

(** **** Exercice : Prouver le théorème suivant. *)

Theorem de_morgan_not_or : forall P Q : Prop, ~(P \/ Q) <-> (~ P) /\ (~ Q).
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** **** Exercice : Prouver le théorème suivant. *)

Theorem de_morgan_not_or_not : forall P Q : Prop, (~ P) \/ (~ Q) -> ~ (P /\ Q).
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** Remarquez qu'on ne vous a demandé qu'une seule implication dans l'exercice
    précédent...
    C'est parce que l'autre n'est tout simplement pas prouvable en logique
    intuitionniste. *)

(** **** Exercice : *)

(** En essayant de prouver le théorème suivant, se convaincre que ce n'est pas
    possible. Laisser [Abort.] (arrêter, abandonner) à la fin. *)
Theorem de_morgan_not_and : forall P Q : Prop, ~ (P /\ Q) -> (~ P) \/ (~ Q).
Proof.
  (* Essayez d'aller le plus loin possible dans la preuve. *)
Abort.

(** Nous verrons plus tard que le tiers-exclus permet de prouver cette dernière
    loi de de Morgan. *)
