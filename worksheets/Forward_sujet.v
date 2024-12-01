(** *** Appliquer une implication dans une autre hypothèse. *)

(** Jusqu'à présent, nous avons toujours prouvé nos théorèmes en travaillant sur
    le _but_. C'est ce qu'on appelle un raisonnement "vers l'arrière"
    (_backward reasoning_). Ce style de raisonnement est favorisé en coq : par
    défaut, la plupart des tactiques transforment le but avec des raisonnements
    du type "d'après telle hypothèse, si je sais prouver truc (nouveau but),
    alors j'aurai bidule (ancien but)", autrement dit,
    "d'après telle hypothèse, pour
    prouver bidule (ancien but) _il suffit_ de prouver truc (nouveau but)". *)

Theorem imp_trans2 : forall P Q R S : Prop,
  (P -> Q) -> (Q -> R) -> (R -> S) -> P -> S.
Proof.
  (* Soient P, Q, R et S des propositions quelconques *)
  intros P Q R S.
  (* On suppose prouvées
     (HPQ) : P -> Q
     (HQR) : Q -> R
     (HRS) : R -> S
     (HP)  : P
     et on doit montrer S.*)
  intros HPQ HQR HRS HP.
  (* D'après HPS, pour prouver S il suffit de prouver R. *)
  apply HRS.
  (* D'après HQR, pour prouver R il suffit de prouver Q. *)
  apply HQR.
  (* D'après HPQ, pour prouver Q il suffit de prouver P. *)
  apply HPQ.
  (* Or, P est prouvée par hypothèse. *)
  exact HP.
Qed.

(** En mathématiques, on a plutôt l'habitude du raisonnement "vers l'avant" :
    construire pas à pas le but en énonçant de nouveaux faits. Ceci est
    aussi possible en coq. *)

Theorem imp_trans2' : forall P Q R S : Prop,
  (P -> Q) -> (Q -> R) -> (R -> S) -> P -> S.
Proof.
  (* La preuve commence de la même manière. *)
  intros P Q R S HPQ HQR HRS HP. 
  (* Remarquez qu'on peut introduire en même temps les variables et les
     hypothèses. *)
  (* D'après (HP) et (HPQ), Q est prouvée. *)
  apply HPQ in HP as HQ.
  (* Donc, par HQR, on a aussi une preuve de R. *)
  apply HQR in HQ as HR.
  (* Enfin, par HRS, on obtient une preuve de S. *)
  apply HRS in HR as HS.
  (* S est donc prouvée par hypothèse. *)
  exact HS.
Qed.

(** Remarque importante : il ne faut pas se mélanger les pinceaux entre
    [apply] et [apply in]. Dans les deux cas, on cherche à appliquer
    _une implication_.
    - Sans [in], on cherche à l'appliquer au but. Si l'on applique
      [H : A -> B] au but [B] avec [apply H], la _conclusion_ de l'implication
      doit être la même que le but (ou peut être unifiée au but).
    - Avec [in], on cherche à appliquer l'implication [H : A -> B] à une
      hypothèse [H' : A]. Cette fois avec [apply H in H'], c'est ce qui est
      _avant la flèche_ (l'impliquant) qui doit être identique (ou unifiable)
      au type de [H'].
*)

(** *** Exercice :
    Prouver avec un raisonnement "vers l'avant" les théorèmes [modus_ponens] et
    [imp_trans]. *)

Theorem modus_ponens' : forall P Q : Prop, P -> (P -> Q) -> Q.
Proof. (* Démonstration "vers l'avant". *)
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


Theorem imp_trans' : forall P Q R : Prop,
  (P -> Q) -> (Q -> R) -> (P -> R).
Proof. (* Démonstration "vers l'avant". *)
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** Conclusion :
    Coq (et en général les assistants de preuve) favorise la démonstration _vers
    l'arrière_. On raisonne sur _le but_ par conditions _suffisantes_. En
    général, c'est une bonne façon de faire (les preuves sont souvent plus
    courtes).

    Les mathématiciens raisonnent plus souvent avec un raisonnement _vers
    l'avant_ (avec un peu de raisonnement vers l'arrière aussi). Il peut être
    plus clair, même avec Coq, d'utiliser le raisonnement vers l'avant, au moins
    pour certaines étapes. L'ingrédient principal pour le faire est [apply in].

    Nous verrons par la suite deux autres tactiques pour un raisonnement vers
    l'avant : [assert] et [replace].
*)
