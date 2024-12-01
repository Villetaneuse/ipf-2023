From Coq Require Import Rbase Classical.
Open Scope R_scope.
(** * Nouvelles tactiques pour le raisonnement vers l'avant *)

(** ** Introduction et rappels *)

(** L'assistant de preuves Coq (et il n'est pas le seul dans ce cas) favorise
    par défaut le raisonnement vers l'arrière.

    C'est-à-dire qu'on va raisonner par conditions suffisantes _sur le but_
    jusqu'à terminer la preuve.
    
    Une justification pratique pour raisonner vers l'arrière est que, comme il
    n'y a toujours qu'un seul but courant, il n'est pas nécessaire de préciser
    où les tactiques sont utilisées.
*)

(** Reprenons l'exercice [double_fixpoint_0] du sujet [RCorps] *)

(** Avec un raisonnement vers l'arrière cela donne : *)
Theorem double_fixpoint_0 : forall (x : R), x + x = x -> x = 0.
Proof.
  (* Soit x un réel tel que x + x = x (hypothèse (H)). *)
  intros x H.
  (* On veut prouver que x = 0. *)

  (* Pour cela, d'après Rplus_eq_reg_l, il suffit de prouver que
     x + x = x + 0. *)
  apply (Rplus_eq_reg_l x).

  (* Comme x + 0 = x, cela revient à prouver que x + x = x. *)
  rewrite Rplus_0_r.

  (* Or, c'est exactement notre hypothèse (H). *)
  exact H.
Qed.

(** Reprenons avec un raisonnement vers l'avant.
    
    Cette fois nous partons des hypothèses et allons progressivement
    vers le but.

    En Coq, cela signifie qu'on va surtout utiliser les versions avec [in] de
    [rewrite] et [apply]. *)

Theorem double_fixpoint_0' : forall (x : R), x + x = x -> x = 0.
Proof.
  (* Soit x un réel tel que x + x = x (hypothèse (H)). *)
  intros x H.
  
  (* Dans le membre de droite de [H], on peut remplacer x par x + 0. *)
  rewrite <-(Rplus_0_r x) in H at 3.

  (* Au passage, remarquer qu'on a dû préciser où appliquer la règle
     "réécrire x en x + 0": à la troisième occurrence
     (on commence la numérotation à 1). *)

  (* D'après Rplus_eq_reg_l, on peut simplifier des deux côté par x dans (H). *)
  apply Rplus_eq_reg_l in H.

  (* On a donc bien x = 0 d'après H. *)
  exact H.
Qed.

(** Voici quelques théorèmes qui n'ont pratiquement aucun contenu mathématique
    (on dit juste que deux nombres égaux ont la même image par une fonction),
    mais sont très utiles pour le raisonnement vers l'avant. *)
Theorem f_equal :
  forall (A B : Type) (f : A -> B) (x y : A), x = y -> f x = f y.
Proof.
  intros A B f x y H. rewrite H. reflexivity.
Qed.

Theorem Rplus_eq_compat_l :
  forall r r1 r2 : R, r1 = r2 -> r + r1 = r + r2.
Proof.
  intros r r1 r2 H. rewrite H. reflexivity.
Qed.

Theorem Rplus_eq_compat_r :
  forall r r1 r2 : R, r1 = r2 -> r1 + r = r2 + r.
Proof.
  intros r r1 r2 H. rewrite H. reflexivity.
Qed.

Theorem Rmult_eq_compat_l :
  forall r r1 r2 : R, r1 = r2 -> r * r1 = r * r2.
Proof.
  intros r r1 r2 H. rewrite H. reflexivity.
Qed.

Theorem Rmult_eq_compat_r :
  forall r r1 r2 : R, r1 = r2 -> r1 * r = r2 * r.
Proof.
  intros r r1 r2 H. rewrite H. reflexivity.
Qed.

(** Ils permettent, d'ajouter un même nombre des deux côtés
    d'une égalité ou de multiplier les deux côtés d'une égalité par un même
    nombre. *)

(** On peut s'en servir pour donner une nouvelle preuve vers l'avant de
    [double_fixpoint_0], peut-être plus naturelle pour vous. *)

Theorem double_fixpoint_0'' :
  forall x : R, x + x = x -> x = 0.
Proof.
  intros x H.
  (* On ajoute -x des deux côtés dans (H). *)
  apply (Rplus_eq_compat_l (- x)) in H.
  (* Après un peu de calcul, on prouve que x = 0. *)
  rewrite Rplus_opp_l in H.
  rewrite <-Rplus_assoc in H.
  rewrite Rplus_opp_l in H.
  rewrite Rplus_0_l in H.

  exact H.
Qed.

(** À vous de prouver le théorème suivant, en utilisant une stratégie de preuve
    vers l'avant inspirée par la preuve précédente. *)

(** **** Exercice : Prouver le théorème suivant. *)
(* Indications *)
Check Rinv_l.
Check Rinv_r.
Check Rmult_eq_compat_l.
Check Rmult_eq_compat_r.
(* et raisonner par cas sur la nullité de x avec
   destruct (classic (x = 0)) as [E | E] *)
Theorem sqr_fixpoint_0_1 :
  forall x : R, x * x = x -> x = 0 \/ x = 1.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** ** La tactique [assert] *)

(** En mathématiques, il est très fréquent que l'on fasse une _coupure_ dans
    la preuve en énonçant et démontrant un résultat intermédiaire.

    C'est ce que permet la tactique [assert] (qui signifie "affirmer") en Coq.

    La syntaxe que nous utiliserons est :

    [assert (formule) as nom]

    Ensuite, Coq vous demandera une preuve de la formule. Une fois cette
    preuve fournie, vous pourrez prouver votre théorème avec cette formule
    en plus dans le contexte (donc vous pourrez vous en servir).
*)

(** Voici un exemple avec une preuve vers l'avant. *)
Theorem Rmult_eq_1_l : forall x y, x * y = 1 -> y = / x.
Proof.
  (* Soient x et y deux réels tels que x * y = 1 (hypothèse (H)). *)
  intros x y H.
  
  (* On affirme que x <> 0. *)
  assert (x <> 0) as D. {
    (* En effet, si x = 0, ... *)
    intros Hx.
    (* ... alors en remplaçant x par 0 dans (H), ... *)
    rewrite Hx in H.
    (* ... on obtient 0 = 1, ... *)
    rewrite Rmult_0_l in H.
    (* ... ce qui est impossible car dans un corps on a 1 <> 0. *)
    apply eq_sym in H.
    apply R1_neq_R0 in H.
    destruct H.
  }
  (* Comme x <> 0, on peut diviser à gauche et à droite par x dans H. *)
  apply (Rmult_eq_compat_l (/ x)) in H.
  rewrite Rmult_1_r in H.
  rewrite <-Rmult_assoc in H.
  rewrite Rinv_l in H by (exact D).
  rewrite Rmult_1_l in H.
  exact H.
Qed.

(** Remarque syntaxique au passage.
    Dans la preuve précédente, la preuve de l'assertion est entre accolades.
    Ce n'est pas obligatoire, de la même manière qu'utiliser des "bullets"
    ([-] ou [+] ou [*]) n'est pas obligatoire pour les différentes étapes
    d'une preuve par cas ou par induction.

    Ceci renforce toutefois:
    - la lisibilité de la preuve : la preuve de l'assertion est clairement
      délimitée dans l'espace. Si elle ne m'intéresse pas, je peux lire la suite
      directement;
    - la robustesse de la preuve : si, à la suite de changements dans une
      bibliothèque ou dans Coq lui-même, la preuve de l'assertion est cassée,
      il y aura une erreur, _au plus tard_, à l'accolade fermante, Coq
      m'indiquant que la preuve de l'assertion n'est pas terminée.
      C'est un principe général important en programmation :
      "fail fast", échouer vite, (ou "fail early", échouer tôt).
      Lorsque quelque chose est cassé, on veut s'en apercevoir le plus tôt
      possible pour pouvoir mieux identifier l'erreur. *)

(** **** Exercice : Prouver le théorème suivant. *)
(** Le but est vraiment d'avoir la preuve la plus proche possible de ce qui
    se fait en mathématiques avec un raisonnement purement vers l'avant.

    Après avoir introduit variables et hypothèses, prouver le résultat
    intermédiaire
    [(Hx) : x = 0]
*)
Theorem exercice_assert : forall x y, y <> 0 -> x * y = 0 -> x + x = x.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** ** La tactique [replace] *)

(** Dans l'exercice précédent, vous avez prouvé une assertion, qui n'a servi
    qu'à réécrire dans le but.

    Ceci est très courant. C'est pourquoi Coq a la tactique [replace].

    La tactique [replace expr1 with expr2] remplace expr1 par expr2 dans le but.

    Une fois le but prouvé, vous aurez à prouver la preuve de l'égalité
    expr2 = expr1.
*)

(** Voyons ce que ça donne avec l'exercice précédent. *)
Theorem exemple_replace : forall (x y : R), y <> 0 -> x * y = 0 -> x + x = x.
Proof.
  intros x y Hy H.
  replace x with 0.
  - (* preuve du but avec x remplacé par 0 *)
    rewrite Rplus_0_r. reflexivity.
  - (* preuve de l'égalité 0 = x *)
    apply (Rmult_eq_reg_r y).
    + rewrite H, Rmult_0_l. reflexivity.
    + exact Hy.
Qed.

(** **** Exercice : Prouver le théorème suivant. *)
(** Dans un premier temps, remplacer [2 * x] par [x + x].
    Pour la preuve que (2 * x) = x + x, on peut utiliser : *)
Check double.
Theorem exercice_replace : forall x : R, 2 * x + (- x) = x.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** ** La tactique [pose proof] *)

(** Pour finir de raisonner "comme en cours de maths", on a besoin d'une
    tactique qui permet l'équivalent de
    "d'après le théorème bidule, on a : machin".
    Cette tactique se nomme [pose proof].

    On peut l'utiliser pour donner une nouvelle preuve du théorème précédent. *)

Theorem exemple_pose_proof : forall x : R, 2 * x + (- x) = x.
Proof.
  intros x.
  (* D'après [double], on sait que 2 * x = x + x (E). *)
  pose proof (double x) as E.
  rewrite E.
  rewrite Rplus_assoc. rewrite Rplus_opp_r. rewrite Rplus_0_r.
  reflexivity.
Qed.
