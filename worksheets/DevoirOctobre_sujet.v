From Coq.Arith Require Import PeanoNat.
Import Nat.

(** * Consignes *)

(**
    Ce devoir est à rendre sur le dépôt moodle avant le :
      dimanche 5 novembre à 23h59

    Vous rendrez un seul fichier appelé [DevoirOctobre.v] et complèterez la 
    déclaration suivante ci-dessous :

    NOM, prénom, numéro étudiant : Je déclare qu'il s'agit de mon propre
    travail.

    C'est un travail individuel. Vous pouvez vous aider les uns les autres mais
    vous ne devez jamais vous montrer le code de votre solution. L'usage de
    ChatGPT ou de toute autre intelligence artificielle pour résoudre les
    exercices est interdit (vous pouvez à la limite lui poser des questions sur
    des points mal compris). Si vous avez des questions (autres que "comment
    résoudre cet exercice"), vous pouvez les poser (en anglais) sur :
    [https://coq.zulipchat.com/] dans le "stream" Coq Users (nécessite une
    inscription avec une adresse mail). Il est possible aussi d'envoyer des
    mails à [rousselin@univ-paris13.fr].

    Le premier but de ce devoir est de vous faire progresser en mathématiques et
    en informatique.

Le deuxième est que tous les étudiants soient bien à jour pour attaquer la
    dernière partie du cours sur les nombres réels.

    Il y a 3 parties inégales et indépendentes.

    - Partie 1 : calcul des propositions. Cette partie revient sur le contenu du
      premier TP pour s'assurer que vous avez des bases suffisantes en logique.
    - Partie 2 : entiers naturels et ordre [<=]. Cette partie est la plus
      fournie. En partant de trois propriétés admise de [<=], vous aurez à
      prouver les propriétés usuelles de [<=]. Pour la traiter, il est nécessaire
      d'avoir terminé le deuxième TP.
    - Partie 3 : entiers naturels et divisibilité. On introduit un autre ordre
      sur Nat, qui n'est pas total. Pour traiter cette partie, il est nécessaire
      d'avoir terminé le troisième TP (pour le quantificateur "il existe").

    Il n'est pas nécessaire de traiter tous les exercices pour avoir une bonne
    note. Vous pouvez toujours admettre un théorème pour l'utiliser _plus tard_
    dans le devoir.

    Vous utiliserez les tactiques :
    - [intros]
    - [unfold]
    - [exact]
    - [split]
    - [destruct] pour : un [/\], un [\/], une preuve de [False], un [exists]
      ou un entier naturel (preuve par cas)
    - [left/right]
    - [exfalso]
    - [reflexivity]
    - [apply] et [apply ... in]
    - [apply <-] et [apply ->] avec ou sans [in] pour appliquer des équivalences
      (voir partie 2)
    - [rewrite], [rewrite <-], [rewrite ... in] et [rewrite <- ... in]
    - [discriminate]
    - [induction]
    - [specialize]
    - (|simpl] est autorisé mais déconseillé, il n'est pas utilisé dans le
       corrigé, on peut faire le devoir sans)

    Pour les parties 2 et 3, vous pouvez utiliser les théorèmes déjà prouvés
    précédemment ainsi que les résultats déjà vus dans le TP2 (et les exercices
    supplémentaires) qui sont :
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
    - [mul_assoc : ∀ n m p : nat, n * (m * p) = (n * m) * p]
    - [mul_add_distr_l : ∀ n m p : nat, n * (m + p) = n * m + n * p]
    - [mul_add_distr_l : ∀ n m p : nat, (n + m) * p = n * p + m * p]

    D'autres nouveaux théorèmes que vous aurez à utiliser seront présentés au
    cours du devoir.

    Il est aussi possible d'utiliser les théorèmes généraux et élémentaires :
    - [iff_refl : ∀ A : Prop, A <-> A]
    - [iff_trans : ∀ A B C : Prop, A <-> B -> B <-> C -> A <-> C]
    - [f_equal : ∀ (A B : Type) (f : A -> B) (x y : A), x = y -> f x = f y]
    - [eq_sym : ∀ (A : Type) (x y : A), x = y -> y = x]
*)
(** * Partie 1 : Calcul des propositions *)

(** **** Exercice : Prouver le théorème suivant. *)

Theorem P1_ex1 : forall (P Q R : Prop), (P -> Q) -> ((Q -> R) -> (P -> R)).
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** **** Exercice : Prouver le théorème suivant. *)
Theorem P1_ex2 : forall (P Q : Prop), ~(P \/ Q) <-> ~P /\ ~Q.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** **** Exercice : Prouver le théorème suivant. *)
Theorem P1_ex3 : forall (P Q : Prop), ~P \/ ~Q -> ~(P /\ Q).
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** **** Exercice : Prouver le théorème suivant. *)
Theorem P1_ex4 : forall (P : Prop), (((P \/ ~P) -> False) <-> False).
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** Partie 2 : entiers naturels et ordre [<=] *)

(** L'ordre [<=] sur les entiers naturels est défini sur les entiers naturels
    d'une certaine façon, qui est hors du programme de ce cours. On peut
    cependant prouver toutes ses propriétés en admettant les trois propriétés
    suivantes, qu'on utilisera comme des axiomes.
*)

Check le_0_l.
Check nle_succ_0.
Check succ_le_mono.

(** Une remarque sur succ_le_mono : c'est une équivalence. Pour l'utiliser comme
    une implication, utiliser [apply ->succ_le_mono] ou [apply <-succ_le_mono],
    suivant le sens que l'on veut. *)

(** Par exemple, on peut prouver les deux résultats suivants "à la main". *)

Theorem exemple_le_1 : 2 <= 4.
Proof.
  apply ->succ_le_mono.
  apply ->succ_le_mono.
  exact (le_0_l 2).
Qed.

Theorem exemple_le_2 : ~(3 <= 2).
Proof.
  intros H.
  apply <-succ_le_mono in H.
  apply <-succ_le_mono in H.
  apply (nle_succ_0 0).
  exact H.
Qed.

(** À partir de maintenant, on va établir les propriétés usuelles de [<=] sur
    les entiers naturels. *)

(** D'abord, on va prouver que c'est une relation d'ordre, c'est-à-dire que
    c'est une relation réflexive, transitive et antisymétrique. *)

(** **** Exercice : Prouver le théorème suivant. *)
(** Indice: [induction]. *)
Theorem le_refl : forall n, n <= n.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** **** Exercice : Prouver le théorème suivant. *)
(** Indices : pas d'induction, faire une preuve _par cas_ sur n. Penser
    à [exfalso] si c'est pertinent. *)
Theorem le_0_r : forall n : nat, n <= 0 <-> n = 0.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** Pour faciliter la preuve de l'antisymétrie, on va avoir besoin du théorème
    suivant, général et très utile.

    Il dit que, quelle que soit la fonction [f], pour prouver que [f x = f y],
    il suffit de prouver que [x] est égal à [y]. *)
(** **** Exercice : Prouver le théorème suivant. *)
Theorem f_equal :
  forall (A B : Type) (f : A -> B) (x y : A), x = y -> f x = f y.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** **** Exercice : Prouver le théorème suivant (assez difficile). *)
(** Indication : ne pas changer la première ligne. Elle permet d'avoir une
    hypothèse de récurrence universellement quantifiée et on en a besoin.
    Dans la deuxième partie de la preuve, raisonner par cas sur [m] de
    façon à pouvoir utiliser [succ_le_mono].
*)
Theorem le_antisymm : forall n m : nat, n <= m -> m <= n -> n = m.
Proof.
  induction n as [| n' IH].
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** **** Exercice : Prouver le théorème suivant (assez difficile). *)
(** Indication : ne pas changer la première ligne. Elle permet d'avoir une
    hypothèse de récurrence universellement quantifiée et on en a besoin.
    La preuve est dans la même veine que [le_antisym], il faudra raisonner
    par cas sur [m] et [p].
*)
Theorem le_trans : forall n m p, n <= m -> m <= p -> n <= p.
Proof.
  induction n as [| n' IH].
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** Maintenant, il faut montrer que l'ordre [<=] est total, c'est-à-dire que
    deux entiers naturels sont toujours comparables. *)
(** **** Exercice : Prouver le théorème suivant (assez difficile). *)
Theorem le_ge_cases : forall n m : nat, n <= m \/ m <= n.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** Maintenant, on va établir des propriétés de compatibilité entre l'addition
    et l'ordre. *)

(** **** Exercice : Prouver le théorème suivant. *)
Theorem le_add_l : forall n m : nat, n <= m + n.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** **** Exercice : Prouver le théorème suivant. *)
(** Ne pas utiliser d'induction. Utiliser [add_comm] et le théorème précédent.
*)
Theorem le_add_r : forall n m : nat, n <= n + m.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** **** Exercice : Prouver le théorème suivant. *)
(** Indice: la récurrence doit porter sur [p].
    Il y a plusieurs façons de procéder. La plus rapide est sans doute
    de raisonner directement par équivalence.
    Dans ce cas, vous pouvez utiliser les théorèmes [iff_refl] et
    [iff_trans].
*)
Theorem add_le_mono_l : forall n m p : nat, n <= m <-> p + n <= p + m.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** **** Exercice : Prouver le théorème suivant. *)
(** Ne pas utiliser d'induction. Utiliser [add_comm] et le théorème précédent.
*)
Theorem add_le_mono_r : forall n m p : nat, n <= m <-> n + p <= m + p.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** **** Exercice : Prouver le théorème suivant. *)
(** Ne pas utiliser d'induction. Utiliser [le_trans] et les résultats
    précédents. *)
Theorem add_le_mono : forall n m p q : nat, n <= m -> p <= q -> n + p <= m + q.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** On passe à la compatibilité avec la multiplication. *)
(** **** Exercice : Prouver le théorème suivant. *)
Theorem mul_le_mono_l : forall n m p : nat, n <= m -> p * n <= p * m.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** **** Exercice : Prouver le théorème suivant. *)
(** Ne pas utiliser d'induction. *)
Theorem mul_le_mono_r : forall n m p : nat, n <= m -> n * p <= m * p.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** **** Exercice : Prouver le théorème suivant. *)
(** Ne pas utiliser d'induction. *)
Theorem mul_le_mono : forall n m p q : nat, n <= m -> p <= q -> n * p <= m * q.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** Partie 3 : un autre ordre sur Nat, la relation de divisibilité. *)

(** On dit qu'un entier [x] _divise_ un entier [y] (notation : [x | y])
    lorsqu'il existe un entier [z] tel que [y = z * x]. *)
Print divide.

(** D'abord quelques propriétés simples : *)
(** **** Exercice : Prouver le théorème suivant. *)

Theorem divide_1_l : forall n : nat, (1 | n).
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** **** Exercice : Prouver le théorème suivant. *)
Theorem divide_0_r: forall n : nat, (n | 0).
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** Cette relation de divisibilité est réflexive. *)
(** **** Exercice : Prouver le théorème suivant. *)
(** Si vous avez besoin de vous rappeler de la définition de [divide],
    n'hésitez pas à [unfold divide].
    Rappelez-vous comment prouver un énoncé du type "il existe".
*)
Theorem divide_refl : forall n : nat, (n | n).
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** Cette relation est de plus transitive. *)
(** **** Exercice : Prouver le théorème suivant. *)
(** Rappelez-vous comment utiliser un énoncé du type "il existe". *)
Theorem divide_trans : forall n m p : nat, (n | m) -> (m | p) -> (n | p).
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** Enfin, c'est une relation antisymétrique. *)
(** **** Exercice : Prouver le théorème suivant (assez difficile). *)
(** Vous pourrez utiliser les théorèmes suivants : *)
Check mul_id_l.
Check mul_id_r.
Check mul_eq_1.
(** Ainsi que : *)
Theorem eq_sym : forall (A : Type) (x y : A), x = y -> y = x.
Proof. intros A x y H. rewrite H. reflexivity. Qed.

Theorem divide_antisym : forall n m : nat, (n | m) -> (m | n) -> n = m.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** Mais elle n'est pas totale, par exemple on a : *)
(** **** Exercice : Prouver le théorème suivant (assez difficile). *)
(** Indice : on pourra raisonner par cas sur l'entier k tel que 2 = k * 3 et
    utiliser [simpl] et [discriminate] pour demander à Coq de trouver une
    contradiction "par calcul". *)
Theorem divide_2_3_not_comparable : ~((2 | 3) \/ (3 | 2)).
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)

(** Enfin, quelques proporiétés faciles de la divisibilité en lien avec
    l'addition et la multiplication : *)

(** **** Exercice : Prouver le théorème suivant. *)
Theorem divide_add_r : forall n m p : nat, (n | m) -> (n | p) -> (n | m + p).
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** **** Exercice : Prouver le théorème suivant. *)
Theorem mul_divide_mono_r: forall n m p : nat, (n | m) -> (n * p | m * p).
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** **** Exercice : Prouver le théorème suivant. *)
Theorem divide_mul_r: forall n m p : nat, (n | p) -> (n | m * p).
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)

