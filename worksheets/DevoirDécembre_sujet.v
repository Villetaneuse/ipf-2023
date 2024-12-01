Set Keyed Unification.
From Coq Require Import PeanoNat.

(** * Devoir à la maison Décembre 2023 *)

(** ** Consignes *)

(** Ce devoir est à rendre sur moodle **avant le 11 décembre 23h59**. *)

(** Il y a trois parties, faîtes ce que vous pouvez, sans angoisse. Idéalement,
    vous touchez un peu aux trois parties. *)

(** Barème prévisionnel :
    - les 3 premiers exercices réussis rapportent 2 points chacun
    - les 6 exercices réussis suivant rapportent 1 point chacun
    - les exercices réussis au-delà du 9ème rapportent 0,5 point chacun.

    Le but est qu'il soit facile d'avoir 10, difficile d'avoir 20.

    A priori la note d'EvC sera calculée avec un coefficient 2 sur la meilleure
    note.

    Des étoiles indiquent la difficulté de l'exercice.
    - [*] indique que la solution tient en une ligne.
    - [**] que c'est un peu plus long mais a priori pas difficile
    - [***] que c'est un peu plus difficile
    - [****] (difficile) ou [*****] (très difficile) indiquent clairement que
      c'est à faire après avoir fait le reste, s'il reste du temps.

    Warning: votre enseignant n'est plus très compétent pour juger de la
    difficulté des exercices.
    Si vous trouvez qu'un exercice est mal "étoilé", n'hésitez pas à le dire en
    commentaire (et encore mieux dire pourquoi).

    Les solutions partielles ne rapportent pas de point, mais m'aident beaucoup
    à comprendre vos difficultés. N'hésitez pas à les laisser.

   En principe, vous n'avez pas le droit d'utiliser des lemmes dont le nom
   commence par [Nat.] ou [RIneq.] (le but est de vous empêcher "d'utiliser A
   pour prouver A").

   Vous pouvez utiliser :
   - les lemmes donnés en début de chaque partie.
   - les lemmes qui précèdent (même si vous n'arrivez pas à les prouver).
   - pour les trois derniers exercices, un peut tout ce que vous voulez.

   Si vous pensez que j'ai oublié un lemme important, contactez-moi rapidement.
   
   Vous pouvez énoncer et prouver des lemmes qui vous servent, mais a priori,
   ce n'est pas nécessaire.

   Et aussi, amusez-vous bien.
*)

(** Tactiques autorisées :
    - exact
    - intros
    - apply
    - apply ... in
    - split
    - destruct
    - rewrite
    - rewrite ... in ...
    - rewrite <-
    - rewrite <- .. in ...
    - exfalso
    - discriminate
    - exists 
    - unfold 
    - specialize
    - pose proof
    - reflexivity
    - symmetry
    - replace ... with ...
    - replace ... with ... in ...
    - assert
    - simpl (seulement dans les deux premiers exercices)
    - induction

    - field et lra pour les trois derniers exercices.

   Si vous pensez que j'ai oublié une tactique importante, contactez-moi
   rapidement.
  
   Les lemmes [eq_sym] et [f_equal], d'intérêt général, peuvent être utilisés
   dans tout le sujet.
*)

Check eq_sym.
Check f_equal.

(** ** Entiers naturels et récurrence *)

Section NaturelsPuissance.

Import Nat(
  add, add_0_l, add_0_r, add_1_l, add_1_r, add_comm, add_assoc, add_succ_l,
  add_succ_r,
  mul, mul_0_l, mul_0_r, mul_1_l, mul_1_r, mul_comm, mul_assoc, mul_succ_l,
  mul_succ_r, mul_add_distr_l, mul_add_distr_r, neq_succ_0).
  
(** On part des entiers avec presque rien. Les seuls lemmes utilisables sont
    - [add_0_l]
    - [add_0_r]
    - [add_1_l]
    - [add_1_r]
    - [add_comm]
    - [add_assoc]
    - [add_succ_l]
    - [add_succ_r]
    - [mul_0_l]
    - [mul_0_r]
    - [mul_1_l]
    - [mul_1_r]
    - [mul_comm]
    - [mul_assoc]
    - [mul_succ_l]
    - [mul_succ_r]
    - [mul_add_distr_l]
    - [mul_add_distr_r]
    - [neq_succ_0]
*)

Disable Notation "_ ^ _".
Arguments mul : simpl never.
Arguments add : simpl never.
(** Vous n'avez pas le droit d'utiliser [simpl] avec [+] et [*]. *)

(** Définition de la fonction puissance sur [nat]. *)

(** On définit la puissance par récurrence :
    - [n ^ 0 = 1] (y compris si [n = 0])
    - [n ^ (S m) = n * (n ^ m)] *)
Fixpoint pow (n m : nat) :=
  match m with
    0 => 1
  | (S m0) => n * (pow n m0)
  end.

(** La notation est [n ^ m] pour "n puissance m". *)
Infix "^" := pow.

(** On commence par énoncer et prouver les deux règles de calcul qui
    définissent la puissance *)

(** **** Exercice [*] : Prouver le théorème suivant. *)
(** Ici vous devez utiliser [simpl]. *)
Lemma pow_0_r : forall (n : nat), n ^ 0 = 1.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** **** Exercice [*] : Prouver le théorème suivant. *)
(** Ici vous devez utiliser [simpl]. *)
Lemma pow_succ_r : forall (n m : nat), n ^ (S m) = n * n ^ m.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** À partir de maintenant, on n'utilise plus [simpl]. *)
Arguments pow : simpl never.

(** **** Exercice [**] : Prouver le théorème suivant. *)
Lemma pow_0_l : forall (m : nat), m <> 0 -> 0 ^ m = 0.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** **** Exercice [**] : Prouver le théorème suivant. *)
Lemma pow_1_r : forall (n : nat), n ^ 1 = n.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** **** Exercice [**] : Prouver le théorème suivant. *)
Lemma pow_1_l : forall (m : nat), 1 ^ m = 1.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** **** Exercice [***] : Prouver le théorème suivant. *)
Lemma pow_add_r : forall (n m p : nat), n ^ (m + p) = n ^ m * n ^ p.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** **** Exercice [***] : Prouver le théorème suivant. *)
Lemma pow_mul_l : forall (n m p : nat), (n * m) ^ p = n ^ p * m ^ p.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** **** Exercice [***] : Prouver le théorème suivant. *)
Lemma pow_mul_r : forall (n m p : nat), n ^ (m * p) = (n ^ m) ^ p.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** **** Exercice [***] : Prouver le théorème suivant. *)
Lemma mul_eq_0 : forall (n m : nat), n * m = 0 <-> n = 0 \/ m = 0.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** **** Exercice [***] : Prouver le théorème suivant. *)
Lemma pow_eq_0 : forall (n m : nat), n ^ m = 0 <-> m <> 0 /\ n = 0.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** **** Exercice [***] : Prouver le théorème suivant. *)
Lemma mul_eq_1_subproof : forall n m : nat, n * m = 1 -> n = 1.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** **** Exercice [***] : Prouver le théorème suivant. *)
Lemma mul_eq_1 : forall n m : nat, n * m = 1 <-> n = 1 /\ m = 1.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** **** Exercice [***] : Prouver le théorème suivant. *)
Lemma pow_eq_1 : forall (n m : nat), n ^ m = 1 <-> n = 1 \/ m = 0.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)

End NaturelsPuissance.

(** ** Prédicats et logique classique *)

(** On commence par un résultat toujours valable : *)
(** **** Exercice [*] : Prouver le théorème suivant. *)
Lemma PNNP (A : Prop) : A -> ~~A.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** On se donne, en plus des règles logiques habituelles, le tiers-exclus: *)
Require Import Coq.Logic.Classical_Prop(classic).
Check classic.

(** Le tiers-exclu implique en particulier qu'on peut prouver des formules par
    l'absurde. *)

(** **** Exercice [**] : Prouver le théorème suivant. *)
Lemma NNPP (A : Prop) : ~~ A -> A.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** Grace au tiers-exclu, on peut prouver des implications par contraposition : *)

(** **** Exercice [**] : Prouver le théorème suivant. *)
Lemma contrapose (A B : Prop) : (~B -> ~A) -> (A -> B).
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** On va travailler avec les nombres réels pour avoir des exemples simples
    de prédicats (égalité, ordres), mais les réels ne jouent pas de rôle
    particulier ici. *)
Require Import Rdefinitions.
Require Import RIneq(Rlt_not_le, Rnot_lt_le, Rle_not_lt, Rnot_le_lt).

Section PrédicatsLogiqueClassique.
Open Scope R_scope.
(* On se donne une fonction quelconque f, de R dans R *)
Context (f : R -> R).

(* On se servira des résultats suivants : *)
Check Rlt_not_le.
Check Rnot_lt_le.
Check Rle_not_lt.
Check Rnot_le_lt.

(* Voici un premier exemple d'équivalence classique. *)
Lemma exemple : ~(forall (x y : R), x < y -> f x < f y) <->
              exists (x y : R), x < y /\ f y <= f x.
Proof.
  split.
  - (* On raisonne par contraposition. On suppose qu'il n'existe pas de
       réels x et y tels que x < y et f y <= f x. *)
    apply contrapose. intros H.
    (* On doit prouver que quels que soient les réels x et y, si x < y, alors
       f x < f y. *)
    (* Soient x et y deux réels tels que x < y. *)
    apply PNNP. intros x y Hxy.
    (* On raisonne par l'absurde : supposons que f y <= f x. *)
    apply NNPP. intros H'. apply Rnot_lt_le in H'.
    (* Alors on a trouvé x et y tels que à la fois x < y et f y <= f x,
       ce qui est exclu par hypothèse. *)
    apply H. exists x. exists y. split.
    + exact Hxy.
    + exact H'.
  - intros [x [y [H1 H2]]] H3.
    specialize (H3 x y H1).
    apply Rlt_not_le in H3. apply H3. exact H2.
Qed.

(** **** Exercice [**] : *)
(** Dans l'énoncé suivant, remplacer [True] par une formule sans négation,
    équivalente à la première (les non-égalités ([x <> y]) sont autorisées).
    Ensuite, prouver cette formule.
*)
Lemma ex1 : ~(forall x, f x = 0 \/ f x = 1) <->
  True.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** **** Exercice [***] : *)
(** Dans l'énoncé suivant, remplacer [True] par une formule sans négation,
    équivalente à la première (les non-égalités ([x <> y]) sont autorisées).
    Ensuite, prouver cette formule.
*)
Lemma ex2 : ~(forall (x y : R), f x = f y -> x = y) <->
  True.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** **** Exercice [***] : *)
(** Dans l'énoncé suivant, remplacer [True] par une formule sans négation,
    équivalente à la première (les non-égalités ([x <> y]) sont autorisées).
    Ensuite, prouver cette formule.
*)
Lemma ex3 : ~(exists (x : R), forall (y : R), f x <= f y) <->
  True.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** **** Exercice [***] : *)
(** Dans l'énoncé suivant, remplacer [True] par une formule sans négation,
    équivalente à la première (les non-égalités ([x <> y]) sont autorisées).
    Ensuite, prouver cette formule.
*)
Lemma ex4 :
  ~(exists (T : R), forall (x : R), f (x + T) = f x) <->
  True.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)

End PrédicatsLogiqueClassique.

(** ** Quelques résultats sur les réels (d'après le Partiel 2022) *)

Section Réels.
Open Scope R_scope.
Search _ in Raxioms.
Import Raxioms(
  Rmult_comm, Rmult_assoc, Rinv_l, Rmult_1_l,
  Rplus_comm, Rplus_assoc, Rplus_opp_r, Rplus_0_l,
  Rmult_plus_distr_l,
  Rlt_asym, Rlt_trans,
  Rplus_lt_compat_l, Rmult_lt_compat_l,
  R1_neq_R0).

Import RIneq(
  Rlt_irrefl,
  Rle_refl, Rle_trans, Rle_antisym,
  Rle_ge, Rge_le, Rge_refl, Rge_trans, Rge_antisym,
  Rgt_irrefl,
  Rmult_1_r, Rmult_0_l, Rmult_0_r, Rinv_r,
  Rplus_0_r, Rplus_opp_l,
  Rmult_plus_distr_r,
  Rplus_eq_compat_l, Rplus_eq_compat_r, Rplus_eq_reg_r, Rplus_eq_reg_l, 
  Rmult_eq_compat_l, Rmult_eq_compat_r, Rmult_eq_reg_r, Rmult_eq_reg_l, 
  Rplus_lt_compat_r, Rplus_lt_reg_r, Rplus_lt_reg_l, 
  Rmult_lt_compat_r, Rmult_lt_reg_r, Rmult_lt_reg_l, 
  Rplus_le_compat_l, Rplus_le_compat_r, Rplus_le_reg_r, Rplus_le_reg_l, 
  Rmult_le_compat_l, Rmult_le_compat_r, Rmult_le_reg_r, Rmult_le_reg_l, 
  Rmult_gt_0_compat,
  Rinv_lt_contravar
).

(** Vous pourrez utiliser les théorèmes suivants **)
Check Rmult_comm.
Check Rmult_assoc.
Check Rinv_l.
Check Rmult_1_l.
Check Rplus_comm.
Check Rplus_assoc.
Check Rplus_opp_r.
Check Rplus_0_l.
Check Rmult_plus_distr_l.
Check Rlt_asym.
Check Rlt_trans.
Check Rplus_lt_compat_l.
Check Rmult_lt_compat_l.
Check R1_neq_R0.
Check Rlt_irrefl.
Check Rle_refl.
Check Rle_trans.
Check Rle_antisym.
Check Rle_ge.
Check Rge_le.
Check Rge_refl.
Check Rge_trans.
Check Rge_antisym.
Check Rgt_irrefl.
Check Rmult_1_r.
Check Rmult_0_l.
Check Rmult_0_r.
Check Rinv_r.
Check Rplus_0_r.
Check Rplus_opp_l.
Check Rmult_plus_distr_r.
Check Rplus_eq_compat_l.
Check Rplus_eq_compat_r.
Check Rplus_eq_reg_r.
Check Rplus_eq_reg_l.
Check Rmult_eq_compat_l.
Check Rmult_eq_compat_r.
Check Rmult_eq_reg_r.
Check Rmult_eq_reg_l.
Check Rplus_lt_compat_r.
Check Rplus_lt_reg_r.
Check Rplus_lt_reg_l.
Check Rmult_lt_compat_r.
Check Rmult_lt_reg_r.
Check Rmult_lt_reg_l.
Check Rplus_le_compat_l.
Check Rplus_le_compat_r.
Check Rplus_le_reg_r.
Check Rplus_le_reg_l.
Check Rmult_le_compat_l.
Check Rmult_le_compat_r.
Check Rmult_le_reg_r.
Check Rmult_le_reg_l.
Check Rmult_gt_0_compat.
Check Rinv_lt_contravar.
                 
(** **** Exercice [**] : Prouver le théorème suivant. *)
Theorem Rmult_2 : forall a, 2 * a = a + a.
Proof.
  (* Aide pour le début : *)
  intros a. replace 2 with (1 + 1) by reflexivity.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** **** Exercice [**] : Prouver le théorème suivant. *)
Lemma Rgt_0_not_0 :
  forall x, x > 0 -> x <> 0.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** **** Exercice [**] : Prouver le théorème suivant. *)
Theorem Rinv_lt_contravar' :
  forall x y, x > 0 -> y > 0 -> x < y -> / y < / x.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** Quelques théorèmes de "changements de côté" *)

(** **** Exercice [***] : Prouver le théorème suivant. *)
Lemma Rplus_eq_chsd_rr :
  forall (x y z : R), x + y = z -> x = z - y.
Proof.
  unfold Rminus.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** **** Exercice [***] : Prouver le théorème suivant. *)
Lemma Rmult_lt_chsd_rr :
  forall (x y z : R), y > 0 -> x * y < z -> x < z / y.
Proof.
  unfold Rdiv.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** À partir de maintenant, vous pouvez utiliser [field] et [lra] *)

Require Import Lra RealField.
Require Import RIneq.

(** **** Exercice [*] : Prouver le théorème suivant. *)
Lemma Rle_minus_nneg : forall (x y : R), x <= y <-> 0 <= y - x.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** **** Exercice [***] : Prouver le théorème suivant. *)
(** D'abord, cherchez une preuve sur papier !
    Vous pouvez utiliser [assert] ou [replace] et [field] ou [lra] pour les
    calculs intermédiaires. *)
(** Enfin, le résultat clé sera (comme souvent avec les réels) : *)
Check Rle_0_sqr.
(** La fonction carré se nomme [Rsqr], on peut [unfold Rsqr]. *)
Lemma inegalite_utile : forall (x y : R), 2 * x * y <= x² + y².
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** Exercice [****] : signe d'une fonction polynôme de degré 2 *)

(** Pour s'amuser, un dernier boss (pas forcément dur, mais qui prend du temps).
    Ici, vous avez droit à tout.

    Il faut déjà savoir le faire sur papier.
*)
    
(** Pour information, quelques lemmes qui peuvent servir : *)
Check Rge_gt_trans.
Check Rgt_0_not_0.
Check Rgt_minus.
Check Rinv_0_lt_compat.
Check Rinv_0_lt_compat.
Check Rle_0_sqr.
Check Rle_0_sqr.
Check Rle_ge.
Check Rlt_0_sqr.
Check Rlt_0_sqr.
Check Rmult_0_l.
Check Rmult_gt_0_compat.
Check Rmult_lt_compat_r.
Check Ropp_gt_lt_0_contravar.
Check Rplus_le_lt_0_compat.
(** J'ai aussi [unfold Rdiv], [unfold Rsqr] et utilisé [lra] et [field].
    Ma solution comporte aussi [replace] et [assert]. *)

Lemma polynome2_positif (a b c : R) : a > 0 -> (b² - 4 * a * c < 0) ->
  forall x, a * x² + b * x + c > 0.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)

End Réels.
