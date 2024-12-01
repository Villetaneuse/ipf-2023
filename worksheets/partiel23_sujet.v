From Coq.Arith Require Import PeanoNat.
From Coq.Reals Require Import RIneq.

(** Instructions :
    Le sujet comporte 5 parties indépendantes :
    - Logique de base (calcul des propositions, sans tiers exclu)
    - Entiers naturels et récurrence (sans tiers exclu)
    - Calcul des prédicats (il existe, pour tout) avec tiers exclu
    - Réels, propriétés de base
    - Réels avec automatisation

    Les tactiques autorisées sont celles du cours :
    - intros
    - exact
    - apply et apply ... in
    - split
    - destruct
    - exfalso
    - exists
    - reflexivity
    - specialize
    - rewrite, rewrite <-, rewrite ... in, rewrite ... <- in et
      toutes les variantes rewrite ... at numéro
    - simpl, seulement pour triangle_0, triangle_succ, factorial_0,
      factorial_succ
    - induction
    - unfold
    - les tactiques pour le raissonnement vers l'avant :
      - assert ... as ... [by (...)]
      - replace ... with ... [by (...)]
      - pose proof ... as ...
    - lra, field, ring dans la dernière partie

    Barème indicatif et susceptible d'être modidié :
    Les exercices sans étoile comptent en fait "une demi étoile".
    Au total il y a donc 50 étoiles.
    Les 10 premières étoiles rapportent chacune 1 point.
    Les 10 suivantes rapportent chacune 0,5 point.
    Les suivantes rapportent chacune 0,25.
*)

Section LogiqueBase.

(** **** Exercice [*] : Prouver le théorème suivant. *)
Lemma conj_and : forall (A B : Prop), A -> B -> A /\ B.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** **** Exercice [*] : Prouver le théorème suivant. *)
Lemma imp_transitivity : forall (A B C : Prop), (A -> B) -> (B -> C) -> (A -> C).
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** **** Exercice [*] : Prouver le théorème suivant. *)
Lemma and_not_diag_falso : forall (A : Prop), A /\ ~A -> forall (B : Prop), B.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** **** Exercice [*] : Prouver le théorème suivant. *)
Lemma or_induction : forall (A B C : Prop), (A -> C) -> (B -> C) -> A \/ B -> C.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** **** Exercice [**] : Prouver le théorème suivant. *)
Lemma or_not_r_imp : forall (A B : Prop), B \/ ~A -> A -> B.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


End LogiqueBase.

Module Entiers.
Import Nat.

(** Vous ne pouvez pas utiliser [simpl] avec [*] et [+] *)
Opaque mul.
Opaque add.

(** On commence par utiliser des relations purement algébriques : *)
Check add_succ_l.
Check add_succ_r.
Check add_0_l.
Check add_0_r.
Check mul_0_l.
Check mul_0_r.
Check add_1_l.
Check add_1_r.
Check add_comm.
Check add_assoc.
Check mul_succ_l.
Check mul_succ_r.
Check mul_1_l.
Check mul_1_r.
Check mul_comm.
Check mul_assoc.
Check mul_add_distr_l.
Check mul_add_distr_r.

Fixpoint triangle (n : nat) :=
  match n with
    0 => 0
  | S n' => S n' + triangle n'
  end.

Compute triangle 2.
Compute triangle 5.

(** **** Exercice [] : Prouver le théorème suivant. *)
Lemma triangle_0 : triangle 0 = 0.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** **** Exercice [] : Prouver le théorème suivant. *)
Lemma triangle_succ : forall (n : nat), triangle (S n) = S n + triangle n.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


Opaque triangle.

(** **** Exercice [***] : Prouver le théorème suivant. *)
Lemma triangle_mul : 
  forall (n : nat), (triangle n) * 2 = S n * n.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


Fixpoint factorial (n : nat) :=
  match n with
    0 => 1
  | S n' => S n' * factorial n'
  end.

Compute factorial 3.
Compute factorial 5.

Notation "n !" := (factorial n) (at level 20).

(** **** Exercice [] : Prouver le théorème suivant. *)
Lemma factorial_0 : 0! = 1.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** **** Exercice [] : Prouver le théorème suivant. *)
Lemma factorial_succ : forall (n : nat), (S n)! = (S n) * n!.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** À partir de maintenant, on n'utilise plus [simpl] avec [factorial]. *)
Opaque factorial.

(** On ajoute l'ordre [<=] sur nat avec les lemmes suivants : *)
Check le_refl.
Check le_trans.
Check le_antisymm.
Check le_succ_r.
Check nle_succ_0.
Check succ_le_mono.
Check add_le_mono_l.
Check add_le_mono_r.
Check mul_le_mono_l.
Check mul_le_mono_r.
Check le_0_l.

(** **** Exercice [**] : Prouver le théorème suivant. *)
Lemma factorial_le_succ : forall (n : nat), n! <= (S n)!.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** **** Exercice [***] : Prouver le théorème suivant. *)
Lemma factorial_non_decr : forall (n m : nat), n <= m -> n! <= m!.
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


(** Enfin, on ajoute la divisibilité : *)

Print divide.
Check divide_refl.
Check divide_trans.
Check divide_antisym.

(** **** Exercice [***] : Prouver le théorème suivant. *)
Lemma facto_le_div : forall (n m : nat), n <= m -> (n! | m!).
Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


End Entiers.

(** À partir de maintenant, on rajoute le tiers exclu. *)
From Coq.Logic Require Import Classical.

Check classic.

Section PredicatsClassique.

  (** **** Exercice [*] : Prouver le théorème suivant. *)
  Lemma not_exists_forall {T : Type} (P : T ->Prop) :
    ~(exists (x : T), P x) -> forall (x : T), ~ P x.
  Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


  (** **** Exercice [*] : Prouver le théorème suivant. *)
  Lemma forall_not_exists {T : Type} (P : T -> Prop) :
    (forall (x : T), ~ P x) -> ~(exists (x : T), P x).
  Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


  (** **** Exercice [*] : Prouver le théorème suivant. *)
  Lemma PNNP : forall (P : Prop), P -> ~~P.
  Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


  (** **** Exercice [**] : Prouver le théorème suivant. *)
  Lemma NNPP : forall (P : Prop), ~~P -> P.
  Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


  (** **** Exercice [***] : Prouver le théorème suivant. *)
  Lemma not_forall_exists_not {T : Type} (P : T -> Prop) :
    ~(forall (x : T), P x) -> exists (x : T), ~ P x.
  Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


  (** **** Exercice [**] : Prouver le théorème suivant. *)
  Lemma classic_imp (P Q : Prop) : (P -> Q) -> Q \/ ~P.
  Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


  (** **** Exercice [***] : Prouver le théorème suivant. *)
  Lemma peirce (P Q : Prop) : ((P -> Q) -> P) -> P.
  Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


End PredicatsClassique.

Section RéelsBase.
  Open Scope R_scope.
  Import RIneq.
  (** Dans cette section et la suivante, vous pouvez utiliser les lemmes
      suivants : *)

Check R1_neq_R0.
Check Rinv_l.
Check Rinv_lt_contravar.
Check Rinv_r.
Check Rle_antisym.
Check Rle_ge.
Check Rle_refl.
Check Rle_trans.
Check Rlt_asym.
Check Rlt_irrefl.
Check Rlt_trans.
Check Rmult_0_l.
Check Rmult_0_r.
Check Rmult_1_l.
Check Rmult_1_r.
Check Rmult_assoc.
Check Rmult_comm.
Check Rmult_eq_compat_l.
Check Rmult_eq_compat_r.
Check Rmult_eq_reg_l.
Check Rmult_eq_reg_r.
Check Rmult_gt_0_compat.
Check Rmult_le_compat_l.
Check Rmult_le_compat_r.
Check Rmult_le_reg_l.
Check Rmult_le_reg_r.
Check Rmult_lt_compat_l.
Check Rmult_lt_compat_r.
Check Rmult_lt_reg_l.
Check Rmult_lt_reg_r.
Check Rmult_plus_distr_l.
Check Rmult_plus_distr_r.
Check Rplus_0_l.
Check Rplus_0_r.
Check Rplus_assoc.
Check Rplus_comm.
Check Rplus_eq_compat_l.
Check Rplus_eq_compat_r.
Check Rplus_eq_reg_l.
Check Rplus_eq_reg_r.
Check Rplus_le_compat_l.
Check Rplus_le_compat_r.
Check Rplus_le_reg_l.
Check Rplus_le_reg_r.
Check Rplus_lt_compat_l.
Check Rplus_lt_compat_r.
Check Rplus_lt_reg_l.
Check Rplus_lt_reg_r.
Check Rplus_opp_l.
Check Rplus_opp_r.
Check Rlt_0_1.

  (** Dans toute cette partie, on considère 2 réels a et b. *)
  Context {a b : R}.

  (** La définition de "fonction strictement croissante" est la suivante : *)
  Definition increasing (f : R -> R) :=
    forall (x y : R), x < y -> f x < f y.

  (** On considère la fonction affine [aff] suivante : *)
  Definition aff (x : R) := a * x + b.

  (** Remarque : vous aurez sans doute à [unfold aff] *)

  (** **** Exercice [**] : Prouver le théorème suivant. *)
  Lemma a_pos_aff_incr : a > 0 -> increasing aff.
  Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


  (** **** Exercice [**] : Prouver le théorème suivant. *)
  Lemma aff_incr_a_pos : increasing aff -> a > 0.
  Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


  (** **** Exercice [***] : Prouver le théorème suivant. *)
  Lemma aff_eq_0 : a <> 0 -> (forall (x : R), (aff x = 0) -> x = - b / a).
  Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


  (** **** Exercice [**] : Prouver le théorème suivant. *)
  (** Indice : [unfold Rdiv] *)
  Lemma eq_0_aff : a <> 0 -> (forall (x : R), x = - b / a -> aff x = 0).
  Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


End RéelsBase.

Require Import Lra RealField Rfunctions.
Section RéelsAuto.
  (** Dans cette partout, vous avez droit à toutes les tactiques automatiques de
      vues en cours, en particulier, [lra], [field] et [field_simplify] *)
  Open Scope R_scope.
  Import RIneq.

  Context {a q : R}.

  (** La fonction puissance est définie de la façon suivante : *)
  Print pow.

  (** **** Exercice [] : Prouver le théorème suivant. *)
  Lemma pow_0_r (x : R) : x ^ 0 = 1.
  Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


  (** **** Exercice [] : Prouver le théorème suivant. *)
  Lemma pow_succ (x : R) (n : nat) : x ^ (S n) = x * x ^ n.
  Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


  (** On définit la suite géométrique de terme initial a et de raison q de la
      façon suivante : *)
  Fixpoint geom_seq (n : nat) :=
    match n with
      0 => a
    | (S n') => q * geom_seq n'
    end.

  (** **** Exercice [] : Prouver le théorème suivant. *)
  Lemma geom_seq_0 : geom_seq 0 = a.
  Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


  (** **** Exercice [] : Prouver le théorème suivant. *)
  Lemma geom_seq_succ (n : nat) : geom_seq (S n) = q * geom_seq n.
  Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


  (** **** Exercice [***] : Prouver le théorème suivant. *)
  (** Indice : récurrence *)
  Lemma geom_eq : 
    forall (n : nat), geom_seq n = a * q ^ n.
  Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


  Fixpoint sum_geom_seq (n : nat) :=
    match n with
      0 => geom_seq 0
    | S n' => sum_geom_seq n' + geom_seq n
    end.

  (** **** Exercice [****] : Prouver le théorème suivant. *)
  (** Indices : récurrence, field, field_simplify, lra *)
  Lemma sum_geom :
    q <> 1 -> forall (n : nat), sum_geom_seq n = a * (1 - q ^ S n) / (1 - q).
  Proof.
  (* Remplir la preuve ici *)
Admitted. (* Remplacer cette ligne par Qed. *)


End RéelsAuto.
