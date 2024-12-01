From Coq Require Import Rbase Rfunctions SeqSeries Lra Lia PeanoNat.
Import Nat.
(** * Quelques tactiques automatiques de Coq *)

(** ATTENTION : l'utilisation de ces tactiques est soumise à l'autorisation de
    vos enseignants pour des raisons pédagogiques évidentes. Si on vous les
    avait présentées plus tôt, vous seriez passés à côté de beaucoup de maths
    intéressantes. *)

(** ** Tactique [easy] et notation [now] *)

(** La tactique [easy] tente de *terminer* une preuve en utilisant un certain
    nombre d'étapes élémentaires ([reflexivity], [symmetry], [assumption], ...)

    Elle fonctionne en général lorsque le but semble logiquement facile à
    démontrer. *)

Theorem easy1 (A B C : Prop) : (A -> B) -> (B -> C) -> B -> C.
Proof.
  easy.
Qed.

Theorem easy2 (A B : Prop) : A /\ B -> A.
Proof.
  easy.
Qed.

Theorem easy3 (n m : nat) : n = m + m -> m + m = n.
Proof.
  easy.
Qed.

(** La notation [now tactique] est équivalente à
    tactique; easy.
    Elle indique clairement au lecteur que la preuve (ou sous-preuve) est
    terminée par cette tactique, les détails restants étant "évidents". *)

Theorem now1 (n m k : nat) : n = k + m -> m + k = n.
Proof.
  (* Par commutativité de l'addition. *)
  now rewrite add_comm.
Qed.

(** Les tactiques ring et field. *)

(** Un anneau (en anglais ring) est en mathématique un ensemble muni :
    - d'une addition (+) commutative avec un élément neutre noté 0 où
      chaque élément a un opposé (-).
    - d'une multiplication * associative et distributive sur (+) avec un
      élément neutre noté 1.

    La tactique automatique puissante ring permet de terminer une preuve
    d'égalité "évidente" faisant intervenir addition et multiplication.
*)

Open Scope R_scope.
Theorem ring1 (x y : R) : x + y * x + x - 4 * x = x * (y - 2).
Proof.
  ring.
Qed.
Close Scope R_scope.

(* Bien que les entiers naturels ne forment pas un anneau (pas d'opposé),
   [ring] sait aussi prouver des égalités dans nat. *)

Theorem ring2 (x y : nat) : (x + y) * (x + y) = x * x + 2 * x * y + y * y.
Proof.
  ring.
Qed.

(** En mathématique, un corps (en anglais field) est un anneau où les éléments
    non nuls ont un inverse.

    La tactique field permet de prouver des égalités "évidentes" faisant
    intervenir addition, multiplication, soustraction et division. *)

Open Scope R_scope.
Theorem field1 (x y : R) : x <> 0 -> (x + y * x + x - 4 * x) / x = y - 2.
Proof.
  intros H. field.
  (* Remarquez que coq demande une preuve que x <> 0. *)
  easy.
Qed.
Close Scope R_scope.

(** Prouver des inégalités linéaires "évidentes" dans nat et R : lia et lra.
    
    lia (dans nat) et lra (dans R) prouvent des inégalités linéaires 
    (donc faisant intervenir addition et multiplication par des constantes)
    lorsqu'elles sont "évidentes".
*)

Theorem lia1 (n m : nat) : n <= m + 1 -> 3 * n < 4 * m + 10.
Proof.
  lia.
Qed.

Theorem lia2 (n m : nat) : n <= 42 -> m < 56 -> max n m <= 55.
Proof.
  lia.
Qed.

Open Scope R_scope.
Theorem lra1 (x y : R) : x > 0 -> x > y -> 5 * x > 2 * y.
Proof.
  intros H H'. lra.
Qed.

(** lra sait aussi prouver certaines égalités *)
Theorem lra2 (x y : R) : x + x + 4 * y - x = x + 4 * y.
Proof.
  lra.
Qed.
