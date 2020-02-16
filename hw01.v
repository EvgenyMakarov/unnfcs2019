Section HW2.

Variables A B C : Prop.

(** [A <-> B] — это обозначение для [iff A B], что в свою очередь значит
по определению [(A -> B) /\ (B -> A)]. В этом можно убедиться с помощью
[unfold iff]. Например, дадим временную недоказуемую цель [A <-> B]. *)

Goal A <-> B.
unfold iff.
Abort.

(** Поэтому доказывать цель вида [A <-> B] нужно тактикой [split],
а использовать посылку вида [H : A <-> B] с помощью
тактики [destruct H as [H1 H2]], где [H1] и [H2] — новые идентификаторы. *)

(** Докажите следующие формулы. Замените команду [Admitted] на доказательство,
за которым идет [Qed]. *)

Theorem hyp_syllogism : (A -> B) -> (B -> C) -> A -> C.
Proof.
Admitted.

(** У команды [Theorem] есть синонимы: [Lemma], [Remark], [Fact],
[Corollary], [Proposition] *)

Fact double_negation : A -> ~~A.
Proof.

(** [~~A] есть [(A -> False) -> False]. Для того, чтобы перенести
[A -> False] в список посылок, не обязательно говорить [unfold not]. *)

intros H1 H2.

(** [H2 : A -> False] *)

apply H2.
assumption.
Qed.

(** Проверьте, работает ли то же самое доказательство, если вместо [False]
поставить произвольную пропозициональную переменную, например, [B] *)

Corollary double_impl : A -> (A -> B) -> B.
Proof.
intros H1 H2.
apply H2.
assumption.
Qed.

Proposition disj_elim : (A \/ B -> C) <-> (A -> C) /\ (B -> C).
Proof.
split.
* intro H.
  split.
  + intro H1. apply H. left. trivial.
  + intro H1. apply H. right. trivial.
* intros H1 H2.
  destruct H1 as [H1 H1'].
  destruct H2.
  + apply H1. trivial.
  + apply H1'. trivial.
Qed.

(** Логические связки располагаются в порядке убывания приоритета
следующим образом: [~], [/\], [\/], [<->], [->] *)

Theorem conj_disj_distr : A /\ (B \/ C) <-> A /\ B \/ A /\ C.
Proof.
split.
* intro H.
  destruct H as [H1 H2].
  destruct H2.
  + left. split. trivial. trivial.
  + right. split. trivial. trivial.
* intro H.
  destruct H.
  + destruct H. split. trivial. left. trivial.
  + destruct H. split. trivial. right. trivial.
Qed.

Theorem disj_conj_distr : A \/ B /\ C <-> (A \/ B) /\ (A \/ C).
Proof.
Admitted.

Theorem deMorgan : ~(A \/ B) <-> ~A /\ ~B.
Proof.
split.
* intro H. split.
  + intro H1. apply H. left. trivial.
  + intro H1. apply H. right. trivial.
* 

End HW2.
