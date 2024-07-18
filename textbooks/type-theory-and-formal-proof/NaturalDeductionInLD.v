(* 
Make sure '-noinit' opton is applied, so coq is naked 
In this source file, Appendix A.1 and Chapter 11 from the textbook will be formalized
See https://www.amazon.com/Type-Theory-Formal-Proof-Introduction/dp/110703650X
*)

Require Import Ltac.

Notation "A -> B" := (forall (_ : A), B) (at level 99, right associativity).

(* Appendix A.1 Constructive propositional logic *)

Definition imp (A B:Prop) : Prop := A -> B.
Notation "A ⇒ B" := (imp A B)(at level 51, right associativity).
Definition imp_in (A B:Prop) (u: A -> B) : A ⇒ B.
exact u.
Defined.

Definition imp_el (A B:Prop) (u: A ⇒ B) (a: A) : B.
unfold imp in u.
exact (u a).
Defined.

Definition absurdity  := (forall (A: Prop), A): Prop.
Notation "⊥" := absurdity.

Definition abs_in (A: Prop) (u: A) (v: A ⇒ ⊥) : ⊥.
unfold imp in v.
apply v in u.
exact u.
Defined.

Definition abs_el (A: Prop) (u: ⊥) : A.
unfold absurdity in u.
exact (u A).
Defined.

Definition neg (A: Prop) := (A ⇒ ⊥): Prop.
Notation "¬ A" := (neg A) (at level 50).

Definition neg_in (A: Prop) (u: A -> ⊥) : (¬ A).
exact u.
Defined.

Definition neg_el (A: Prop) (u: ¬ A) (v: A) : ⊥.
unfold neg in u.
unfold imp in u.
apply u in v.
exact v.
Defined.

Definition conj (A B: Prop) := (forall C, (A -> B -> C) -> C): Prop.
Notation "A ∧ B" := (conj A B) (at level 99).

Definition conj_in (A B: Prop) (a: A) (b: B) :  A ∧ B.
unfold conj.
intros C h.
exact (h a b). 
Defined.

Definition conj_el_1 (A B: Prop) (u: A ∧ B):  A.
unfold conj in u.
pose proof (u A).
apply H.
intros.
exact H0.
Defined.

Definition conj_el_2 (A B: Prop) (u: A ∧ B):  B.
pose proof (u B).
apply H.
intros.
exact H1.
Defined.

Definition disj (A B: Prop) := (forall C, (A -> C) -> (B -> C) -> C): Prop.
Notation "A ∨ B" := (disj A B) (at level 99).

Definition disj_in_1 (A B: Prop) (u: A) :  A ∨ B.
unfold disj.
intros.
exact (H u).
Defined.

Definition disj_in_2 (A B: Prop) (u: B) :  A ∨ B.
unfold disj.
intros.
exact (H0 u).
Defined.

Definition disj_el (A B C: Prop) (u: A ∨ B) (v: A ⇒ C) (w: B ⇒ C) :  C.
unfold disj in u.
pose proof (u C).
apply H.
unfold imp in v.
exact v.
exact w.
Defined.

Definition biimpl (A B: Prop) := (A ⇒ B) ∧ (B ⇒ A).
Notation "A ⇔ B" := (biimpl A B) (at level 99).

Definition biimpl_in (A B: Prop) (u: A ⇒ B) (v: B ⇒ A) :  A ⇔ B.
unfold biimpl.
pose proof (conj_in (A ⇒ B) (B ⇒ A)).
apply H.
exact u.
exact v.
Defined.

Definition biimpl_el_1 (A B: Prop) (u: A ⇔ B) :  A ⇒ B.
unfold biimpl in u.
pose proof conj_el_1 (A ⇒ B) (B ⇒ A) u.
exact H.
Defined.

Definition biimpl_el_2 (A B: Prop) (u: A ⇔ B) :  B ⇒ A.
unfold biimpl in u.
pose proof conj_el_2 (A ⇒ B) (B ⇒ A) u.
exact H.
Defined.

Axiom exc_thrd : forall A, A ∨ (¬ A).

Definition DN_in (A: Prop) (u: A) : ¬¬ A.
unfold neg.
intro.
exact (H u).
Defined.

Definition DN_el (A: Prop) (u: ¬¬ A) : A.
pose proof (exc_thrd A).
unfold disj in H.
pose proof H A.
apply H0.
intro.
exact H1.
intro.
unfold neg in u.
unfold neg in H1.
pose proof u H1.
pose proof H2 A.
exact H3.
Defined.

Definition disj_in_alt_1 (A B: Prop) (u: ¬A ⇒ B): A ∨ B.
unfold disj.
intros.
pose proof (exc_thrd A).
unfold imp in u.
pose proof disj_el A (¬A) C.
apply H2.
apply H1.
pose proof imp_in A C.
apply H3.
apply H.
unfold imp.
intro.
apply H0.
apply u.
apply H3.
Defined.

Definition disj_in_alt_2 (A B: Prop) (u: ¬B ⇒ A): A ∨ B.
unfold disj.
intros.
pose proof (exc_thrd B).
unfold imp in u.
pose proof disj_el B (¬B) C.
apply H2.
apply H1.
pose proof imp_in B C.
apply H3.
apply H0.
unfold imp.
intro.
apply H.
apply u.
apply H3.
Defined.

Definition disj_el_alt_1 (A B: Prop) (u: A ∨ B) (v: ¬A ): B.
unfold disj in u.
pose proof u B.
apply H.
unfold neg in v.
intro.
pose proof abs_in A H0 v.
pose proof abs_el B H1.
apply H2.
intro.
apply H0.
Defined.

Definition disj_el_alt_2 (A B: Prop) (u: A ∨ B) (v: ¬B ): A.
unfold disj in u.
pose proof u A.
apply H.
unfold neg in v.
intro.
apply H0.
intro.
pose proof abs_in B H0 v.
pose proof abs_el A H1.
apply H2.
Defined.

Definition all (S: Set) (P: S->Prop) := forall x: S, P x.

Declare Scope type_scope.
Notation "'∀' x . p" := (all _ (fun x => p))
  (at level 200, x binder, right associativity,
   format "'[' '∀' '/ ' x . '/ ' p ']'").


Definition all_in (S: Set) (P: S->Prop) (u: forall x: S, P x) : ∀ x: S. P x.
unfold all.
intro.
pose proof u x.
exact H.
Defined.

Definition all_el (S: Set) (P: S->Prop) (u: (∀ x: S. P x)) (v: S) : P v.
unfold all in u.
pose proof u v.
exact H.
Defined.

Definition ex (S: Set) (P: S->Prop) := forall A: Prop,  (∀ x: S. (P x ⇒ A)) ⇒ A.

Declare Scope type_scope.
Notation "'∃' x . p" := (ex _ (fun x => p))
  (at level 200, x binder, right associativity,
   format "'[' '∃' '/ ' x . '/ ' p ']'").

Definition ex_in (S: Set) (P: S->Prop) (u: S) (v: P u): ∃ x : S . P x.
unfold ex.
intros.
unfold imp.
intros.
unfold all in H.
apply (H u).
apply v.
Defined.

Definition ex_el (S: Set) (P: S->Prop) (u: (∃ x : S . P x)) 
(A: Prop) (v : ∀x : S. (P x ⇒ A)): A.
unfold ex.
intros.
unfold ex in u.
pose proof u A.
apply H.
apply v.
Defined.

(* Figure 11.26 Example: ¬∃ implies ∀¬ *)
Definition not_ex_implies_all_not (S: Set) (P: S->Prop) 
(u: ¬∃x : S . P x) : ∀y : S . ¬(P y).
unfold all.
intro.
unfold neg.
unfold imp.
intro.
pose proof ex_in S P x H.
pose proof abs_in (∃ x. P x) H0 u.
apply H1.
Defined.

Definition ex_in_alt (S: Set) (P: S->Prop) (u : ¬∀x : S . ¬(P x)) : ∃x : S . P x.
assert(¬¬ ∃ y. P y).
refine (_: ¬ (∃ y. P y)-> ⊥ ).
intro v.
pose proof not_ex_implies_all_not S P v.
pose proof abs_in (∀ y. ¬ P y) H u.
apply H0.
pose proof DN_el (∃ y. P y) H.
apply H0.
Defined.

Definition ex_el_alt (S: Set) (P: S->Prop) (u : ∃x : S . P x) : ¬∀x : S . ¬(P x).
unfold neg.
unfold imp.
intro.
unfold all in H.
pose proof ex_el S P u ⊥.
unfold all in H0.
unfold imp in H0.
apply H0.
exact H.
Defined.

(* Chapter 11 Exercises *)

Module Exercise_11_1.
  (* a) [Taken from ERRATA https://www.win.tue.nl/~wsinrpn/CUP-C-Selected-exercises.pdf]
  Prove: ∅ ; x : ∧(⊥, ⊥) ⊢ x ⊥ : ¬(⊥ ⇒ ¬⊥)
  *)
  Definition Exercise_11_1_a (x : ⊥ ∧ ⊥):  ¬(⊥ ⇒ ¬⊥).
  unfold conj in x.
  pose proof x ⊥.
  unfold imp.
  unfold neg.
  unfold imp.
  apply H.
  Defined.

  Parameter  S: Set.
  Parameter  P: S -> Prop.
  Parameter  Q: S -> Prop.
  (* b) Give the δ-normal form of ∃(S, λx : S . (P x ∨ Qx)). *)
  Eval compute in (ex S (fun x : S => (P x ∨ Q x))).
End Exercise_11_1.

Definition Exercise_11_7 (A B: Prop): (A ∨ B) ⇒ (B ∨ A).
intros.
pose proof disj_el A B ((B ∨ A)).
pose proof imp_in (A ∨ B) (B ∨ A).
apply H0.
intro.
apply H.
apply H1.
pose proof imp_in (A) (B ∨ A) (fun (a:A) => (disj_in_2 B A a) ).
apply H2.
pose proof imp_in (B) (B ∨ A) (fun (b: B) => (disj_in_1 B A b) ).
apply H2.
Defined.

Definition Exercise_11_8 (A B: Prop):  (¬A ⇒ B) ⇒ (A ∨ B).
pose proof disj_in_alt_1.
exact (imp_in (¬ A ⇒ B) (A ∨ B) (H A B)).
Defined.

Definition Exercise_11_9_a (A:Prop):  ¬(A ∧ ¬A).
pose proof neg_in (A ∧ ¬ A).
apply H.
intro.
pose proof abs_in A.
apply H1.
exact (conj_el_1 A (¬ A) H0).
pose proof abs_el (A ⇒ ⊥).
apply H2.
apply H1.
exact (conj_el_1 (A) (¬ A) H0).
pose proof (conj_el_2 (A) (¬ A) H0).
pose proof neg_el A H3.
pose proof imp_in A ⊥ H4.
exact H5.

Definition Exercise_11_9_b (A B:Prop):  ¬(A ∨ B) ⇒ (¬A ∧ ¬B).
pose proof imp_in (¬ (A ∨ B)) ( (¬ A ∧ ¬ B)).
apply H.
intro.
pose proof conj_in (¬ A) (¬ B).
apply H1.
pose proof neg_in.
apply H2.
intro.
pose proof disj_in_1 (A) B H3.
pose proof abs_in (A ∨ B) H4 H0.
apply H5.
pose proof neg_in B.
apply H2.
intro.
pose proof disj_in_2 (A) B H3.
pose proof abs_in (A ∨ B) H4 H0.
apply H5.
Defined.

Definition Exercise_11_9_c (S: Set) (P: S->Prop):  (¬∃x:S. (¬P(x))) ⇒ ∀y:S. (P(y)).
pose proof imp_in (¬ (∃ x. ¬ P x)) (∀ y. P y).
apply H.
intro.
pose proof all_in S P.
apply H1.
intro.
pose proof DN_el (P x).
apply H2.
pose proof neg_in ((¬ P x)).
apply H3.
intro.
pose proof ex_in S (fun (x:S)=>¬ P x) x.
cbv beta in H5.
pose proof abs_in (∃ x. ¬ P x).
apply H6.
exact (H5 H4).
pose proof neg_el (∃ x. ¬ P x) H0.
pose proof imp_in ((∃ x. ¬ P x)) ⊥ H7.
exact H8.
Defined.

Definition tauto_7_1_b (A B: Prop): ¬A ⇒ (A ⇒ B).
apply (imp_in (¬ A) (A ⇒ B)).
intro.
apply (imp_in A B).
intro.
pose proof neg_el A H.
pose proof imp_in A ⊥ H1.
pose proof abs_in A H0 H2.
exact (abs_el B H3).
Defined.

Definition Exercise_11_10 (A B: Prop): ((A ⇒ B) ⇒ A) ⇒ A.
apply (imp_in ((A ⇒ B) ⇒ A) A).
intro.
pose proof exc_thrd A.
pose proof tauto_7_1_b A B.
pose proof disj_el A (¬ A) A H0.
apply H2.
apply (imp_in A A (fun a:A => a)).
apply (imp_in (¬ A) A).
intro.
pose proof imp_el ((A ⇒ B)) (A) H.
apply H4.
pose proof imp_el (¬ A) (A ⇒ B) H1.
apply H5.
apply H3.
Defined.

Definition tauto_7_1_a (A B: Prop): B ⇒ (A ⇒ B).
apply (imp_in B (A ⇒ B)).
intro.
apply (imp_in A (B)).
intro.
apply H.
Defined.

Definition Exercise_11_11_a (A B: Prop): (A ⇒ B) ∨ A.
pose proof disj_in_alt_2 (A ⇒ B) A.
apply H.
apply tauto_7_1_b.
Defined.

Definition Exercise_11_11_b (A B: Prop): (A ⇒ B) ∨ ¬B.
pose proof disj_in_alt_2 (A ⇒ B) (¬B).
apply H.
pose proof DN_el B.
apply (imp_in (¬ (¬ B)) (A ⇒ B)).
intro.
pose proof H0 H1.
pose proof imp_el B (A ⇒ B) (tauto_7_1_a A B) H2.
exact H3.
Defined.


Definition Exercise_11_12_a(A B: Prop): (A ⇔ B) ⇒ (¬A ⇔ ¬B).
apply (imp_in (A ⇔ B) (¬ A ⇔ ¬ B)).
intro.
pose proof biimpl_el_1 A B H.
pose proof biimpl_el_2 A B H.
apply (biimpl_in (¬ A) (¬ B)).
apply (imp_in (¬ A) (¬ B)).
intro.
apply (neg_in B).
intro.
pose proof imp_el B A H1 H3.
apply (abs_in A H4 H2).
apply (imp_in (¬ B) (¬ A)).
intro.
apply (neg_in A).
intro.
pose proof imp_el A B H0 H3.
apply (abs_in B H4 H2).
Defined.

Definition Exercise_11_12_b(A B: Prop): (A ⇔ B) ⇒ ((A ∧ B) ∨ (¬A ∧ ¬B)).
apply (imp_in ((A ⇔ B) ) (((A ∧ B) ∨ (¬ A ∧ ¬ B)))).
intro.
pose proof exc_thrd (A ∧ B).
apply (disj_el (A ∧ B) (¬ (A ∧ B)) ((A ∧ B) ∨ (¬ A ∧ ¬ B)) H0).
apply (imp_in ((A ∧ B)) ((A ∧ B) ∨ (¬ A ∧ ¬ B))).
intro.
apply (disj_in_1 (A ∧ B) (¬ A ∧ ¬ B) H1).
apply (imp_in (¬ (A ∧ B)) ((A ∧ B) ∨ (¬ A ∧ ¬ B))).
intro.
pose proof Exercise_11_12_a A B H.
apply (disj_in_2 (A ∧ B) (¬ A ∧ ¬ B)).
apply (conj_in (¬ A) (¬ B)).
apply (neg_in A).
intro.
pose proof biimpl_el_1 A B H.
pose proof imp_el A B H4 H3.
pose proof conj_in A B H3 H5.
apply (abs_in (A ∧ B) H6 H1).
apply (neg_in B).
intro.
pose proof biimpl_el_2 A B H.
pose proof imp_el B A H4 H3.
pose proof conj_in A B H5 H3.
apply (abs_in (A ∧ B) H6 H1).
Defined.

Definition Exercise_11_12_c(A B: Prop): ¬(A ∨ B) ⇔ (¬A ∧ ¬B).
apply (biimpl_in (¬ (A ∨ B)) (¬ A ∧ ¬ B)).
apply (imp_in (¬ (A ∨ B)) (¬ A ∧ ¬ B)).
intro.
apply (conj_in (¬ A) (¬ B)).
apply (neg_in A).
intro.
pose proof disj_in_1 A B H0.
apply (abs_in (A ∨ B) H1 H).
apply (neg_in B).
intro.
pose proof disj_in_2 A B H0.
apply (abs_in (A ∨ B) H1 H).
apply (imp_in ((¬ A ∧ ¬ B)) (¬ (A ∨ B))).
intro.
apply (neg_in (A ∨ B)).
intro.
pose proof conj_el_1 (¬ A) (¬ B) H.
pose proof conj_el_2 (¬ A) (¬ B) H.
pose proof disj_el A B ⊥ H0.
apply H3.
apply (imp_in A ⊥).
intro.
apply (abs_in A H4 H1).
apply (imp_in B ⊥).
intro.
apply (abs_in B H4 H2).
Defined.

Definition Exercise_11_13_a: 
(forall A: Prop, (A ∨ (¬ A))) ⇒ 
(forall B: Prop, ((¬(¬B))⇒B)).
pose proof (imp_in (forall A : Prop,
(A ∨ ¬ A)) ((forall B : Prop, ((¬(¬B))⇒B)))).
apply H.
intro.
intro.
apply (imp_in (¬ (¬ B)) B).
intro.
pose proof H0 (B).
pose proof disj_el (B) (¬ B) B H2.
apply H3.
exact (fun b:B => b).
apply (imp_in (¬ B) B).
intro.
pose proof abs_in (¬ B) H4 H1.
apply (abs_el B H5).
Defined.

Definition Exercise_11_13_b: 
(forall B: Prop, ((¬(¬B))⇒B)) ⇒ 
(forall A: Prop, (A ∨ (¬ A))).
pose proof (imp_in ((forall B : Prop, ¬ (¬ B) ⇒ B))
 ((forall A : Prop, A ∨ ¬ A))).
 intro.
intro.
pose proof H0 (A ∨ ¬ A).
pose proof (imp_el (¬ (¬ (A ∨ ¬ A))) ( (A ∨ ¬ A)) H1).
apply H2.
apply (neg_in (¬ (A ∨ ¬ A))).
intro.
pose proof abs_in (A ∨ ¬ A).
apply H4.
pose proof disj_in_2 (A) (¬ A).
apply H5.
apply (neg_in A).
intro.
pose proof disj_in_1 A (¬ A) H6.
apply (abs_in (A ∨ ¬ A) H7 H3).
apply (imp_in (A ∨ ¬ A) ⊥).
intro.
apply (abs_in (A ∨ ¬ A) H5 H3).
Defined.

Definition Exercise_11_14 (S T: Set) (R: S->T->Prop): 
(¬∃x:S. ∃y:T. ((R x y))) ⇒ ∀x:S. ∀y:T. (¬(R x y)).
apply (imp_in (¬ (∃ x. ∃ y. R x y)) (∀ x. ∀ y. ¬ R x y)).
intro.
pose proof all_in S (fun x:S => (∀ y:T. ¬(R x y))).
apply H0.
intro.
pose proof all_in T.
pose proof all_in T (fun y:T => (¬ R x y)).
apply H1.
refine (_:(forall y : T, ¬ R x y)).
intro.
apply (neg_in (R x y) ).
intro.
pose proof ex_in T  (fun y: T=> R x y) y H3.
cbv beta in H4.
pose proof H4: (∃ y. R x y).
pose proof ex_in S  (fun x: S=> ∃ y. R x y) x H5.
cbv beta in H6.
apply (abs_in (∃ x. ∃ y. R x y) H6 H).
Defined.

Definition Exercise_11_15_A (S: Set) (P: S->Prop): (∃x:S. (¬(P x))) ⇒(¬∀x:S. (P(x))).
apply (imp_in (∃ x. ¬ P x) (¬ (∀ x0. P x0))).
intro.
pose proof ex_el_alt S (fun x:S => ¬ ((P x))) H.
cbv beta in H0.
apply (neg_in (∀ x0. P x0)).
intro.
pose proof H1: (∀ x. P x) as H1.
pose proof abs_in (∀ x. ¬ (¬ P x)).
apply H2.
apply (all_in S (fun x:S => ¬ (¬ P x))).
intro.
pose proof all_el S P H1 x.
pose proof DN_in (P x) H3.
apply H4.
apply (imp_in (∀ x. ¬ (¬ P x)) ⊥).
intro.
apply (abs_in (∀ x. ¬ (¬ P x)) H3 H0).
Defined.

Definition Exercise_11_15_B (S: Set) (P: S->Prop): 
(∀x: S. (¬P(x))) ⇒¬∃x: S. (P(x)).
apply (imp_in ((∀ x. ¬ P x)) (¬ (∃ x. P x))).
intro.
apply (neg_in (∃ x. P x)).
intro.
pose proof ex_el_alt S P H0.
apply (abs_in (∀ x. ¬ P x) H H1).
Defined.

Definition Exercise_11_16 (S: Set) (P: S->Prop): 
(∀x:S. (P(x))) ⇔ ¬∃x:S. (¬P(x)).
apply (biimpl_in ((∀ x. P x)) (¬ (∃ x. ¬ P x))).
apply (imp_in ((∀ x. P x)) (¬ (∃ x. ¬ P x))).
intro.
apply (neg_in (∃ x. ¬ P x)).
intro.
pose proof ex_el_alt S (fun x:S => ¬ P x).
cbv beta in H1.
pose proof H1 H0.
apply (abs_in (∀ x. ¬ (¬ P x))).
apply (all_in S (fun x:S =>  ¬ (¬ P x))).
intro.
pose proof all_el S P H x.
apply (DN_in (P x) H3).
apply (imp_in (∀ x. ¬ (¬ P x)) ⊥).
intro.
apply (abs_in (∀ x. ¬ (¬ P x)) H3 H2).
apply (imp_in (¬ (∃ x. ¬ P x)) ((∀ x. P x))).
intro.
apply (all_in S P).
intro.
apply (DN_el (P x)).
apply (neg_in (¬ P x)).
intro.
pose proof ex_in S (fun x: S=> ¬ P x) x H0.
cbv beta in H1.
apply (abs_in (∃ x. ¬ P x) H1 H).
Defined.

Definition Exercise_11_17 (S: Set) (P: S->Prop): 
∀x:S. ((¬∃y:S. (P(y))) ⇒ ∃z:S. (¬P(z))).
intro.
apply (imp_in (¬ (∃ y. P y)) (∃ z. ¬ P z)).
intro.
pose proof ex_in_alt S (fun z:S =>¬ P z).
cbv beta in H0.
apply (ex_in S (fun z:S =>¬ P z) x).
apply (neg_in (P x)).
intro.
pose proof ex_in S P x H1.
apply(abs_in (∃ x. P x) H2 H).
Defined.

Definition Exercise_11_18_a (S: Set) (P Q: S->Prop):  
(∃x:S. (P(x) ∨ Q(x))) ⇒ ((∃x:S. (P(x))) ∨ (∃x:S. (Q(x)))).
apply (imp_in (∃ x. P x ∨ Q x)  ((∃ x. P x) ∨ (∃ x. Q x))).
intro.
pose proof ex_el S (fun x:S => P x ∨ Q x) H ((∃ x. P x) ∨ (∃ x. Q x)).
cbv beta in H0.
apply H0.
refine (_: ∀ x. (P x ∨ Q x) ⇒ ((∃ y. P y) ∨ (∃ y. Q y))).
apply (all_in S (fun x:S => (P x ∨ Q x) ⇒ ((∃ y. P y) ∨ (∃ y. Q y)))).
intro.
apply (imp_in ((P x ∨ Q x)) ((∃ y. P y) ∨ (∃ y. Q y))).
intro.
pose proof disj_el (P x) (Q x) ((∃ y. P y) ∨ (∃ y. Q y)) H1.
apply H2.
apply (imp_in (P x) ((∃ y. P y) ∨ (∃ y. Q y))).
intro.
pose proof ex_in S P x H3.
pose proof disj_in_1 (∃ y. P y) (∃ y. Q y) H4.
apply H5.
apply (imp_in (Q x) (((∃ y. P y) ∨ (∃ y. Q y)))).
intro.
pose proof ex_in S Q x H3.
pose proof disj_in_2 (∃ y. P y) (∃ y. Q y) H4.
apply H5.
Defined.


Definition Exercise_11_18_b (S T: Set) (R: S->T->Prop):  
(∃x:S. ∀y:T. ((R x y))) ⇒ ∀y:T. ∃x:S. ((R x y)).
apply (imp_in (∃ x. ∀ y. R x y) (∀ y. ∃ x. R x y)).
intro.
apply (all_in T (fun y:T => ∃ x. R x y)).
refine (_: forall y : T, ∃ x. R x y).
intro.
pose proof ex_el S (fun x:S => ∀ y. R x y) H (∃ x. R x y).
cbv beta in H0.
apply H0.
refine (_: ∀ x. (∀ y. R x y) ⇒ (∃ x. R x y)).
apply (all_in S (fun x:S => (∀ y. R x y) ⇒ (∃ x. R x y))).
intro.
apply (imp_in (∀ y0. R x y0) (∃ x0. R x0 y)).
intro.
pose proof all_el T (fun y:T => R x y) H1 y.
cbv beta in H2.
apply (ex_in S (fun x:S => R x y) x H2).
Defined.
