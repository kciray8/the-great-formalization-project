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

Definition all (P: Set->Prop) := forall x: Set, P x.

Declare Scope type_scope.
Notation "'∀' x . p" := (all (fun x => p))
  (at level 200, x binder).

Definition all_in (P: Set->Prop) (u: forall x: Set, P x) : ∀ x. P x.
unfold all.
intro.
pose proof u x.
exact H.
Defined.

Definition all_el (P: Set->Prop) (u: (∀ x. P x)) (v: Set) : P v.
unfold all in u.
pose proof u v.
exact H.
Defined.

Definition ex (P: Set->Prop) := forall A: Prop,  (∀ x. (P x ⇒ A)) ⇒ A.

Declare Scope type_scope.

Notation "'∃' x . p" := (ex (fun x => p))
  (at level 200, x binder, right associativity).

Definition ex_in (P: Set->Prop) (u: Set) (v: P u): ∃ x . P x.
unfold ex.
intros.
unfold imp.
intros.
unfold all in H.
apply (H u).
apply v.
Defined.

Definition ex_el (P: Set->Prop) (u: (∃ x . P x)) 
(A: Prop) (v : ∀x. (P x ⇒ A)): A.
unfold ex.
intros.
unfold ex in u.
pose proof u A.
apply H.
apply v.
Defined.

(* Figure 11.26 Example: ¬∃ implies ∀¬ *)
Definition not_ex_implies_all_not (P: Set->Prop) 
(u: ¬∃x . P x) : ∀y . ¬(P y).
unfold all.
intro.
unfold neg.
unfold imp.
intro.
pose proof ex_in P x H.
pose proof abs_in (∃ x. P x) H0 u.
apply H1.
Defined.

Definition ex_in_alt (P: Set->Prop) (u : ¬∀x . ¬(P x)) : ∃x . P x.
assert(¬¬ ∃ y. P y).
refine (_: ¬ (∃ y. P y)-> ⊥ ).
intro v.
pose proof not_ex_implies_all_not P v.
pose proof abs_in (∀ y. ¬ P y) H u.
apply H0.
pose proof DN_el (∃ y. P y) H.
apply H0.
Defined.

Definition ex_el_alt (P: Set->Prop) (u : ∃x . P x) : ¬∀x . ¬(P x).
unfold neg.
unfold imp.
intro.
unfold all in H.
pose proof ex_el P u ⊥.
unfold all in H0.
unfold imp in H0.
apply H0.
exact H.
Defined.

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
Defined.

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

Definition Exercise_11_9_c (P: Set->Prop):  (¬∃x. (¬P(x))) ⇒ ∀y. (P(y)).
pose proof imp_in (¬ (∃ x. ¬ P x)) (∀ y. P y).
apply H.
intro.
pose proof all_in P.
apply H1.
intro.
pose proof DN_el (P x).
apply H2.
pose proof neg_in ((¬ P x)).
apply H3.
intro.
pose proof ex_in (fun x=>¬ P x) x.
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

Definition eq (x y: Set) : Prop := forall P: (Set -> Prop), (P x ⇔ P y).
Notation "A = B" := (eq A B)(at level 51, right associativity).

Definition eq_refl (x: Set) : x = x.
intro.
unfold biimpl.
assert (P x ⇒ P x).
intro.
exact H.
exact (biimpl_in _ _ H H).
Defined.

Definition eq_subs (P: (Set -> Prop)) (x y: Set) (u: x = y) (v: P x) : P y.
pose proof u P.
pose proof biimpl_el_1 _ _ H.
apply H0.
exact v.
Defined.

Definition eq_cong (f: (Set -> Set)) (x y: Set) (u: x = y) : (f x) = (f y).
pose proof eq_subs (fun z: Set=> f x = f z) x y.
cbv beta in H.
apply H.
exact u.
exact (eq_refl (f x)).
Defined.

Definition refl (R: Set-> Set-> Prop) : Prop := ∀x . (R x x).

Definition trans (R: Set-> Set-> Prop) : Prop := 
∀x . ∀y . ∀z : Set. ((R x y) ⇒ (R y z) ⇒ (R x z)).

Definition pre_ord (R: Set-> Set-> Prop) := (refl R) ∧ (trans R).

Definition symm (R: Set-> Set-> Prop) :=
 ∀x . ∀y . ((R x y) ⇒ (R y x)).

Definition antisymm (R: Set-> Set-> Prop) :=
 ∀x . ∀y . ((R x y) ⇒ (R y x) ⇒ (x = y)).

Definition part_ord (R: Set-> Set-> Prop) := (pre_ord R) ∧ (antisymm R).


Definition eq_symm : ∀x . ∀y . ((x = y) ⇒ (y = x)).
intro.
intro y.
intro.
intro.
pose proof H P.
pose proof biimpl_el_1 _ _ H0.
pose proof biimpl_el_2 _ _ H0.
pose proof biimpl_in _ _ H2 H1.
exact H3.
Defined.
 

Definition eq_trans 
: ∀x . ∀y . ∀z : Set. ((x = y) ⇒ (y = z) ⇒ (x = z)).
intro x.
intro y.
intro z.
intro.
intro.
pose proof eq_subs (fun w => x = w) y z.
cbv beta in H1.
apply H1.
exact H0.
exact H.
Defined.

Definition Least (R: Set-> Set-> Prop) (m : Set) := ∀n : Set. (R m n).
  
Definition ex_more (P: Set-> Prop) := ex P.

Notation "'∃≥1' x . p" := (ex_more (fun x => p))
  (at level 200, x binder, right associativity,
   format "'[' '∃≥1' '/ ' x . '/ ' p ']'").

Definition ex_less (P: Set-> Prop) := 
∀y. ∀z: Set. (P y ⇒ P z ⇒ (y = z)).

Notation "'∃≤1' x . p" := (ex_less (fun x => p))
  (at level 200, x binder, right associativity,
   format "'[' '∃≤1' '/ ' x . '/ ' p ']'").

Definition ex_unique (P: Set-> Prop) := (∃≥1 x. P x) ∧ (∃≤1 x. P x).

Notation "'∃1' x . p" := (ex_unique (fun x => p))
  (at level 200, x binder, right associativity,
   format "'[' '∃1' '/ ' x . '/ ' p ']'").

(* 
Definition 12.1.1 Let Setbe a set and ≤ a binary relation on S.
Then m ∈ Setis a least element of Setwith respect to ≤ if ∀n∈S(m ≤ n).

Lemma 12.1.2 Let Setbe a set, partially ordered by ≤. Assume that
S has a least element with respect to ≤. Then this least element is
unique.
*)

Definition lemma_12_1_2 (R: Set-> Set-> Prop) 
(u: part_ord R) : (∃ l. Least R l) -> (∃1 l. Least R l).
intro.
unfold ex_unique.
unfold ex_more.
refine (conj_in _ _ H _).
unfold ex_less.
intro x.
intro y.
intro.
intro.
unfold Least in H0.
unfold Least in H1.
pose proof H0 y.
pose proof H1 x.
cbv beta in H2, H3.
unfold part_ord in u.
pose proof conj_el_2 _ _ u.
unfold antisymm  in H4.
pose proof H4 x y.
cbv beta in H5.
apply H5.
exact H2.
exact H3.
Defined.

Axiom ι: forall (P: Set-> Prop) (u: (∃1 x. P x)), Set.

Axiom ι_prop: forall (P: Set-> Prop) (u: (∃1 x. P x)), P ((ι P u)).

Axiom ε: forall (P: Set-> Prop) (u: (∃ x. P x)), Set.

Axiom ε_prop: forall (P: Set-> Prop) (u: (∃ x. P x)), P ((ε P u)).

(* Lemma 12.7.1 Let Setbe a set, P a predicate on Setand assume
∃1x∈S(P(x)). Then ∀z∈S(P(z) ⇒ (z =S ιx∈S(P(x)))). *)

Definition lemma_12_7_1 (P: Set-> Prop) (u: ∃1x. (P(x))): 
∀z. (P(z) ⇒ ((z = (ι P u)))).
intro.
intro.
unfold ex_unique in u.
pose proof conj_el_2 _ _ u.
unfold ex_less in H0.
pose proof H0 x (ι P u).
cbv beta in H1.
apply H1.
exact H.
pose proof ι_prop P u.
exact H2.
Defined.

Definition Min (R: Set-> Set-> Prop) (r: part_ord R) 
(w : ∃≥1 x. (Least R x)): Set.
pose proof lemma_12_1_2 R r w.
pose proof ι (fun l => Least R l) H.
exact X.
Defined.

Definition Min_Prop (R: Set-> Set-> Prop) 
(r: part_ord R) (w : ∃≥1 x. (Least R x))
: (∀x . ((Least R x)) ⇒ (x = (Min R r w))).
intro.
intro.
unfold Min.
cbv beta.
unfold part_ord in r.
pose proof lemma_12_7_1 ((fun l : Set=> Least R l)).
cbv beta in H0.
pose proof H0 (lemma_12_1_2 R r w) x.
cbv beta in H1.
apply H1.
exact H.
Defined.

Definition biimpl_symm (A B: Prop): (A ⇔ B) ⇒ (B ⇔ A).
intro.
unfold biimpl.
unfold biimpl in H.
pose proof conj_el_1 _ _ H.
pose proof conj_el_2 _ _ H.
exact (conj_in _ _ H1 H0).
Defined.

Definition biimpl_trans (A B C: Prop): (A ⇔ B) ⇒ (B ⇔ C) ⇒ (A ⇔ C).
intro.
intro.
apply (conj_in _ _).
intro.
pose proof conj_el_1 _ _ H.
pose proof conj_el_1 _ _ H0.
apply (H3 (H2 H1)).
pose proof conj_el_2 _ _ H.
pose proof conj_el_2 _ _ H0.
intro.
apply (H1 (H2 H3)).
Defined.

Definition exercise_12_1 : ∀x . ∀y . ((x = y) ⇒ (y = x)).
intro x.
intro y.
intro.
intro.
pose proof H P.
exact (biimpl_symm _ _ H0).
Defined.

Definition eq_alt (x y: Set) : Prop := forall P: (Set -> Prop), (P x -> P y).

Definition subs_prop (R: Set-> Set-> Prop) : Prop 
:= forall (P: Set-> Prop) (x y: Set) (u: R x y) (v: P x), P y.

Definition eq_statisfies_subs_prop: forall S: Set, subs_prop (eq).
intro.
intro.
exact (eq_subs P).
Defined.

Definition exercise_12_2_a : refl (eq_alt).
intro.
intro.
intro.
exact H.
Defined.

Definition exercise_12_2_b : symm (eq_alt).
intro x.
intro y.
intro.
pose proof H (fun z => eq_alt z x).
cbv beta in H0.
apply H0.
pose proof exercise_12_2_a.
unfold refl in H1.
exact (H1 x).
Defined.

Definition exercise_12_2_c : trans (eq_alt).
intro x.
intro y.
intro z.
intro.
intro.
pose proof H0 (fun k => eq_alt x k).
cbv beta in H1.
apply H1.
exact H.
Defined.

Definition exercise_12_2_d:  forall S: Set, subs_prop (eq_alt).
intro.
intro.
intro x.
intro y.
intro.
pose proof u P.
exact H.
Defined.

Ltac left x := pose proof conj_el_1 _ _ x.
Ltac right x := pose proof conj_el_2 _ _ x.

Ltac conj_el x:= left x; right x.

(* 12.3 
(a) Check that line (3) of Figure 12.10 and line (2) of Figure 12.12 satisfy
the derivation rules of λD. --> Proved in eq_symm and eq_trans
(b) The same question for lines (1) and (2) of Figure 12.18.
--> Proved in Min and Min_Prop
 *)

Module exercise_12_4.
Parameter S: Set.
Parameter le: Set-> Set-> Prop.
Parameter ordered: part_ord le.
Notation "A ≤ B" := (le A B)(at level 52, left associativity).

(* 12.4 (a) *)
Definition lt (m n: Set):= (m ≤ n) ∧ (¬(m = n)).
Notation "A < B" := (lt A B)(at level 52, left associativity).

Definition exercise_12_4_b: ∀m. (¬(m<m)).
intro.
intro.
unfold lt in H.
conj_el H.
pose proof ordered.
unfold part_ord in H2.
right H2.
pose proof H3 x x H0 H0.
apply (H1 H4).
Defined.

Definition exercise_12_4_c: ∀m. ∀n. (¬((m < n) ∧ (n < m))).
pose proof ordered.
unfold part_ord in H.
right H.
unfold antisymm  in H0.
intro x.
intro y.
intro.
conj_el H1.
conj_el H2.
conj_el H3.
pose proof H0 x y H4 H6.
exact (H5 H8).
Defined.

Definition exercise_12_4_d: trans lt.
unfold trans.
intro x.
intro y.
intro z.
intro.
intro.
conj_el H.
conj_el H0.
unfold lt.
eapply (conj_in _ _ _).
intro.
pose proof eq_subs (fun k => k ≤ y) x z H5 H1.
cbv beta in H6.
apply H4.
pose proof ordered.
unfold part_ord in H7.
right H7.
unfold antisymm in H8.
pose proof H8 y z H3 H6.
exact H9.
Unshelve.
pose proof ordered.
unfold part_ord in H5.
left H5.
unfold pre_ord in H6.
right H6.
pose proof H7 x y z H1 H3.
exact H8.
Defined.

Definition exercise_12_5_a (P: Set-> Prop) 
(n: Set) (u: (P n)) (v: (∀x. (P(x) ⇒ (x = n))))
: ∃1 x. (P(x)).
unfold ex_unique.
pose proof (ex_in P n u):∃≥1 x. P x.
refine (conj_in _ _ H _).
unfold ex_less.
intro y.
intro z.
intro.
intro.
pose proof v y H0.
pose proof v z H1.
pose proof eq_symm z n H3.
exact (eq_trans y n z H2 H4).
Defined.

Definition exercise_12_5_b (P: Set-> Prop) (n: Set) 
(u: (P n)) (v: (∀x. (P(x) ⇒ (x = n)))) (w: ∃1 x. (P(x)))
: n = (ι P w).
pose proof lemma_12_7_1 P w n.
cbv beta in H.
apply H.
exact u.
Defined.

End exercise_12_4.

Module exercise_12_6.
Parameter S: Set.
Parameter le: Set-> Set-> Prop.
Parameter ordered: part_ord le.

Definition minimal (m:Set) := ∀x. ((le x m) ⇒ x = m).

Definition exercise_12_6_b (m: Set): (Least le m) -> minimal m.
intro.
intro x.
intro.
unfold Least in H.
pose proof H x.
cbv in H1.
pose proof ordered.
right H2.
pose proof H3 x m H0 H1.
exact H4.
Defined.

Definition exercise_12_6_c (m: Set): (Least le m) -> (forall k: Set, (minimal k) -> m = k).
intro.
intro.
intro.
pose proof H0 m.
cbv beta in H1.
apply H1.
unfold Least in H.
apply (H k).
Defined.

Definition exercise_12_6_c' (m: Set): (Least le m) -> 
forall (w: ∃1 x. minimal x), (m = (ι (fun g => minimal g) w)).
intro.
intro.
pose proof exercise_12_4.exercise_12_5_b (fun g : Set=> minimal g) m (exercise_12_6_b m H).
cbv beta in H0.
apply H0.
clear H0.
intro.
right w.
unfold ex_less in H0.
pose proof H0 x m.
cbv beta in H1.
pose proof exercise_12_6_b m H.
intro.
exact (H1 H3 H2).
Defined.

End exercise_12_6.

Definition associative_closed (R: Set-> Set-> Set) :=
 ∀x . ∀y . ∀z : Set. ((R (R x y) z) = (R x (R y z))).

Definition monoid (op: Set-> Set-> Set) := associative_closed op.

Definition has_unit (op: Set-> Set-> Set) := ∃e. ∀x. (op e x) = x ∧ (op x e) = x.

Definition unit (op: Set-> Set-> Set) (e: Set) := ∀x. ((op e x) = x ∧ (op x e) = x).

Definition exercise_12_7_b (op: Set-> Set-> Set) (M: monoid op):
(∃e. (unit op e)) ⇒ (∃1 e. (unit op e)).
unfold monoid in M.
unfold associative_closed  in M.
intro.
refine (conj_in _ _ H _).
intro x.
intro y.
intro unitx.
intro unity.
unfold unit in unitx.
unfold unit in unity.
pose proof unitx x.
cbv beta in H0.
pose proof unity y.
cbv beta in H1.
pose proof unitx y.
cbv beta in H2.
pose proof unity x.
cbv beta in H3.
left H3.
pose proof eq_symm (op y x) x H4.
right H2.
pose proof eq_trans x (op y x) y H5 H6.
exact H7.
Defined.

Definition inverse (op: Set-> Set-> Set) (x: Set) (y: Set) (e: Set):= 
((op x y)) = e ∧ ((op y x) = e). (* exercise_12_7_d *)

Definition exercise_12_7_c (op: Set-> Set-> Set) (M: monoid op) 
(e: Set) (e_is_unit: unit op e):
(∀x. ∃y. (inverse op x y e)) -> (∀x. ∃1 y. (inverse op x y e)).
intro each_x_has_inverse_y.
intro.
unfold ex_unique.
refine (conj_in _ _ (each_x_has_inverse_y x) _).
refine (_:∃≤1 y. inverse op x y e).
unfold ex_less.
intro y.
intro z.
intro y_inverse_for_x.
intro z_inverse_for_x.
unfold inverse in y_inverse_for_x.
unfold inverse in z_inverse_for_x.
unfold inverse in each_x_has_inverse_y.
unfold monoid in M.
unfold associative_closed in M.
unfold unit in e_is_unit.
pose proof e_is_unit y.
cbv beta in H.
right H.
pose proof eq_symm (op y e) y H0.
left z_inverse_for_x.
pose proof eq_symm (op x z) e H2.
pose proof eq_subs (fun e => y = op y e) e (op x z) H3 H1.
cbv beta in H4.
pose proof M y x z.
cbv beta in H5.
pose proof eq_symm (op (op y x) z) (op y (op x z)) H5.
pose proof eq_subs (fun R => y = R) (op y (op x z)) (op (op y x) z) H6 H4.
cbv beta in H7.
right y_inverse_for_x.
pose proof eq_subs (fun R => y = op (R) z) (op y x) (e) H8 H7.
cbv beta in H9.
pose proof e_is_unit z.
left H10.
pose proof eq_trans y (op e z) z H9 H11.
exact H12.
Defined.

Definition exercise_12_8 (R: Set-> Set-> Prop) 
(r: part_ord R) (w : ∃≥1 x. (Least R x))
: (∀x . (x = (Min R r w)) ⇒ ((Least R x))).
intro.
intro.
intro y.
unfold Min in H.
unfold Least in w.
unfold ex_more in w.
unfold ex in w.
pose proof w (R x y).
apply H0.
intro z.
intro.
pose proof H1 y.
cbv beta in H2.
pose proof H1: (Least R z).
pose proof lemma_12_7_1 (fun l : Set=> Least R l) (lemma_12_1_2 R r w) z.
cbv beta in H4.
pose proof H4 H3.
pose proof eq_symm _ _ H5.
pose proof eq_trans _ _ _ H H6.
pose proof eq_symm _ _ H7.
pose proof eq_subs (fun q => R q y) z x H8 H2.
exact H9.
Defined.

