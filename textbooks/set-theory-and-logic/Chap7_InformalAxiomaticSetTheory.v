Require Import Ltac.
From BASE Require Import MathLogic.

Parameter In: Set -> Set -> Prop.
Notation "a ∈ b" := (In a b)(at level 81, left associativity).
Notation "a ∉ b" := (¬(a ∈ b))(at level 81, left associativity).

Notation "∀ x :: S . p" := (all (fun x => ((x ∈ S) -> p)))
  (at level 200, x binder, format "∀ x :: S .  p").

Notation "∃ x :: S . p" := (ex (fun x => ((x ∈ S) ∧ p)))
  (at level 200, x binder, right associativity, format "∃ x :: S .  p").

(* not working! *)
Definition biimpl_el_left {A: Prop} {s: Set} {x: Set} 
(H: (∀z . (z ∈ s) ⇔ A)) (u: x ∈ s)  : A.
pose proof H x.
left H0.
pose proof H1 u.
apply H2.
Defined.

Axiom ZF1_extension: ∀ a. ∀ b. (∀ x. x ∈ a ⇔ x ∈ b) -> a = b.

Definition extension_backwards {a b: Set}: (a = b) -> (∀ x. x ∈ a ⇔ x ∈ b).
intros H.
intro x.
apply conj_in.
intro.
repl H H0.
apply H1.
intro.
repl H H0.
apply H1.
Defined.

Axiom ZF2_subsets: forall A: (Set -> Prop), ∀ a: Set. 
∃b. ∀ x. ((x ∈ b) ⇔ ((x ∈ a) ∧ (A x))).

Definition unique_subset_exists: forall A: (Set -> Prop), ∀ a. 
∃1b. ∀ x. ((x ∈ b) ⇔ ((x ∈ a) ∧ (A x))).
intro A.
intro a.
pose proof ZF2_subsets A a.
apply (conj_in _ _ H).
intro k.
intro m.
intro.
intro.
pose proof ZF1_extension k m.
cbv beta in H2.
apply H2.
intro x.
apply (conj_in _ _).
intro.
pose proof H0 x.
left H4.
pose proof H1 x.
right H6.
apply H7.
apply H5.
apply H3.
intro.
pose proof H0 x.
right H4.
apply H5.
left (H1 x).
apply H6.
apply H3.
Defined.

Ltac iota_in H := pose proof ι _ H.

Ltac destruct_ex H c := apply (H _); intro c; intro.

Definition unique_subset (A: (Set -> Prop)) (a: Set): Set 
:= ι _ (unique_subset_exists A a).

Notation "{ x 'ε' a | A }" := (unique_subset (fun x => A) a).

(* Deprecated *)
Definition unique_subset_exists_eq (A: (Set -> Prop)) (a: Set): 
∃s. s = unique_subset A a.
pose proof unique_subset_exists A a.
cbv beta in H.
left H.
cbv beta in H0.
destruct_ex H0 s.
apply (ex_in _ s).
unfold unique_subset.
apply(lemma_12_7_1 _).
apply H1.
Defined.

Definition subset(a b: Set) := ∀ x. (x ∈ a) -> (x ∈ b).

Notation "a ⊆ b" := (subset a b)(at level 81, left associativity).

Notation "a ⊈ b" := (¬(subset a b))(at level 81, left associativity).

Module RusselParadox.

Axiom unrestricted_comperension: forall A: (Set -> Prop), 
∃b. ∀ x. ((x ∈ b) ⇔ (A x)).

Definition russelsParadox: ⊥.
pose proof unrestricted_comperension (fun x => ¬(x ∈ x)).
destruct_ex H b.
pose proof H0 b.
cbv beta in H1.
pose proof biimpl_el_1 _ _ H1.
pose proof biimpl_el_2 _ _ H1.
pose proof exc_thrd (b ∈ b).
pose proof disj_el (b ∈ b) (¬ (b ∈ b)) ⊥ H4.
apply H5.
intro.
pose proof H2 H6.
apply (H7 H6).
intro.
pose proof H3 H6.
apply (H6 H7).
Defined.

Definition thereIsASetContaningItself: ∃s. s ∈ s.
pose proof unrestricted_comperension (fun x => (x = x)).
destruct_ex H s.
apply (ex_in _ s).
pose proof H0 s.
right H1.
pose proof H2 (eq_refl s).
apply H3.
Defined.

End RusselParadox.

Definition nothingContainsEverything: ¬(∃a. ∀ b. b ∈ a).
intro.
destruct_ex H a.
pose proof ZF2_subsets (fun x => ¬(x ∈ x)) a.
cbv beta in H1.
destruct_ex H1 b.
pose proof H0 b.
cbv beta in H3.
pose proof H2 b.
cbv beta in H4.
pose proof exc_thrd (b ∈ b) ⊥.
apply H5.
intro.
left H4.
pose proof H7 H6.
right H8.
apply (H9 H6).
intro.
right H4.
pose proof conj_in _ _ H3 H6.
pose proof H7 H8.
apply (H6 H9).
Defined.

Axiom ZF3_pairing: ∀ a. ∀b. ∃c. (a ∈ c) ∧ (b ∈ c).

Definition ZF3_pairing_equiv: ∀ a. ∀b. ∃c.  
∀ x. (x ∈ c) ⇔ ((x = a) ∨ (x = b)).
intro a.
intro b.
pose proof ZF3_pairing a b.
cbv beta in H.
pose proof ZF2_subsets (fun x =>((x = a) ∨ (x = b))).
destruct_ex H c.
clear H.
pose proof H0 c.
cbv beta in H.
destruct_ex H s.
apply(ex_in (fun c0 => ∀ x . x ∈ c0 ⇔ (x = a ∨ x = b)) s).
intro x.
apply (conj_in _ _).
intro.
pose proof H2 x.
cbv beta in H4.
left H4.
pose proof H5 H3.
right H6.
apply H7.
intro.
apply (disj_el (x = a) (x = b) (x ∈ s) H3).
intro.
pose proof H2 x.
right H5.
apply H6.
left H1.
pose proof eq_symm x a H4.
pose proof eq_subs (fun a => a ∈ c) a x H8 H7.
apply (conj_in _ _ H9 H3).
intro.
pose proof H2 x.
right H5.
apply H6.
right H1.
pose proof eq_symm x b H4.
pose proof eq_subs (fun a => a ∈ c) b x H8 H7.
apply (conj_in _ _ H9 H3).
Defined.

Definition any_biimpl_set_is_no_more_than_one (A: (Set -> Prop))
: ∃≤1 s. ∀ x. ((x ∈ s) ⇔ A x).
intros s1 s2.
intro.
intro.
pose proof ZF1_extension s1 s2.
apply H1.
intro x.
pose proof H x.
pose proof H0 x.
pose proof biimpl_symm _ _ H3.
pose proof biimpl_trans _ _ _ H2 H4.
apply H5.
Defined.

Definition pair_unord_exists (a b: Set): ∃1p. ∀ x. ((x ∈ p) ⇔ ((x = a) ∨ (x = b))).
unfold ex_unique.
apply (conj_in _ _).
pose proof ZF3_pairing_equiv a b.
cbv beta in H.
apply H.
intro x1.
intro x2.
intro.
intro.
apply (ZF1_extension x1 x2).
intro.
pose proof H x.
pose proof H0 x.
cbv beta in H1.
cbv beta in H2.
pose proof biimpl_symm _ _ H2.
pose proof biimpl_trans _ _ _ H1 H3.
apply H4.
Defined.

Definition pair_unord (a b: Set): Set := ι _ (pair_unord_exists a b).

Notation "{ a , b }" := (pair_unord a b).

Definition unit_set_exists (a: Set): ∃1p. ∀ x. ((x ∈ p) ⇔ ((x = a))).
pose proof pair_unord_exists a a.
apply (conj_in _ _).
left H.
destruct_ex H0 p.
apply (ex_in _ p).
intro x.
apply (conj_in _ _).
intro.
pose proof H1 x.
left H3.
pose proof H4 H2.
apply (disj_el _ _ (x = a) H5).
intro.
apply H6.
intro.
apply H6.
intro.
pose proof H1 x.
right H3.
apply H4.
apply (disj_in_1 _ _ H2).
apply (any_biimpl_set_is_no_more_than_one _).
Defined.

Definition unit_set (a: Set): Set := (ι _ (unit_set_exists a)).

(* '`' is used to prevent collision with coq { } *)
Notation "{` a }" := (unit_set a).


Definition every_set_is_in_unit_set: ∀m. m ∈ {`m}.
intro.
extract_iota_from_goal {`x}.
pose proof iota_prop x.
right H.
apply H0.
apply (eq_refl x).
Defined.

Definition everySetIsElementOfSomeSet: ∀ a . ∃b. a ∈ b.
intro.
pose proof pair_unord_exists x x.
left H.
cbv beta in H0.
pose proof (H0: ∃ b. ∀ x1 . x1 ∈ b ⇔ (x1 = x ∨ x1 = x)).
destruct_ex H1 b.
apply (ex_in _ b).
pose proof H2 x.
right H3.
apply H4.
pose proof eq_refl x.
apply (disj_in_1 _ _ H5).
Defined.

Axiom ZF4_union: ∀c. ∃a. ∀b. (b ∈ c) -> (∀x. (x ∈ b) -> x ∈ a).

Definition destruct_subset_def (A: (Set -> Prop)) (s a: Set)
(H1 : s = unique_subset A a): ∀ x. ((x ∈ s) ⇔ ((x ∈ a) ∧ (A x))).
unfold unique_subset in H1.
pose proof eq_symm _ _ H1.
pose proof ι_prop (fun b : Set => ∀ x . x ∈ b ⇔ (x ∈ a ∧ A x))
(unique_subset_exists A a).
cbv beta in H0.
pose proof eq_subs (fun g=> ∀ x. x∈ g ⇔ (x ∈ a ∧ A x)) (ι (fun b : Set => ∀ x . x ∈ b ⇔ (x ∈ a ∧ A x))
(unique_subset_exists A a)) s H H0.
cbv beta in H2.
apply H2.
Defined.

Ltac destruct_subset H := 
let x := fresh in
pose proof (destruct_subset_def _ _ _ H) as x; clear H; cbv beta in x.

Definition union_exists (c: Set): ∃1u. ∀ x. ((x ∈ u) ⇔ ((∃y. (x ∈ y) ∧ (y ∈ c)))).
apply (conj_in _ _).
refine ((_): (∃ u. ∀ x. ((x ∈ u) ⇔ ((∃y. (x ∈ y) ∧ (y ∈ c)))))).
pose proof ZF4_union c.
destruct_ex H a.
clear H.
pose proof unique_subset_exists_eq (fun x => (∃y. (x ∈ y) ∧ (y ∈ c))) a.
destruct_ex H s.
apply (ex_in _ s).
intro x.
apply (conj_in _ _).
intro.
unfold unique_subset in H1.
pose proof ι_prop _ (unique_subset_exists (fun x : Set => ∃ y . x ∈ y ∧ y ∈ c) a).
cbv beta in H3.
pose proof eq_symm _ _ H1.
pose proof eq_subs (fun g => ∀ x
. x ∈ g
⇔ (x ∈ a ∧ (∃ y . x ∈ y ∧ y ∈ c))) (ι (fun b : Set => ∀ x . x ∈ b ⇔ (x ∈ a ∧ (∃ y . x ∈ y ∧ y ∈ c)))
(unique_subset_exists (fun x : Set => ∃ y . x ∈ y ∧ y ∈ c) a)) s H4 H3.
cbv beta in H5.
pose proof H5 x.
cbv beta in H6.
left H6.
pose proof H7 H2.
right H8.
apply H9.
intro.
destruct_subset H1.
pose proof H3 x.
right H1.
apply H4.
refine (conj_in _ _ _ H2).
destruct_ex H2 b.
right H5.
left H5.
pose proof H0 b H6 x H7.
apply H8.
intros x1 x2.
intro.
intro.
apply (ZF1_extension x1 x2).
intro.
pose proof H x.
pose proof H0 x.
pose proof biimpl_symm _ _ H2.
pose proof biimpl_trans _ _ _ H1 H3.
apply H4.
Defined.

Definition union (c: Set): Set := ι _ (union_exists c).

Notation " ⋃ a " := (union a )(at level 81, left associativity).

Definition union2_exists (a b: Set): ∃1u. (∀ x. ((x ∈ u) ⇔ ((x ∈ a) ∨ (x ∈ b)))).
pose proof pair_unord_exists a b.
left H.
destruct_ex H0 p.
clear H H0.
pose proof union_exists p.
left H.
destruct_ex H0 u.
clear H H0.
apply (conj_in _ _).
apply (ex_in _ u).
intro x.
apply (conj_in _ _).
intro.
pose proof H2 x.
cbv beta in H0.
left H0.
pose proof H3 H.
destruct_ex H4 y.
right H5.
pose proof H1 y.
cbv beta in H7.
left H7.
pose proof H8 H6.
left H5.
apply (disj_el _ _ (x ∈ a ∨ x ∈ b) H9).
intro.
pose proof eq_subs _ y a H11 H10.
apply (disj_in_1 _ ( x ∈ b) H12).
intro.
pose proof eq_subs _ y b H11 H10.
apply (disj_in_2 (x ∈ a) (x ∈ b) H12).
intro.
pose proof H2 x.
right H0.
apply H3.
apply (disj_el _ _ _ H).
intro.
apply (ex_in _ a).
refine (conj_in _ _ H4 _).
pose proof H1 a.
right H5.
apply H6.
pose proof eq_refl a.
apply (disj_in_1 _ _ H7).
intro.
apply (ex_in _ b).
refine (conj_in _ _ H4 _).
pose proof H1 b.
right H5.
apply H6.
pose proof eq_refl b.
apply (disj_in_2 _ _ H7).
apply (any_biimpl_set_is_no_more_than_one _).
Defined.

Definition union2 (a b: Set) := ι _ (union2_exists a b).

Notation " a ∪ b " := (union2 a b)(at level 81, left associativity).

Axiom ZF6_infinity: ∃a. ((∃e.  (∀ x . ¬(x ∈ e)) ∧ (e ∈ a))
∧ (∀ x . (x ∈ a) -> (x ∪ (unit_set x)) ∈ a)).

Definition empty_set_unique: ∃1e.  (∀ x . ¬(x ∈ e)).
apply (conj_in _ _).
pose proof ZF6_infinity.
destruct_ex H a.
left H0.
destruct_ex H1 e.
left H2.
refine (ex_in _ e _).
apply H3.
intros a b.
intro.
intro.
refine (ZF1_extension a b _).
intro.
apply (conj_in _ _).
intro.
pose proof H x H1.
apply (abs_el (x ∈ b) H2).
intro.
pose proof H0 x H1.
apply (abs_el (x ∈ a) H2).
Defined.

Definition empty_set: Set := ι _ (empty_set_unique).
Notation " ∅ " := (empty_set).

Definition non_empty_set_has_element: ∀c. ¬(c = ∅) -> ∃a. a ∈ c.
intro c.
intro.
refine (ex_in_alt (fun a=> a ∈ c) _).
intro.
pose proof ZF1_extension c ∅.
cbv beta in H1.
apply H.
apply H1.
intro.
apply (conj_in _ _).
intro.
pose proof H0 x H2.
apply (abs_el (x ∈ ∅) H3).
intro.
pose proof empty_set_unique.
left H3.
destruct_ex H4 e.
pose proof lemma_12_7_1 (fun e => ∀ x . ¬ (x ∈ e)) empty_set_unique.
cbv beta in H6.
pose proof H6 e.
cbv beta in H7.
pose proof H7: ((∀ x . ¬ (x ∈ e)) ⇒ e = ∅).
pose proof H8 H5.
pose proof H5 x.
cbv beta in H10.
pose proof eq_symm _ _ H9.
pose proof eq_subs _ ∅ e H11 H2.
pose proof H10 H12.
apply (abs_el (x ∈ c) H13).
Defined.

Definition intersection_exists (c: Set) (not_empty: ¬(c = ∅)): 
∃1a. ∀ x. ((x ∈ a) ⇔ (∀y. (y ∈ c -> x ∈ y))).
pose proof non_empty_set_has_element c not_empty.
destruct_ex H a.
pose proof unique_subset_exists (fun x=>∀y. (y ∈ c -> x ∈ y)) a.
cbv beta in H1.
apply (conj_in _ _).
refine (_:∃ b. ∀ x . x ∈ b ⇔ (∀ y . y ∈ c -> x ∈ y)).
left H1.
cbv beta in H2.
pose proof (H2: ∃ b. ∀ x . x ∈ b ⇔ (x ∈ a ∧ (∀ y . y ∈ c -> x ∈ y))).
clear H1 H2.
destruct_ex H3 b.
apply (ex_in _ b).
intro x.
apply (conj_in _ _).
intro.
pose proof H1 x.
left H4.
pose proof H5 H2.
right H6.
apply H7.
intro.
pose proof H1 x.
cbv beta in H4.
right H4.
apply H5.
refine (conj_in _ _ _ H2).
pose proof H2 a.
apply H6.
apply H0.
apply (any_biimpl_set_is_no_more_than_one 
(fun x => ∀ y . y ∈ c -> x ∈ y)).
Defined.

Definition intersection (c: Set) (not_empty: ¬(c = ∅)): Set 
:= ι _ (intersection_exists c not_empty).

Definition intersection2_exists (a b: Set): 
∃1i. ∀ x. ((x ∈ i) ⇔ (x ∈ a ∧ x ∈ b)).
pose proof unique_subset_exists (fun x=>x ∈ b) a.
cbv beta in H.
apply H.
Defined.

Definition intersection2 (a b: Set): Set 
:= ι _ (intersection2_exists a b).

Notation " a ∩ b " := (intersection2 a b)(at level 81, left associativity).

Definition triple_unord_exists (a b c: Set): ∃1t. 
(∀ x. ((x ∈ t) ⇔ ((x = a) ∨ (x = b) ∨ (x = c)))).
pose proof unit_set_exists a as unit_a_ex.
left unit_a_ex.
destruct_ex H unit_a.
clear H.
rename H0 into unit_a_prop.
pose proof unit_set_exists b as unit_b_ex.
left unit_b_ex.
destruct_ex H unit_b.
clear H.
rename H0 into unit_b_prop.
pose proof unit_set_exists c as unit_c_ex.
left unit_c_ex.
destruct_ex H unit_c.
clear H.
rename H0 into unit_c_prop.
pose proof union2_exists unit_a unit_b as union_a_b_ex.
left union_a_b_ex.
destruct_ex H union_a_b.
clear H.
rename H0 into union_a_b_prop.
pose proof union2_exists union_a_b unit_c as union_a_b_c_ex.
left union_a_b_c_ex.
destruct_ex H union_a_b_c.
clear H.
rename H0 into union_a_b_c_prop.
apply (conj_in _ _).
apply (ex_in _ union_a_b_c).
intro.
apply (conj_in _ _).
intro.
pose proof union_a_b_c_prop x.
left H0.
pose proof H1 H.
apply (disj_el _ _ _ H2).
intro.
pose proof union_a_b_prop x.
left H4.
pose proof H5 H3.
apply (disj_el _ _ _ H6).
intro.
pose proof unit_a_prop x.
left H8.
pose proof H9 H7.
pose proof disj_in_1 _ (x = b) H10.
apply (disj_in_1 _ (x = c) H11).
intro.
pose proof  unit_b_prop x.
left H8.
pose proof H9 H7.
pose proof disj_in_2 (x = a) (x = b) H10.
apply (disj_in_1 _ (x = c) H11).
intro.
pose proof unit_c_prop x.
left H4.
pose proof H5 H3.
apply (disj_in_2 ((x = a ∨ x = b)) (x = c) H6).
intro.
apply (disj_el _ _ _ H).
intro.
apply (disj_el _ _ _ H0).
intro.
pose proof unit_a_prop x.
right H2.
pose proof H3 H1.
pose proof disj_in_1 _ (x ∈ unit_b) H4.
pose proof union_a_b_prop x.
right H6.
pose proof H7 H5.
pose proof union_a_b_c_prop x.
right H9.
apply H10.
apply (disj_in_1 _ _ H8).
intro.
pose proof unit_b_prop x.
right H2.
pose proof H3 H1.
pose proof disj_in_2 (x ∈ unit_a) (x ∈ unit_b) H4.
pose proof union_a_b_prop x.
right H6.
pose proof H7 H5.
pose proof union_a_b_c_prop x.
right H9.
apply H10.
apply (disj_in_1 _ _ H8).
intro.
pose proof  unit_c_prop x.
right H1.
pose proof H2 H0.
pose proof union_a_b_c_prop x.
right H4.
apply H5.
apply (disj_in_2 _ _ H3).
apply (any_biimpl_set_is_no_more_than_one _).
Defined.

Definition triple_unord(a b c: Set) := ι _ (triple_unord_exists a b c).

Notation "{ a , b , c }" := (triple_unord a b c).

Definition quadriple_unord_exists (a b c d: Set): ∃1t. 
(∀ x. ((x ∈ t) ⇔ ((x = a) ∨ (x = b) ∨ (x = c) ∨ (x = d)))).
pose proof triple_unord_exists a b c.
conj_el H.
destruct_ex H0 l.
pose proof union2_exists l ({`d}).
conj_el H3.
clear H1 H5.
destruct_ex H4 s.
clear H H0 H3 H4.
apply (conj_in).
apply (ex_in _ s).
intro x.
apply conj_in.
intro.
pose proof H1 x.
conj_el H0.
pose proof H3 H.
apply (disj_el _ _ _ H5).
intro.
apply disj_in_1.
pose proof H2 x.
pose proof biimpl_el_1 _ _ H7.
apply H8.
assumption.
intro.
apply disj_in_2.
extract_iota ({`d}) H6.
pose proof (iota_prop x).
pose proof biimpl_el_1 _ _ H7.
apply H8.
apply H6.
intro.
apply (disj_el _ _ _ H).
pose proof biimpl_el_2 _ _ (H2 x).
intro.
pose proof H0 H3.
pose proof biimpl_el_2 _ _ (H1 x).
apply H5.
apply disj_in_1.
apply H4.
intro.
pose proof biimpl_el_2 _ _ (H1 x).
apply H3.
apply disj_in_2.
repl_in_goal H0.
pose proof every_set_is_in_unit_set d.
apply H4.
intros q w.
intro.
intro.
apply ZF1_extension.
intro x.
pose proof H x.
pose proof H0 x.
simpl in H3.
simpl in H4.
pose proof biimpl_symm _ _ H3.
pose proof biimpl_trans _ _ _ H4 H5.
apply biimpl_symm.
apply H6.
Qed.

Definition quadriple_unord(a b c d: Set) := ι _ (quadriple_unord_exists a b c d).

Notation "{ a , b , c , d }" := (quadriple_unord a b c d).

Definition relative_complement_exists (a b: Set): ∃1c. 
(∀ x. ((x ∈ c) ⇔ ((x ∈ a) ∧ ¬(x ∈ b)))).
pose proof unique_subset_exists (fun x => ¬(x ∈ b) ) a.
cbv beta in H.
apply H.
Defined.

(* The relative complement of b with respect to a set a (don't read backward!) *)
Definition relative_complement (a b: Set) := 
ι _ (relative_complement_exists a b). 

Notation "a - b" := (relative_complement a b)(at level 81, left associativity).

Definition symmetric_difference (a b: Set) :=
(relative_complement a b) ∪ (relative_complement b a).

Notation "a + b" := (symmetric_difference a b)(at level 81, left associativity).

Definition pair (a b: Set) := { (unit_set a) , { a, b } }. 

Notation "⟨ a , b ⟩" := (pair a b)(at level 0, a at level 99, b at level 99).

Definition triple (a b c: Set) := ⟨⟨a, b⟩, c⟩.

Notation "⟨ a , b , c ⟩" := (triple a b c)(at level 0, a at level 99, b at level 99, c at level 99).

Definition tuple4 (a b c d: Set) := ⟨(triple a b c), d⟩.
Definition tuple5 (a b c d e: Set) := ⟨(tuple4 a b c d), e⟩.
Definition tuple6 (a b c d e f: Set) := ⟨(tuple5 a b c d e), f⟩.
Definition tuple7 (a b c d e f g: Set) := ⟨(tuple6 a b c d e f), g⟩.

Definition is_pair(p: Set) :=  ∃a. ∃b. p = ⟨a, b⟩.

Definition triple_is_pair(a b c: Set) : is_pair (triple a b c).
unfold triple.
unfold is_pair.
apply(ex_in _ (⟨ a, b ⟩)).
apply(ex_in _ (c)).
apply eq_refl.
Defined.

Definition tuple4_is_pair(a b c d: Set) : is_pair (tuple4 a b c d).
unfold tuple4.
unfold is_pair.
apply(ex_in _ (⟨ a, b, c ⟩)).
apply(ex_in _ (d)).
apply eq_refl.
Defined.

Definition tuple5_is_pair(a b c d e: Set) : is_pair (tuple5 a b c d e).
apply(ex_in _ (tuple4 a b c d)).
apply(ex_in _ (e)).
apply eq_refl.
Defined.

Definition tuple6_is_pair(a b c d e f: Set) : is_pair (tuple6 a b c d e f).
apply(ex_in _ (tuple5 a b c d e)).
apply(ex_in _ (f)).
apply eq_refl.
Defined.

Definition tuple7_is_pair(a b c d e f g: Set) : is_pair (tuple7 a b c d e f g).
apply(ex_in _ (tuple6 a b c d e f)).
apply(ex_in _ (g)).
apply eq_refl.
Defined.

Definition is_tuple7(p: Set) :=  ∃a. ∃b. ∃c. ∃d. ∃e. ∃f. ∃g. p = (tuple7 a b c d e f g).

Definition pair_is_never_empty(p: Set)(p_is_pair: is_pair p): ¬(p = ∅).
intro.
extract_iota ∅ H.
unfold is_pair in p_is_pair.
destruct_ex p_is_pair a.
destruct_ex H0 b.
repl H iota_prop.
unfold pair in H1.
extract_iota ({{`a}, {a, b}}) H1.
pose proof iota_prop1 {`a} .
right H2.
pose proof iota_prop0 {`a}.
apply H4.
repl H1 H3.
apply H5.
apply (disj_in_1).
apply (eq_refl ({`a})).
Defined.
Definition it_is_a_pair(x y p: Set) (E: p = ⟨x, y⟩): is_pair p.
unfold is_pair.
apply (ex_in _ x).
apply (ex_in _ y).
apply E.
Defined.

Definition pair_obviously_exists {L: Set} {M: Set} (z a b: Set)
(z_eq_pair : z = (⟨ a, b ⟩))
(a_in_L: a ∈ L) (b_in_M: b ∈ M): 
∃ x :: L . ∃ y :: M . z = (⟨ x, y ⟩).
apply (ex_in _ a).
apply conj_in.
apply a_in_L.
apply (ex_in _ b).
apply conj_in.
apply b_in_M.
apply z_eq_pair.
Defined.

Definition tuple5_arg2_obviously_exists {X: Set} {Y: Set} {A: Set} {B: Set} {C: Set}
(w x y a b c: Set)
(w_eq_tuple : w = (⟨ ⟨ x, y ⟩, ⟨ a, b, c ⟩ ⟩))
(x_in_X: x ∈ X) 
(y_in_Y: y ∈ Y)
(a_in_A: a ∈ A) 
(b_in_B: b ∈ B)
(c_in_C: c ∈ C): 
∃ x :: X. ∃ y :: Y
. ∃ a :: A . ∃ b :: B . ∃ c :: C
. w = (⟨ ⟨ x, y ⟩, ⟨ a, b, c ⟩ ⟩).
apply (ex_in _ x).
apply conj_in.
apply x_in_X.
apply (ex_in _ y).
apply conj_in.
apply y_in_Y.
apply (ex_in _ a).
apply conj_in.
apply a_in_A.
apply (ex_in _ b).
apply conj_in.
apply b_in_B.
apply (ex_in _ c).
apply conj_in.
apply c_in_C.
apply w_eq_tuple.
Defined.


Definition pr1_formula(p: Set)(p_is_pair: is_pair p) := 
(union (intersection p (pair_is_never_empty p p_is_pair))).

Definition element_of_unit_set (k u: Set): k ∈ (unit_set u) -> k = u.
intro.
pose proof unit_set_exists u.
left H0.
destruct_ex H1 a.
pose proof lemma_12_7_1 _ (unit_set_exists u) a H2.
pose proof eq_subs (fun g => k ∈ (g)) _ _ (eq_symm _ _ H3) H.
cbv beta in H4.
pose proof H2 k.
left H5.
apply H6.
apply H4.
Defined.

Definition intersection_of_pair(x y p: Set)(E: p = ⟨x, y⟩)(M: is_pair p): 
(intersection p (pair_is_never_empty p M)) = {`x}.
apply (ZF1_extension).
intro k.
apply (conj_in).
intro.
extract_iota (intersection p (pair_is_never_empty p M)) H.
pose proof iota_prop k.
cbv beta in H0.
left H0.
pose proof H1 H.
pose proof H2 {`x}.
apply H3.
unfold pair in E.
extract_iota ({{`x}, {x, y}}) E.
pose proof iota_prop0 {`x}.
right H4.
repl E H5.
apply H6.
apply (disj_in_1).
apply (eq_refl {`x}).
intro.
pose proof element_of_unit_set _ _ H.
repl H0 E.
unfold pair in E0.
extract_iota_from_goal (intersection p (pair_is_never_empty p M)).
pose proof iota_prop k.
right H1.
apply H2.
intro t.
intro.
extract_iota ({{`k}, {k, y}}) E0.
pose proof iota_prop0 t.
left H4.
repl E0 H3.
pose proof H5 H6.
cbv beta in H7.
apply (disj_el _ _ _ H7).
intro.
extract_iota ({`k}) H8.
pose proof iota_prop1 k.
right H9.
repl H8 H10.
apply H11.
apply (eq_refl k).
intro.
pose proof H8: (t = {k, y}).
extract_iota ({k, y}) H9.
pose proof iota_prop1 k.
right H10.
repl H9 H11.
apply H12.
apply (disj_in_1).
apply (eq_refl k).
Defined.

Definition pr1_formula_prop (x y p: Set) (E: p = ⟨x, y⟩) (M: is_pair p): (pr1_formula p M) = x.
unfold pr1_formula.
apply (ZF1_extension).
intro z.
apply (conj_in).
intro.
pose proof intersection_of_pair x y p E M.
pose proof eq_subs (fun g => z ∈ union g) _ _ H0 H.
cbv beta in H1.
extract_iota (union {`x}) H1.
pose proof iota_prop z.
left H2.
pose proof H3 H1.
cbv beta in H4.
destruct_ex H4 k.
left H5.
right H5.
pose proof element_of_unit_set _ _ H7.
repl H8 H6.
apply H9.
intro.
pose proof intersection_of_pair x y p E M.
pose proof eq_subs (fun k=> z ∈ union k) _ _ (eq_symm _ _ H0).
cbv beta in H1.
apply H1.
clear H1.
extract_iota_from_goal (union {`x}).
pose proof iota_prop z.
right H1.
apply H2.
apply (ex_in _ x).
apply (conj_in).
apply H.
apply (every_set_is_in_unit_set x).
Defined.

Definition pr1_exists(p: Set)(H: is_pair p): ∃1k. ∀x. ∀y. (p = ⟨x, y⟩) -> k = x.
apply (conj_in).
assert (∃l. l = pr1_formula p H).
apply (ex_in _ (pr1_formula p H)).
apply (eq_refl).
destruct_ex H0 x.
apply (ex_in _ x).
intros a b.
intro.
pose proof pr1_formula_prop a b p H2 H.
pose proof eq_trans _ _ _ H1 H3.
apply H4.
intros p1 p2.
intro.
intro.
unfold is_pair in H.
destruct_ex H a.
destruct_ex H2 b.
pose proof H0 a b H3.
pose proof eq_symm _ _ (H1 a b H3).
pose proof eq_trans _ _ _ H4 H5.
apply H6.
Defined.

Definition pr1(p: Set)(H: is_pair p):=  ι _ (pr1_exists p H).


Definition element_of_pair (k a b: Set): k ∈ ({a, b}) -> ((k = a) ∨ (k = b)).
intro.
pose proof pair_unord_exists a b.
left H0.
destruct_ex H1 p.
pose proof lemma_12_7_1 _ (pair_unord_exists a b) p H2.
pose proof eq_symm _ _ H3.
pose proof eq_subs (fun g => k ∈ g) _ _ H4 H.
cbv beta in H5.
pose proof H2 k.
cbv beta in H6.
left H6.
apply (H7 H5).
Defined.

Definition collapse_unit (u: Set): {u, u} = (unit_set u).
apply (ZF1_extension ({u, u}) (unit_set u)).
intro k.
apply (conj_in _ _).
intro.
extract_iota ({u, u}) H.
extract_iota_from_goal {`u}.
cbv beta in iota_prop0 .
pose proof iota_prop k.
cbv beta in H0.
left H0.
pose proof H1 H.
pose proof iota_prop0 k.
cbv beta in H3.
right H3.
apply H4.
apply (disj_el _ _ (k = u) H2).
intro.
apply H5.
intro.
apply H5.
intro.
extract_iota {`u} H.
extract_iota_from_goal {u, u}.
pose proof iota_prop k.
cbv beta in H0.
pose proof iota_prop0 k.
cbv beta in H1.
right H1.
apply H2.
left H0.
pose proof H3 H.
apply (disj_in_1 _ _ H4).
Defined.

Definition pair_unord_eq_to_unit_set (a b c: Set):
({a, b}) = (unit_set c) -> (a = c) ∧ (b = c).
intro.
pose proof pair_unord_exists a b.
left H0.
destruct_ex H1 p.
pose proof lemma_12_7_1 _ (pair_unord_exists a b) p H2.
pose proof eq_subs (fun g => g = (unit_set c)) _ _ (eq_symm _ _ H3) H.
cbv beta in H4.
pose proof unit_set_exists c.
left H5.
destruct_ex H6 u.
pose proof lemma_12_7_1 _ (unit_set_exists c) u H7.
pose proof eq_subs (fun g => p = g) _ _ (eq_symm _ _ H8) H4.
cbv beta in H9.
clear H3 H8.
pose proof H7 a.
cbv beta in H3.
left H3.
apply (conj_in _ _).
apply H8.
apply (eq_subs (fun g => a ∈ g) p u H9).
pose proof H2 a.
right H10.
apply H11.
pose proof eq_refl a.
apply (disj_in_1 _ _ H12).
pose proof H7 b.
cbv beta in H10.
left H10.
apply H11.
apply (eq_subs (fun g => b ∈ g) p u H9).
pose proof H2 b.
right H12.
apply H13.
pose proof eq_refl b.
apply (disj_in_2 _ _ H14).
Defined.

Definition pair_equals_to_set (a b k: Set): ({a, b} = k) -> (a ∈ k) ∧ (b ∈ k).
intro.
pose proof pair_unord_exists a b.
left H0.
destruct_ex H1 p.
pose proof lemma_12_7_1 _ (pair_unord_exists a b) p H2.
pose proof eq_symm _ _ H3.
pose proof eq_subs (fun g => g = k) _ _ H4 H.
cbv beta in H5.
pose proof eq_subs (fun g => ∀ x . x ∈ g ⇔ (x = a ∨ x = b)) p k H5 H2.
cbv beta in H6.
pose proof H6 a.
cbv beta in H7.
right H7.
apply (conj_in _ _).
apply H8.
apply (disj_in_1 _ _ (eq_refl a)).
pose proof H6 b.
right H9.
apply H10.
apply (disj_in_2 _ _ (eq_refl b)).
Defined.

Definition unit_set_property (x y: Set): ((unit_set x) = (unit_set y)) -> x = y.
intro.
pose proof unit_set_exists x.
left H0.
destruct_ex H1 p.
pose proof lemma_12_7_1 _ (unit_set_exists x) p H2.
pose proof eq_symm _ _ H3.
pose proof eq_subs (fun g => g = (unit_set y)) _ _ H4 H.
cbv beta in H5.
pose proof unit_set_exists y.
left H6.
destruct_ex H7 q.
pose proof lemma_12_7_1 _ (unit_set_exists y) q H8.
pose proof eq_symm _ _ H9.
pose proof eq_subs (fun g => p = g) _ _ H10 H5.
cbv beta in H11.
pose proof (H2: (∀ z . z ∈ p ⇔ z = x)).
pose proof (H8: (∀ x . x ∈ q ⇔ x = y)).
pose proof eq_subs (fun g => ∀ z . z ∈ g ⇔ z = x) p q H11 H12.
cbv beta in H14.
clear H12.
pose proof (H13: (∀ z . z ∈ q ⇔ z = y)).
clear H13.
pose proof H14 x.
cbv beta in H13.
right H13.
pose proof H15 (eq_refl x).
pose proof H2 x.
cbv beta in H17.
right H17.
pose proof H18 (eq_refl x).
pose proof eq_subs (fun g => x ∈ g) p (unit_set y) H5 H19.
cbv beta in H20.
pose proof element_of_unit_set x y.
apply (H21 H20).
Defined.

Definition pair_property {x y u v: Set}: (⟨x,y⟩ =  ⟨u,v⟩) -> (x = u) ∧ (y = v).
intro.
pose proof exc_thrd (u = v).
apply (disj_el _ _ (x = u ∧ y = v) H0).
intro.
unfold pair in H.
pose proof eq_subs (fun g => ({(unit_set x), {x, y}}) = 
({(unit_set u), {u, g}}))
v u (eq_symm _ _ H1) H.
cbv beta in H2.
pose proof collapse_unit u.
pose proof eq_subs (fun g => ({unit_set x, {x, y}}) = 
({unit_set u, g})) _ _ H3 H2.
cbv beta in H4.
pose proof collapse_unit (unit_set u).
pose proof eq_trans _ _ _ H4 H5.
pose proof pair_unord_eq_to_unit_set (unit_set x) ({x, y}) 
(unit_set u) H6.
right H7.
pose proof pair_unord_eq_to_unit_set x y u H8.
pose proof eq_subs (fun g => x = u ∧ y = g) u v H1 H9.
apply H10.
intro.
assert (¬ ((unit_set u) = {u, v})).
intro.
pose proof pair_unord_eq_to_unit_set u v u (eq_symm _ _ H2).
right H3.
pose proof eq_symm _ _ H4.
apply (H1 H5).
assert (¬ ((unit_set x) = {u, v})).
intro.
pose proof pair_unord_eq_to_unit_set u v x (eq_symm _ _ H3).
left H4.
right H4.
pose proof eq_symm _ _ H6.
pose proof eq_trans _ _ _ H5 H7.
apply (H1 H8).
assert ((unit_set x) ∈ {(unit_set u), {u, v} }).
unfold pair in H.
pose proof pair_equals_to_set _ _ _ H.
left H4.
apply H5.
pose proof element_of_pair _ _ _ H4.
pose proof disj_el ((unit_set x) = (unit_set u)) ((unit_set x) = ({u, v}))
 ((unit_set x) = (unit_set u)) H5 (fun g => g) ( fun g => abs_el _ (H3 g)).
pose proof unit_set_property x u H6.
refine (conj_in _ _ H7 _).
pose proof eq_symm _ _ H.
unfold pair in H8.
pose proof pair_unord_exists (unit_set x) {x, y}.
left H9.
destruct_ex H10 p.
pose proof lemma_12_7_1 _ (pair_unord_exists (unit_set x) {x, y}) p H11.
pose proof eq_symm _ _ H12.
pose proof eq_subs (fun g => {(unit_set u), {u, v}} = g) _ _ H13 H8.
cbv beta in H14.
pose proof pair_equals_to_set ({`u}) ({u,v}) p H14.
right H15.
pose proof H11 ({u, v}).
left H17.
pose proof H18 H16.
assert (¬ ({u, v} = (unit_set x))).
intro.
pose proof eq_symm _ _ H20.
apply (H3 H21).
apply (disj_el ({u, v} = (unit_set x)) ({u, v} = {x, y}) (y = v) H19).
intro.
apply (abs_el _ (H20 H21)).
intro.
assert (¬ ( (unit_set x) = {x, y})).
intro.
pose proof eq_symm _ _ H22.
pose proof eq_trans _ _ _ H21 H23.
pose proof eq_symm _ _ H24.
apply (H3 H25).
assert (¬ (x = y)).
intro.
pose proof eq_subs (fun x =>¬ ((unit_set x) = {x, y})) x y H23 H22.
cbv beta in H24.
pose proof collapse_unit  y.
pose proof eq_symm _ _ H25.
apply (H24 H26).
assert (¬ (y = u)).
intro.
pose proof eq_subs (fun y => ¬ (x = y)) y u H24 H23.
apply (H25 H7).
assert (y ∈ {u, v}).
pose proof eq_symm _ _ H21.
pose proof pair_equals_to_set x y ({u, v}) H25.
right H26.
apply H27.
pose proof element_of_pair y u v H25.
apply (disj_el (y = u) (y = v) (y = v) H26).
intro.
apply (H24 H27).
intro.
apply H27.
Defined.

Axiom ZF6_power_set: ∀a. ∃b. ∀x. (x ⊆ a) -> x ∈ b.

Definition power_set_exists: ∀a. ∃1b. 
(∀ x. ((x ∈ b) ⇔ ((x ⊆ a)))).
intro a.
pose proof ZF6_power_set a.
destruct_ex H b.
pose proof ZF2_subsets (fun x => (x ⊆ a)) b.
cbv beta in H1.
destruct_ex H1 c.
clear H1.
cbv beta in H.
clear H.
refine (conj_in _ _ _ (any_biimpl_set_is_no_more_than_one _)).
refine (ex_in _ c _).
intro x.
apply (conj_in _ _).
intro.
pose proof (H2 x).
cbv beta in H1.
left H1.
pose proof H3 H.
right H4.
apply H5.
intro.
pose proof H2 x.
cbv beta in H1.
right H1.
apply H3.
apply (conj_in _ _).
apply (H0 x H).
apply H.
Defined.

Definition power_set (a: Set) := ι _ (power_set_exists a).

Notation "'𝒫' a " := (power_set a)(at level 69, left associativity).

Definition cartesian_product_exists (a b: Set): ∃1c. 
(∀ w. ((w ∈ c) ⇔ ((∃x. (x ∈ a) ∧ (∃y. (y ∈ b) ∧ w = ⟨x,y⟩))))).
pose proof ZF2_subsets (
    fun w => (∃x. ∃y. ((¬(x = y)) ∧ (x ∈ a) ∧ (y ∈ b) ∧ (∀z. (z ∈ w) ⇔ 
    (z = {`x} ∨ z = {x, y}))))
     ∨ (∃x. (x ∈ a) ∧ (x ∈ b) ∧ (∀z. (z ∈ w) ⇔ z = {`x})
)) (𝒫(𝒫((a ∪ b)))).
refine (conj_in _ _ _ (any_biimpl_set_is_no_more_than_one _)).
destruct_ex H big.
apply (ex_in _ big).
clear H.
intro.
apply (conj_in _ _).
intro.
pose proof H0 x.
left H1.
pose proof H2 H.
clear H1 H2.
left H3.
right H3.
clear H3.
apply (disj_el _ _ _ H2).
intro.
clear H2.
destruct_ex H3 c.
clear H3.
destruct_ex H2 d.
clear H2.
left H3.
right H3.
clear H3.
apply (ex_in _ c).
left H2.
right H2.
left H3.
right H3.
refine (conj_in _ _ H7 _).
apply (ex_in _ d).
refine (conj_in _ _ H5 _).
unfold pair.
extract_iota_from_goal ({{`c}, {c, d}}).
pose proof iota_prop : ∀ x
. x ∈ s
⇔ (x = {`c}
∨ x =
{c, d}).
clear iota_prop.
apply (ZF1_extension x s).
intro m.
apply (conj_in _ _).
intro.
pose proof H4 m.
pose proof H8 m.
cbv beta in H10.
cbv beta in H11.
pose proof biimpl_symm _ _ H11.
pose proof (biimpl_trans _ _ _ H10 H12).
left H13.
apply H14.
apply H9.
intro.
pose proof H8 m.
left H10.
pose proof H11 H9.
pose proof H4 m.
right H13.
apply H14.
apply H12.
intro.
destruct_ex H3 w.
left H4.
right H4.
left H5.
right H5.
apply (ex_in _ w).
refine (conj_in _ _ H7 _).
apply (ex_in _ w).
refine (conj_in _ _ H8 _).
unfold pair.
extract_iota_from_goal ({{`w}, {w, w}}).
pose proof (iota_prop: ∀ x
. x ∈ s
⇔ (x = {`w}
∨ x =
{w,w})).
clear iota_prop.
clear H4 H5.
apply (ZF1_extension x s).
intro m.
apply (conj_in _ _).
intro.
pose proof H9 m.
right H5.
apply H10.
pose proof H6 m.
left H11.
pose proof H12 H4.
apply (disj_in_1 _ _ H13).
intro.
pose proof H6 m.
right H5.
apply H10.
pose proof H9 m.
left H11.
pose proof H12 H4.
apply (disj_el _ _ _ H13).
intro.
apply H14.
intro.
pose proof collapse_unit w.
pose proof eq_subs (fun g => m = g) _ _ H15 H14.
apply H16.
intro.
rename x into w.
pose proof H0 w.
right H1.
apply H2.
clear H1 H2.
destruct_ex H x.
left H1.
right H1.
clear H1.
clear H.
destruct_ex H3 y.
left H.
right H.
clear H.
apply (conj_in _ _).
2:{
pose proof exc_thrd (x = y).
apply (disj_el _ _ _ H).
intro.
refine (disj_in_2 _ _ _).
apply (ex_in _ x).
pose proof eq_subs (fun g=>g ∈ b) _ _ (eq_symm _ _ H5) H1.
cbv beta in H6.
pose proof (conj_in _ _ H2 H6).
refine (conj_in _ _ H7 _).
intro z.
apply (conj_in _ _).
intro.
pose proof eq_subs (fun g=>w = (⟨ x, g ⟩)) _ _ (eq_symm _ _ H5) H4.
cbv beta in H9.
unfold pair in H9.
extract_iota ({{`x}, {x, x}}) H9.
pose proof iota_prop : ∀ x0
. x0 ∈ s
⇔ (x0 = {`x}
∨ x0 =
{x, x}).
pose proof eq_subs (fun g=>z ∈ g) _ _ H9 H8.
cbv beta in H11.
pose proof H10 z.
cbv beta in H12.
left H12.
pose proof H13 H11.
apply (disj_el _ _ _ H14).
intro.
apply H15.
intro.
pose proof collapse_unit x.
pose proof eq_subs (fun g => z = g) _ _ H16 H15.
apply H17.
intro.
unfold pair in H4.
pose proof eq_subs (fun g => w = {g, {x, y}}) _ _ (eq_symm _ _ H8) H4.
cbv beta in H9.
pose proof eq_symm _ _ H9.
pose proof pair_equals_to_set _ _ _ H10.
left H11.
apply H12.
intro.
refine (disj_in_1 _ _ _).
apply (ex_in _ x).
apply (ex_in _ y).
apply (conj_in _ _).
apply (conj_in _ _).
apply (conj_in _ _).
apply H5.
apply H2.
apply H1.
pose proof eq_symm _ _ H4.
pose proof pair_equals_to_set _ _ _ H6.
unfold pair in H6.
pose proof (pair_unord_exists {`x}
(ι (fun b => ∀ x0. ((x0 ∈ b) ⇔ (x0 = x ∨ x0 = y)))
(pair_unord_exists x y))).
left H8.
destruct_ex H9 r.
pose proof lemma_12_7_1 _ (pair_unord_exists {`x}
(ι (fun b => ∀ x0. ((x0 ∈ b) ⇔ (x0 = x ∨ x0 = y)))
(pair_unord_exists x y))) r H10.
pose proof eq_symm _ _ H11.
pose proof eq_subs (fun g=> g = w) _ _ H12 H6.
cbv beta in H13.
pose proof (H10 :∀ z. z ∈ r⇔ (z = {`x}∨ z ={x, y})).
pose proof eq_subs (fun g => ∀ z . z ∈ g ⇔ (z = {`x} ∨ z = {x, y})) r w H13 H14.
cbv beta in H15.
apply H15.
}
clear H3.
assert ({`x} ⊆ a).
intro m.
intro.
extract_iota {`x} H.
pose proof iota_prop m.
cbv beta in H3.
left H3.
pose proof H5 H.
pose proof eq_subs (fun g => g ∈ a) _ _ (eq_symm _ _ H6) H2.
apply H7.
assert ({`y} ⊆ b).
intro m.
intro.
extract_iota {`y} H3.
pose proof iota_prop m.
cbv beta in H5.
left H5.
pose proof H6 H3.
pose proof eq_subs (fun g => g ∈ b) _ _ (eq_symm _ _ H7) H1.
apply H8.

assert (∃ p_p_a_b. p_p_a_b = 𝒫 (𝒫 (a ∪ b))).
pose proof power_set_exists (𝒫 (a ∪ b)).
left H5.
destruct_ex H6 p_p_a_b.
pose proof lemma_12_7_1 _ (power_set_exists (𝒫 (a ∪ b))) p_p_a_b H7.
apply (ex_in _ p_p_a_b).
apply H8.
destruct_ex H5 p_p_a_b.

assert (∃ p_a_b. p_a_b = (𝒫 (a ∪ b))).
pose proof power_set_exists ((a ∪ b)).
left H7.
destruct_ex H8 p_a_b.
pose proof lemma_12_7_1 _ (power_set_exists ((a ∪ b))) p_a_b H9.
apply (ex_in _ p_a_b).
apply H10.
destruct_ex H7 p_a_b.

assert (∃ a_b. a_b = ((a ∪ b))).
pose proof union2_exists a b.
left H9.
destruct_ex H10 a_b.
pose proof lemma_12_7_1 _ (union2_exists a b) a_b H11.
apply (ex_in _ a_b).
apply H12.
destruct_ex H9 a_b.
clear H5 H7 H9.

assert ({`x} ⊆ a_b).
intro e.
intro.
pose proof element_of_unit_set e x H5.
pose proof H10.
extract_iota (a ∪ b) H9.
pose proof eq_subs (fun g => ∀ x . x ∈ g ⇔ (x ∈ a ∨ x ∈ b)) 
_ _ (eq_symm _ _ H9) iota_prop.
cbv beta in H11.
pose proof H11 e.
right H12.
apply H13.
pose proof eq_subs (fun g => g ∈ a ∨ g ∈ b) _ _ (eq_symm _ _ H7).
apply H14.
apply (disj_in_1 _ _ H2).

pose proof H10.
extract_iota (a ∪ b) H7.
pose proof eq_subs (fun g => ∀ x . x ∈ g ⇔ (x ∈ a ∨ x ∈ b)) 
_ _ (eq_symm _ _ H7) iota_prop.
cbv beta in H9.
clear H7 iota_prop.
clear s.

pose proof H8.
extract_iota (𝒫 (a ∪ b)) H7.
pose proof eq_subs (fun g => ∀ x . x ∈ g ⇔ x ⊆ (a ∪ b)) 
_ _ (eq_symm _ _ H7) iota_prop.
cbv beta in H11.
clear H7 iota_prop s.

pose proof H6.
extract_iota (𝒫 (𝒫 (a ∪ b))) H7.
pose proof (iota_prop : ∀ x. x ∈ s ⇔ x ⊆ (𝒫(a ∪ b))).
pose proof eq_subs (fun g => ∀ x . x ∈ g ⇔ x ⊆ 𝒫 (a ∪ b)) 
_ _ (eq_symm _ _ H7) iota_prop.
cbv beta in H13.
clear H7 iota_prop s H12.

assert ({x, y} ⊆ a_b).
intro m.
intro.
pose proof element_of_pair m x y H7.
clear H7.
pose proof H9 m.
right H7.
apply H14.
apply (disj_el _ _ _ H12).
intro.
pose proof eq_subs (fun g => g ∈ a) _ _ (eq_symm _ _ H15) H2.
apply (disj_in_1 _ _ H16).
intro.
pose proof eq_subs (fun g => g ∈ b) _ _ (eq_symm _ _ H15) H1.
apply (disj_in_2 _ _ H16).

assert ({`x} ∈ p_a_b).
pose proof H11 ({`x}).
right H12.
apply H14.
intro g.
intro.
pose proof element_of_unit_set g x H15.
pose proof eq_subs (fun g => g ∈ (a ∪ b)) _ _ (eq_symm _ _ H16).
apply H17.
pose proof eq_subs (fun g => x ∈ g) _ _ (H10).
apply H18.
pose proof H9 x.
right H19.
apply H20.
apply (disj_in_1 _ _ H2).

assert ({x, y} ∈ p_a_b).
pose proof H11 ({x, y}).
right H14.
apply H15.
intro g.
intro.
pose proof element_of_pair g x y H16.
apply (disj_el _ _ _ H17).
intro.
pose proof eq_subs (fun g => g ∈ (a ∪ b)) _ _ (eq_symm _ _ H18).
apply H19.
pose proof eq_subs (fun g => x ∈ g) _ _ (H10).
apply H20.
pose proof H9 x.
right H21.
apply H22.
apply (disj_in_1 _ _ H2).
intro.
pose proof eq_subs (fun g => g ∈ (a ∪ b)) _ _ (eq_symm _ _ H18).
apply H19.
pose proof eq_subs (fun g => y ∈ g) _ _ (H10).
apply H20.
pose proof H9 y.
right H21.
apply H22.
apply (disj_in_2 _ _ H1).

assert (w ⊆ p_a_b).
intro h.
intro.
pose proof H4.
unfold pair in H16.
extract_iota {{`x}, {x, y}} H16.
pose proof (iota_prop : ∀ x0. x0 ∈ s⇔ (x0 = {`x}∨ x0 ={x , y })).
pose proof eq_subs (fun g => 
∀ x0 . x0 ∈ g ⇔ (x0 = {`x} ∨ x0 = {x, y})) _ _ (eq_symm _ _ H16) H17.
cbv beta in H18.
pose proof H18 h.
left H19.
pose proof H20 H15.
pose proof H11 h.
right H22.
apply H23.
intro l.
intro.
pose proof eq_subs (fun g => l ∈ (g)) _ _ H10.
apply H25.
pose proof H9 l.
right H26.
apply H27.
apply (disj_el _ _ _ H21).
intro.
extract_iota {`x} H28.
pose proof eq_subs (fun g => ∀ x0 . x0 ∈ g ⇔ x0 = x) _ _ 
(eq_symm _ _ H28) iota_prop0 .
cbv beta in H29.
pose proof H29 l.
left H30.
pose proof H31 H24.
pose proof eq_subs (fun g => g ∈ a) _ _ (eq_symm _ _ H32) H2.
apply (disj_in_1 _ _  H33).
intro.
extract_iota {x ,y} H28.
pose proof eq_subs (fun g => ∀ x0 . x0 ∈ g ⇔ (x0 = x ∨ x0 = y)) _ _ 
(eq_symm _ _ H28) iota_prop0 .
pose proof H29 l.
left H30.
pose proof H31 H24.
apply (disj_el _ _ _ H32).
intro.
pose proof eq_subs (fun g => g ∈ a) _ _ (eq_symm _ _ H33) H2.
apply (disj_in_1 _ _  H34).
intro.
pose proof eq_subs (fun g => g ∈ b) _ _ (eq_symm _ _ H33) H1.
apply (disj_in_2 _ _  H34).
pose proof eq_subs (fun g => ∀ x . x ∈ p_p_a_b ⇔ x ⊆ g)
 _ _ (eq_symm _ _ H8) H13.
 cbv beta in H16.
 pose proof H16 w.
 right H17.
 pose proof H18 H15.
 pose proof eq_subs (fun g => w ∈ g) _ _ H6 H19.
 apply H20.
 Defined.

Definition cartesian_product (a b: Set) := ι _ (cartesian_product_exists a b).

Notation "a × b" := (cartesian_product a b)(at level 70).

Definition relation (a: Set) := ∀x. (x ∈ a) -> ∃m. ∃n. x = ⟨m,n⟩.

Definition relation_is_subset_of_cp_with_itself: ∀r. (relation r) ->  
r ⊆ (union (union r)) × (union (union r)).
intro r.
intro.
unfold relation in H.
intro m.
intro.
extract_iota_from_goal (union (union r) × union (union r)).
pose proof iota_prop m.
right H1.
apply H2.
pose proof H m.
pose proof H3 H0.
destruct_ex H4 x.
destruct_ex H5 y.
apply (ex_in _ x).
apply (conj_in _ _).
extract_iota_from_goal (union (union r)).
pose proof iota_prop0: ∀ x. x ∈ s0⇔ (∃ y. x ∈ y∧ y∈ union r).
clear iota_prop0.
pose proof H7 x.
right H8.
apply H9.
unfold pair in H6.
pose proof pair_unord_exists x y.
left H10.
destruct_ex H11 x_y.
apply (ex_in _ x_y).
apply (conj_in _ _).
pose proof H12 x.
right H13.
apply H14.
apply (disj_in_1 _ _ (eq_refl x)).
extract_iota_from_goal (union r).
pose proof iota_prop0 x_y.
right H13.
apply H14.
apply (ex_in _ m).
apply (conj_in _ _).
extract_iota ({{`x}, {x, y}}) H6.
pose proof iota_prop1:∀ x0. x0 ∈ s2⇔ (x0 = {`x}∨ x0 ={x, y}).
pose proof H15 x_y.
right H16.
pose proof eq_subs(fun g=>(x_y = {`x} ∨ x_y = {x, y}) ⇒ (x_y ∈ g)) _ _
(eq_symm _ _ H6) H17.
apply H18.
refine (disj_in_2 _ _ _).
extract_iota_from_goal ({x, y}).
pose proof H12.
apply (ZF1_extension x_y s3).
intro o.
pose proof iota_prop2 o.
cbv beta in H20.
pose proof H19 o.
cbv beta in H21.
pose proof biimpl_trans _ _ _ H20 (biimpl_symm _ _ H21).
pose proof biimpl_symm _ _ H22.
apply H23.
apply H0.
apply (ex_in _ y).
apply (conj_in _ _).
extract_iota_from_goal (union (union r)).
pose proof iota_prop0 : ∀ x. x ∈ s0⇔ (∃ y
. x ∈ y ∧ y ∈ union r).
pose proof H7 y.
right H8.
apply H9.
pose proof pair_unord_exists x y.
left H10.
destruct_ex H11 x_y.
apply (ex_in _ x_y).
apply (conj_in _ _).
pose proof H12 y.
right H13.
apply H14.
refine (disj_in_2 _ _ (eq_refl y)).
extract_iota_from_goal (union r).
pose proof iota_prop1 x_y.
right H13.
apply H14.
apply (ex_in _ m).
apply (conj_in _ _).
unfold pair in H6.
extract_iota ({{`x}, {x, y}}) H6.
pose proof iota_prop2:∀ x0. x0 ∈ s2⇔ (x0 = {`x}∨ x0 ={x, y}).
pose proof H15 x_y.
right H16.
pose proof eq_subs(fun g=>(x_y = {`x} ∨ x_y = {x, y}) ⇒ (x_y ∈ g)) _ _
(eq_symm _ _ H6) H17.
apply H18.
refine (disj_in_2 _ _ _).
extract_iota_from_goal ({x, y}).
pose proof H12.
apply (ZF1_extension x_y s3).
intro o.
pose proof iota_prop3 o.
cbv beta in H20.
pose proof H19 o.
cbv beta in H21.
pose proof biimpl_trans _ _ _ H20 (biimpl_symm _ _ H21).
pose proof biimpl_symm _ _ H22.
apply H23.
apply H0.
apply H6.
Defined.

Definition domain_exists (r: Set): ∃1d. 
(∀ x. ((x ∈ d) ⇔ ((∃y. ⟨x,y⟩ ∈ r )))).
apply (conj_in _ _).
pose proof ZF2_subsets (fun x => (∃y. ⟨x,y⟩ ∈ r ))
((union (union r))).
cbv beta in H.
destruct_ex H d.
apply (ex_in _ d). (* GOOD *)
intro q.
apply (conj_in _ _).
intro.
pose proof H0 q.
left H2.
pose proof H3 H1.
right H4.
apply H5.  (* PART 2 *)
pose proof H0 q.
intro.
right H1.
apply H3.
apply (conj_in _ _).
destruct_ex H2 y.
clear H2.
unfold pair in H4.
pose proof pair_unord_exists {`q} {q, y}.
left H2.
destruct_ex H5 q_y.
pose proof lemma_12_7_1 _ (pair_unord_exists {`q} {q, y}) q_y H6.
pose proof eq_symm _ _ H7.
pose proof eq_subs (fun g=> g ∈ r) _ _ H8 H4.
cbv beta in H9.
clear H7 H8.
extract_iota_from_goal (union (union r)).
pose proof iota_prop : ∀ x. x ∈ s⇔ (∃ y
. x ∈ y ∧ y ∈ (union r)).
clear iota_prop.
pose proof H7 q.
right H8.
apply H10.
pose proof pair_unord_exists q y.
left H11.
destruct_ex H12 q_y_unord.
apply (ex_in _ q_y_unord).
apply (conj_in _ _).
pose proof H13 q.
right H14.
apply H15.
apply (disj_in_1 _ _ (eq_refl q)).
extract_iota_from_goal (union r).
pose proof iota_prop q_y_unord.
right H14.
apply H15.
apply (ex_in _ q_y).
apply (conj_in _ _).
pose proof H6 q_y_unord.
right H16.
apply H17.
refine (disj_in_2 _ _ _).
extract_iota_from_goal {q, y}.
apply (ZF1_extension q_y_unord s1).
intro x.
pose proof H13 x.
pose proof iota_prop0 x.
cbv beta in H18, H19.
pose proof (biimpl_trans _ _ _ H18 (biimpl_symm _ _ H19)).
apply H20.
apply H9.
apply H2.
apply (any_biimpl_set_is_no_more_than_one _).
Defined.

Definition domain (r: Set):= ι _ (domain_exists r).

Definition range_exists (r: Set): ∃1d. 
(∀ y. ((y ∈ d) ⇔ ((∃x. ⟨x,y⟩ ∈ r )))).
apply (conj_in _ _).
pose proof ZF2_subsets (fun y => (∃x. ⟨x,y⟩ ∈ r ))
((union (union r))).
cbv beta in H.
destruct_ex H d.
apply (ex_in _ d). (* GOOD *)
intro q.
apply (conj_in _ _).
intro.
pose proof H0 q.
left H2.
pose proof H3 H1.
right H4.
apply H5.  (* PART 2 *)
pose proof H0 q.
intro.
right H1.
apply H3.
apply (conj_in _ _).
destruct_ex H2 y.
clear H2.
unfold pair in H4.
pose proof pair_unord_exists {`y} {y, q}.
left H2.
destruct_ex H5 q_y.
pose proof lemma_12_7_1 _ (pair_unord_exists {`y} {y, q}) q_y H6.
pose proof eq_symm _ _ H7.
pose proof eq_subs (fun g=> g ∈ r) _ _ H8 H4.
cbv beta in H9.
clear H7 H8.
extract_iota_from_goal (union (union r)).
pose proof iota_prop : ∀ x. x ∈ s⇔ (∃ y
. x ∈ y ∧ y ∈ (union r)).
clear iota_prop.
pose proof H7 q.
right H8.
apply H10.
pose proof pair_unord_exists y q.
left H11.
destruct_ex H12 q_y_unord.
apply (ex_in _ q_y_unord).
apply (conj_in _ _).
pose proof H13 q.
right H14.
apply H15.
apply (disj_in_2 _ _ (eq_refl q)).
extract_iota_from_goal (union r).
pose proof iota_prop q_y_unord.
right H14.
apply H15.
apply (ex_in _ q_y).
apply (conj_in _ _).
pose proof H6 q_y_unord.
right H16.
apply H17.
refine (disj_in_2 _ _ _).
extract_iota_from_goal {y, q}.
apply (ZF1_extension q_y_unord s1).
intro x.
pose proof H13 x.
pose proof iota_prop0 x.
cbv beta in H18, H19.
pose proof (biimpl_trans _ _ _ H18 (biimpl_symm _ _ H19)).
apply H20.
apply H9.
apply H2.
apply (any_biimpl_set_is_no_more_than_one _).
Defined.

Definition S (x: Set) := x ∪ {`x}.

Definition is_successor_set (a: Set) := (∅ ∈ a) ∧ (∀x. ((x ∈ a) -> (S x) ∈ a)).

Definition subset_refl (a: Set): a ⊆ a.
intro x.
intro.
apply H.
Defined.

Definition set_equals_to_empty_set (empty_set: Set) (g: ∀ x. ¬ (x ∈ empty_set)): 
empty_set = ∅.
extract_iota_from_goal ∅.
apply (ZF1_extension empty_set s).
intro.
apply (conj_in _ _).
intro.
pose proof g x H.
apply (abs_el _ H0).
intro.
pose proof iota_prop x H.
apply (abs_el _ H0).
Defined.


Definition min_successor_set_exists : ∃1w. (is_successor_set w) 
∧ (∀z. (is_successor_set z) -> w ⊆ z).
apply (conj_in _ _).
pose proof ZF6_infinity.
destruct_ex H some_successor_set.
left H0.
right H0.
clear H0.
destruct_ex H1 empty_set'.
clear H1.
clear H.
rename H2 into ss_main_prop.
rename H0 into empty_set_prop.
pose proof power_set_exists some_successor_set as p_a_ex.
cbv beta in p_a_ex.
left p_a_ex.
destruct_ex H p_a.
clear p_a_ex H.
rename H0 into pa_prop.
pose proof unique_subset_exists 
(fun s=> (is_successor_set s)) p_a.
left H.
destruct_ex H0 subset_of_p_a.
clear H H0.
pose proof intersection_exists subset_of_p_a.
rename H1 into subset_of_p_a_prop.
assert (¬ (subset_of_p_a = ∅)).
intro.
extract_iota ∅ H0.
repl H0 iota_prop.
pose proof (iota_prop0 some_successor_set).
cbv beta in H1.
apply H1.
pose proof subset_of_p_a_prop some_successor_set.
right H2.
apply H3.
apply (conj_in _ _).
pose proof pa_prop some_successor_set.
right H4.
apply H5.
apply (subset_refl some_successor_set).
unfold is_successor_set.
apply (conj_in _ _).
right empty_set_prop.
assert (empty_set' = ∅).
apply (ZF1_extension _ _).
intro.
apply (conj_in _ _).
intro.
left empty_set_prop.
pose proof H6 x H5.
apply (abs_el _ H7).
intro.
extract_iota ∅ H5.
pose proof iota_prop1 x H5.
apply (abs_el _ H6).
repl H5 H4.
apply H6.
apply (ss_main_prop).
pose proof H H0.
clear H H0.
left H1.
destruct_ex H int_of_subset_of_p_a.
clear H1 H.
rename H0 into int_of_subset_of_p_a_prop.
apply (ex_in _ int_of_subset_of_p_a).
assert (is_successor_set int_of_subset_of_p_a).
apply (conj_in _ _).
pose proof int_of_subset_of_p_a_prop ∅.
right H.
apply H0. (* Good *)
intro y.
intro.
pose proof subset_of_p_a_prop y.
left H2.
pose proof H3 H1.
conj_el H4.
unfold is_successor_set in H6.
left H6.
apply H7.
intro x. (* Step 1*)
intro x_in_intersection.
pose proof int_of_subset_of_p_a_prop (S x).
right H.
apply H0. (* Moment *)
pose proof int_of_subset_of_p_a_prop x.
left H1.
pose proof H2 x_in_intersection. (* Step 2*)
intro y.
intro.
pose proof H3 y H4. (* Step 3*)
pose proof subset_of_p_a_prop y.
left H6.
pose proof H7 H4.
conj_el H8.
unfold is_successor_set in H10.
right H10.
pose proof H11 x H5.
apply H12.
rename H into part1.
apply (conj_in _ _).
apply part1.
intro b. (* subset of any ss *)
intro.
pose proof intersection2_exists some_successor_set b.
left H0.
destruct_ex H1 sss_b.
clear H0 H1.
assert (is_successor_set sss_b).
unfold is_successor_set.
apply (conj_in _ _).
pose proof H2 ∅.
right H0.
apply H1.
apply (conj_in _ _).
right empty_set_prop.
assert (empty_set' = ∅).
apply (ZF1_extension _ _).
intro.
apply (conj_in _ _).
intro.
left empty_set_prop.
pose proof H5 x H4.
apply (abs_el _ H6).
intro.
extract_iota ∅ H4.
pose proof iota_prop x H4.
apply (abs_el _ H5).
repl H4 H3.
apply H5.
left H.
apply H3.
intro.
intro.
pose proof H2 x.
left H1.
pose proof H3 H0.
conj_el H4.
pose proof H2 (S x).
right H7.
apply H8.
clear H4 H7 H8.
apply (conj_in _ _).
pose proof ss_main_prop x H5.
apply H4.
right H.
pose proof H4 x H6.
apply H7.
assert (sss_b ⊆ some_successor_set).
intro g.
intro.
pose proof H2 g.
left H3.
pose proof H4 H1.
left H5.
apply H6.
rename some_successor_set into a.
rename sss_b into a_inters_b.
rename int_of_subset_of_p_a into w.
rename int_of_subset_of_p_a_prop into w_prop.
assert (a_inters_b ∈ p_a).
pose proof pa_prop a_inters_b.
right H3.
apply H4.
apply H1.
assert (a_inters_b ∈ subset_of_p_a).
pose proof subset_of_p_a_prop a_inters_b.
right H4.
apply H5.
apply (conj_in _ _).
apply H3.
apply H0.
assert (w ⊆ a_inters_b).
intro t.
intro.
pose proof w_prop t.
left H6.
pose proof H7 H5.
pose proof H8 a_inters_b H4.
apply H9.
intro q.
intro.
pose proof H5 q.
pose proof H7 H6.
pose proof H2 q.
left H9.
pose proof H10 H8.
right H11.
apply H12.
intros a b.
intro.
intro.
conj_el H.
conj_el H0.
pose proof H2 b H3.
pose proof H4 a H1.
apply (ZF1_extension a b).
intro.
apply (conj_in _ _).
intro.
apply (H5 x H7).
intro.
apply (H6 x H7).
Defined.

Definition N := ι _ min_successor_set_exists.

Definition n_is_successor_set: is_successor_set N.
extract_iota_from_goal N.
left iota_prop.
apply H.
Defined.

Definition n_is_subset_of_any_successor_set: (∀z. (is_successor_set z) -> N ⊆ z).
extract_iota_from_goal N.
right iota_prop.
apply H.
Defined.

Definition extensionality_for_subsets {p q: Set}: (p ⊆ q) -> (q ⊆ p) -> p = q.
intros.
apply (ZF1_extension _ _).
intro x.
apply (conj_in _ _).
intro.
apply (H x H1).
intro.
apply (H0 x H1).
Defined.

Definition extensionality_for_subsets_with_conj {p q: Set}: 
((p ⊆ q) ∧ (q ⊆ p)) -> p = q.
intros.
apply (ZF1_extension _ _).
intro x.
apply (conj_in _ _).
intro.
left H.
apply (H1 x H0).
intro.
right H.
apply (H1 x H0).
Defined.

(* PEANO AXIOMS (not axioms but provable theorems for me) *)

Definition zero := ∅.
Notation "0" := zero.

Definition one := (S 0).
Notation "1" := one.

Definition two := (S 1).
Notation "2" := two.

Definition three := (S 2).
Notation "3" := three.

Definition four := (S 3).
Notation "4" := four.

Definition five := (S 4).
Notation "5" := five.

Definition PN1_empty_set: ∅ ∈ N.
extract_iota_from_goal N.
left iota_prop.
left H.
apply H0.
Defined.

Definition PN2_succ: ∀n. (n ∈ N) -> ((S n) ∈ N).
intro n. 
intro.
extract_iota N H.
left iota_prop.
unfold is_successor_set in H0.
right H0.
pose proof H1 n.
cbv beta in H2.
extract_iota_from_goal N.
pose proof H2 H.
assert (s = s0).
conj_el iota_prop.
conj_el iota_prop0.
pose proof H5 s0 H6.
pose proof H7 s H4.
apply (extensionality_for_subsets H8 H9).
repl H4 H3.
apply H5.
Defined.

Definition PN3_not_zero: ∀n. (n ∈ N) -> ¬((S n) = 0).
intro n.
intro.
unfold zero.
unfold S.
intro.
extract_iota ∅ H0.
extract_iota (n ∪ {`n}) H0.
repl H0 iota_prop0.
pose proof iota_prop1 n.
right H1.
pose proof iota_prop n.
apply H3.
apply H2.
apply (disj_in_2 _ _).
extract_iota_from_goal ({`n}).
pose proof iota_prop2 n.
right H4.
apply H5.
apply (eq_refl n).
Defined.

(*
Attempt 1 - 74 lines of code 
Attempt 2 - 51 lines of code (done on august 12, 2026)
*)
Definition PN5_induction: forall (P: Set->Prop), 
(P 0) -> (∀x :: N. P x -> (P (S x))) ->  (∀x :: N. P x).
intros.
intro x.
intro.
pose proof ZF2_subsets P N.
cbv beta in H2.
destruct_ex H2 b.
pose proof H3 x.
left H4.
assert (b = N).
apply (extensionality_for_subsets).
intro t.
intro.
pose proof H3 t.
left H7.
pose proof H8 H6.
left H9.
apply H10.
extract_iota_from_goal N.
right iota_prop.
apply (H6 b).
apply (conj_in _ _).
pose proof H3 ∅.
right H7.
apply H8.
apply (conj_in _ _).
extract_iota_from_goal N.
left iota_prop0.
left H9.
apply H10.
apply H.
intro u.
intro.
pose proof H3 u.
left H8.
pose proof H9 H7.
left H10.
extract_iota_ex N H11 retain_equality.
left iota_prop0.
right H12.
pose proof H13 u H11.
pose proof H3 (S u).
right H15.
apply H16.
apply (conj_in _ _).
assert (s0 = N).
apply (extensionality_for_subsets).
extract_iota_from_goal_ex N retain_equality.
intro g.
intro.
pose proof eq_symm _ _ eq_to_iota0.
pose proof eq_trans _ _ _ eq_to_iota H18.
repl H19 H17.
apply H20.
pose proof (eq_subs (fun g=>N ⊆ g) _ _ (eq_symm _ _ eq_to_iota)).
apply H17.
apply (subset_refl N).
repl H17 H11.
repl H17 H12.
right H19.
pose proof H20 u H18.
apply H21.
right H10.
repl eq_to_iota H11.
pose proof H0 u.
pose proof H19 H18.
apply H20.
apply H17.
repl H6 H5.
pose proof H7 H1.
right H8.
apply H9.
Defined.

Definition lt (a b: Set) := a ∈ b.

Declare Scope direct_relations.
Open Scope direct_relations.
Notation "a < b" := (lt a b)(at level 70):direct_relations.

Definition le (a b: Set) := (a < b) ∨ (a = b).

Notation "a ≤ b" := (le a b)(at level 70):direct_relations.

Definition ordinary_induction_prop:= forall (P: Set->Prop), 
(P 0) -> 
(∀x :: N. P x -> (P (S x))) ->  
(∀x :: N. P x).

Definition strong_induction_prop:= forall (P: Set->Prop), 
(P 0) -> 
(∀x :: N. (∀k :: N. (k ≤ x) -> P k) -> (P (S x))) -> 
(∀x :: N. P x).

Definition only_zero_is_less_than_one (k: Set) 
(k_is_nn: k ∈ N) (H: k < S 0): k = 0.
unfold lt in H.
unfold S in H.
unfold zero in H.
extract_iota (∅ ∪ {`∅}) H.
extract_iota N k_is_nn.
pose proof iota_prop k.
left H0.
pose proof H1 H.
apply (disj_el _ _ _ H2).
intro.
extract_iota ∅ H3.
pose proof iota_prop1 k H3.
apply (abs_el _ H4).
unfold zero.
unfold imp.
apply (element_of_unit_set k ∅).
Defined.

Definition only_zero_is_le_zero (k: Set) 
(k_is_nn: k ∈ N) (H: k ≤ 0): k = 0.
apply (disj_el _ _ _ H).
intro.
unfold zero in H0.
extract_iota ∅ H0.
pose proof iota_prop k.
pose proof H1 H0.
apply (abs_el _ H2).
intro.
apply H0.
Defined.

Definition zero_is_less_than_successor_of_any_nn (k: Set) 
(k_is_nn: k ∈ N): 0 < S k.
unfold zero.
unfold lt.
unfold S.
extract_iota_from_goal (k ∪ {`k}).
pose proof iota_prop ∅.
right H.
apply H0.
pose proof PN5_induction (fun k => ∅ ∈ k ∨ ∅ ∈ {`k}).
cbv beta in H1.
assert (∅ ∈ 0 ∨ ∅ ∈ {`0}).
apply (disj_in_2 _ _).
unfold zero.
extract_iota_from_goal ({`∅}).
pose proof iota_prop0 ∅.
cbv beta in H2.
right H2.
apply H3.
apply (eq_refl ∅).
pose proof H1 H2.
clear H1 H2.
assert ((∀ x :: N . (∅ ∈ x ∨ ∅ ∈ {`x}) -> ∅ ∈ S x ∨ ∅ ∈ {`S x})).
intro.
intro.
unfold S.
intro hyp.
apply (disj_el _ _ _ hyp).
intro.
apply (disj_in_1 _ _).
extract_iota_from_goal (x ∪ {`x}).
pose proof iota_prop0 ∅.
right H4.
apply H5.
apply (disj_in_1 _ _).
apply H2.
intro.
pose proof element_of_unit_set ∅ x H2.
apply (disj_in_1 _ _).
extract_iota_from_goal (x ∪ {`x}).
pose proof iota_prop0 ∅.
right H5.
apply H6.
apply (disj_in_2 _ _).
apply H2.
pose proof H3 H1 k k_is_nn.
apply H2.
Defined.

Definition zero_is_le_nn (k: Set) 
(k_is_nn: k ∈ N): 0 ≤ k.
unfold le.
pose proof PN5_induction (fun k => 0 < k ∨ 0 = k).
cbv beta in H.
assert (0 < 0 ∨ 0 = 0).
apply (disj_in_2 _ _).
apply (eq_refl 0).
assert ((∀ x :: N . (0 < x ∨ 0 = x) -> 0 < S x ∨ 0 = S x)).
intro.
intro.
intro.
apply (disj_el _ _ _ H2).
intro.
apply (disj_in_1 _ _).
unfold lt.
unfold S.
extract_iota_from_goal (x ∪ {`x}).
pose proof iota_prop 0.
right H4.
apply H5.
apply (disj_in_1 _ _).
apply H3.
intro.
apply (disj_in_1 _ _).
unfold S.
unfold lt.
extract_iota_from_goal  (x ∪ {`x}).
pose proof iota_prop 0.
right H4.
apply H5.
apply (disj_in_2 _ _).
pose proof every_set_is_in_unit_set x.
cbv beta in H6.
pose proof eq_subs (fun g => g ∈ {`x}) _ _ (eq_symm _ _ H3) H6.
apply H7.
pose proof H H0 H1 k k_is_nn.
apply H2.
Defined.

Definition elimitane_S_and_lt: ∀ x :: N. (∀ y :: N. (x  < (S y)) -> x ≤ y).
intro x.
intro.
intro y.
intro.
intro.
unfold le.
unfold S in H1.
unfold lt in H1.
unfold lt.
extract_iota (y ∪ {`y}) H1.
pose proof iota_prop x.
left H2.
apply (H3 H1).
intro.
apply (disj_in_1 _ _).
apply H4.
intro.
pose proof element_of_unit_set x y H4.
apply (disj_in_2 _ _).
apply H5.
Defined.

Definition move_left_from_S: ∀k. (k ∈ N) ->
∀y. (y ∈ N) -> (k ≤ S y) -> ((k ≤ y) ∨ (k = S y)).
intro k.
intro.
intro y.
intro.
intro.
apply (disj_el _ _ _ H1).
intro.
pose proof elimitane_S_and_lt k H y H0 H2.
apply (disj_in_1 _ _).
apply H3.
intro.
apply (disj_in_2 _ _).
apply H2.
Defined.

Definition ordinary_induction_is_equivalent_to_strong_induction:
ordinary_induction_prop ⇔ strong_induction_prop.
unfold ordinary_induction_prop.
unfold strong_induction_prop.
apply (conj_in _ _).
intro.
intro.
intro.
pose proof H (fun x =>(∀ k :: N. k ≤ x -> P k)).
cbv beta in H1.
assert (∀ k :: N. k ≤ 0 -> P k).
intro k.
intro.
intro.
pose proof only_zero_is_le_zero k H2 H3.
apply ((eq_subs (fun k => P k)) _ _ (eq_symm _ _ H4) H0).
pose proof H1 H2.
clear H1 H2.
intro strong_H.
intro x.
intro.
assert ((∀ x :: N . (∀ k :: N . k ≤ x -> P k) -> 
(∀ k :: N . k ≤ S x -> P k))).
intro y.
intro.
intro hyp.
intro k.
intro.
intro.
pose proof move_left_from_S k H4 y H2 H5.
apply (disj_el _ _ _ H6).
intro.
apply (hyp k H4 H7).
intro.
pose proof strong_H y H2.
apply ((eq_subs (fun k => P k)) _ _ (eq_symm _ _ H7)).
apply H8.
intro z.
intro.
apply (hyp z H9).
pose proof H3 H2 x H1 x H1.
apply H4.
apply (disj_in_2 _ _).
apply (eq_refl x).
intro.
intro P.
intro base.
intro s_i.
intro x.
intro.
pose proof H P base.
assert ((∀ x :: N . (∀ k :: N . k ≤ x -> P k) -> P (S x))).
intro z.
intro.
intro.
pose proof s_i z H2.
apply H4.
pose proof H3 z H2.
apply H5.
apply (disj_in_2 _ _).
apply (eq_refl z).
pose proof H1 H2 x H0.
apply H3.
Defined.

Definition subset_trans (a b c: Set): (a ⊆ b) -> (b ⊆ c) -> (a ⊆ c).
intros.
intro g.
intro.
apply (H0 g).
apply (H g).
apply H1.
Defined.

(* SUPER HARDCORE *)
Definition no_nat_is_subset_of_any_its_elements:
∀ a :: N . ∀ x :: a. ¬(a ⊆ x).
pose proof ZF2_subsets (fun a => ∀ x :: a. ¬(a ⊆ x)) N.
cbv beta in H.
destruct_ex H a.
pose proof H0: ∀ n . n ∈ a ⇔ (n ∈ N ∧ (∀ x :: n . ¬ (n ⊆ x))).
clear H0.
assert (0 ∈ a).
unfold zero.
pose proof H1 ∅.
right H0.
apply H2.
apply (conj_in _ _).
extract_iota_from_goal N.
left iota_prop.
left H3.
apply H4.
intro.
intro.
extract_iota ∅ H3.
pose proof iota_prop x H3.
apply (abs_el _ H4).
refine (_:∀ x :: N . (∀ n :: x . ¬ (x ⊆ n))).
assert (a = N).
apply (ZF1_extension).
intro g.
apply (conj_in _ _).
intro.
pose proof H1 g.
left H3.
pose proof H4 H2.
left H5.
apply H6.
intro.
assert (is_successor_set a).
apply (conj_in _ _).
apply H0.
intro n.
intro.
assert (¬(S n ⊆ n)).
intro.
unfold S in H4.
extract_iota (n ∪ {`n}) H4.
pose proof iota_prop n.
right H5.
pose proof H4 n.
cbv beta in H7.
pose proof H1 n.
left H8.
clear H8.
pose proof H9 H3.
right H8.
pose proof H10 n.
cbv beta in H11.
pose proof subset_refl n.
apply H11.
apply H7.
apply H6.
apply (disj_in_2 _ _).
extract_iota_from_goal {`n}.
pose proof iota_prop0 n.
right H13.
apply H14.
apply (eq_refl n).
apply H12.
(* part 2*)
assert (∀ x :: n . ¬ ((S n) ⊆ x)).
intro x.
intro.
intro.
assert (n ⊆ S n).
intro k.
intro.
unfold S.
extract_iota_from_goal (n ∪ {`n}).
pose proof iota_prop k.
right H8.
apply H9.
apply (disj_in_1 _ _).
apply H7.
pose proof subset_trans _ _ _ H7 H6.
pose proof H3.
clear H3. (* new page -- must use x ∈ n to prove a contradiction *)
pose proof H8 x H5.
pose proof H1 n.
left H10.
pose proof H11 H9.
left H12.
right H12.
clear H12 H10.
pose proof H14 x H5.
apply (H10 H8).
assert (∀ x :: (S n) . ¬ ((S n) ⊆ x)). (*last step*)
intro.
intro.
unfold S in H6.
extract_iota (n ∪ {`n}) H6.
pose proof iota_prop x.
left H7.
pose proof H8 H6.
apply (disj_el _ _ _ H9).
intro.
apply (H5 x H10).
intro.
pose proof element_of_unit_set x n H10.
pose proof eq_subs (fun x => ¬ (S n ⊆ x)) _ _ (eq_symm _ _ H11) H4.
apply H12. (*last last step*)
pose proof H1 n.
left H7.
pose proof H8 H3.
left H9.
pose proof n_is_successor_set.
right H11.
pose proof H12 n H10.
pose proof H1 (S n).
right H14.
apply H15.
apply (conj_in _ _).
apply H13.
apply H6.
extract_iota N H2.
right iota_prop.
pose proof H4 a.
pose proof H5 H3 g H2.
apply H6.
intro x.
intro.
pose proof eq_symm _ _ H2.
pose proof (eq_subs (fun g=> x ∈ g)) _ _ H4 H3.
pose proof H1 x.
left H6.
pose proof H7 H5.
right H8.
apply H9.
Defined.

Definition complete (a: Set) := ∀x::a. x ⊆ a.

Definition every_natural_number_is_complete: ∀n::N. complete n.
apply (PN5_induction (fun n => complete n)).
intro x.
intro.
unfold zero in H.
extract_iota ∅ H.
pose proof iota_prop x.
pose proof H0 H.
apply (abs_el _ H1).
intro.
intro.
intro.
intro y.
intro.
unfold complete in H0.
pose proof H0 y.
cbv beta in H2.
unfold S.
unfold S in H1.
extract_iota (x ∪ {`x}) H1.
pose proof iota_prop y.
cbv beta in H3.
left H3.
pose proof H4 H1.
intro z.
intro.
extract_iota_from_goal (x ∪ {`x}).
pose proof iota_prop0 z.
right H7.
apply H8.
apply (disj_el _ _ _ H5).
intro.
pose proof H2 H9.
pose proof H10 z H6.
apply (disj_in_1 _ _ H11).
intro.
pose proof element_of_unit_set y x H9.
repl H10 H6.
apply (disj_in_1 _ _ H11).
Defined.

Definition PN4_injection: ∀m::N. ∀n::N. ((S m) = (S n)) -> (m = n).
intro m.
intro m_nat.
intro n.
intro n_nat.
intro main.
pose proof DN_el (m = n).
apply H.
clear H.
intro.
unfold S in main.
extract_iota (m ∪ {`m}) main.
extract_iota ((n ∪ {`n})) main.
pose proof iota_prop0 m.
left H0.
cbv beta in H1.
pose proof iota_prop m.
cbv beta in H2.
right H2.
assert ((m ∈ m ∨ m ∈ {`m})).
apply (disj_in_2 _ _).
apply (every_set_is_in_unit_set m).
pose proof H3 H4.
repl main H5.
pose proof H1 H6.
assert (¬(m ∈ {`n})).
intro.
pose proof element_of_unit_set m n H8.
apply (H H9).
pose proof disj_el_alt_2 _ _ H7 H8.
pose proof iota_prop n.
left H10.
cbv beta in H11.
pose proof iota_prop0 n.
right H12.
cbv beta in H13.
pose proof every_set_is_in_unit_set n.
cbv beta in H14.
pose proof disj_in_2 (n ∈ n) _ H14.
pose proof H13 H15.
repl main H16.
pose proof H11 H17.
assert (¬(n ∈ {`m})).
intro.
pose proof element_of_unit_set n m H19.
pose proof eq_symm _ _ H20.
apply (H H21).
pose proof disj_el_alt_2 _ _ H18 H19.
pose proof every_natural_number_is_complete n n_nat m H9 n H20.
pose proof subset_refl n.
pose proof no_nat_is_subset_of_any_its_elements n n_nat n H21.
apply (H23 H22).
Defined.

Definition relation_on_cp (f: Set) (X Y: Set) := f ⊆ (X × Y).

Definition is_function (f: Set) (X Y: Set) := 
(relation_on_cp f X Y) ∧ 
(∀ x :: X. ∃ y :: Y. (⟨x,y⟩ ∈ f)) ∧ 
(∀ x. ∀ y. ∀ z. (⟨x,y⟩ ∈ f) -> (⟨x,z⟩ ∈ f) -> (y = z)).

Definition f_appl_ex (f: Set) (X Y: Set) (H: is_function f X Y) (x: Set) 
(x_in_X: x ∈ X):
 ∃1y. (y ∈ Y) ∧ (⟨x,y⟩ ∈ f).
apply (conj_in _ _).
left H.
refine (_: ∃ y. (y ∈ Y) ∧ ⟨ x, y ⟩ ∈ f).
right H0.
pose proof H1 x x_in_X.
apply H2.
intro a.
intro b.
intro.
intro.
right H.
pose proof H2 x a b.
apply H3.
right H0.
right H1.
apply H4.
right H1.
apply H4.
Defined.

Definition f_appl (f: Set) (X Y: Set) 
(H: is_function f X Y) (x: Set) (x_in_X: x ∈ X) := 
ι _ (f_appl_ex f X Y H x x_in_X).

Definition f_x_eq_y (f: Set) (x y: Set) := (⟨x, y⟩ ∈ f).

Notation "f [ x ] ≔ y" := (f_x_eq_y f x y)(at level 70).

Definition inc_set_ex: ∃1f. (is_function f N N) ∧ 
(∀x :: N. (f [x] ≔ (S x))).
pose proof cartesian_product_exists N N as NN_ex.
left NN_ex.
destruct_ex H NN.
clear H.
pose proof ZF2_subsets 
(* made it simple a bit *)
(fun g => ∃ a :: N . g = (⟨ a, (S a) ⟩)) NN.
destruct_ex H f.
clear H.
apply (conj_in _ _).
apply (ex_in _ f).
apply (conj_in _ _).
apply (conj_in _ _).
apply (conj_in _ _).
unfold relation.
intro q.
intro.
pose proof H1 q.
left H2.
pose proof H3 H.
right H4.
destruct_ex H5 a.
right H6.
assert (NN = (N × N)).
apply (ZF1_extension).
intro m.
apply (conj_in _ _).
intro.
pose proof H0 m.
left H9.
pose proof H10 H8.
extract_iota_from_goal (N × N).
pose proof iota_prop  m.
right H12.
apply H13.
apply H11.
intro.
pose proof H0 m.
right H9.
apply H10.
extract_iota (N × N) H8.
pose proof iota_prop m.
left H11.
apply H12.
apply H8.
pose proof H0 q.
right H9.
repl H8 H10.
apply H11.
apply (ex_in _ a).
apply (conj_in _ _).
left H6.
apply H12.
apply (ex_in _ (S a)).
apply (conj_in _ _).
left H6.
apply (PN2_succ a H12).
apply H7.
intro x.
intro.
apply (ex_in _ (S x)).
apply (conj_in _ _).
pose proof PN2_succ x H.
apply H2.
pose proof PN2_succ x H.
pose proof H1 (⟨ x, S x ⟩).
right H3.
apply H4.
apply (conj_in _ _).
pose proof H0 (⟨ x, S x ⟩).
right H5.
apply H6.
apply (ex_in _ x).
apply (conj_in _ _).
apply H.
apply (ex_in _ (S x)).
apply (conj_in _ _).
apply H2.
apply (eq_refl _).
apply (ex_in _ x).
apply (conj_in _ _).
apply H.
apply (eq_refl _).
intros x y z.
intro.
intro.
pose proof H1 (⟨ x, y ⟩).
pose proof H1 (⟨ x, z ⟩).
left H3.
left H4.
pose proof H5 H.
pose proof H6 H2.
right H7.
right H8.
destruct_ex H9 a1.
right H11.
destruct_ex H10 a2.
right H13.
pose proof H12.
pose proof pair_property H14.
left H16.
pose proof eq_subs (fun a2 => (⟨ x, z ⟩) = (⟨ a2, S a2 ⟩))
_ _ (eq_symm _ _ H17) H14.
cbv beta in H18.
pose proof pair_property H15.
left H19.
pose proof eq_subs (fun a2 => (⟨ x, y ⟩) = (⟨ a2, S a2 ⟩))
_ _ (eq_symm _ _ H20) H15.
cbv beta in H21.
pose proof eq_trans _ _ _ H18 (eq_symm _ _ H21).
pose proof pair_property H22.
right H23.
apply (eq_symm _ _ H24).
intro x.
intro.
unfold f_x_eq_y.
pose proof H1 (⟨ x, S x ⟩).
right H2.
apply H3.
apply (conj_in _ _).
pose proof H0 (⟨ x, S x ⟩).
right H4.
apply H5.
pose proof PN2_succ x H.
apply (ex_in _ x).
apply (conj_in _ _).
apply H.
apply (ex_in _ (S x)).
apply (conj_in _ _).
apply H6.
apply (eq_refl _).
apply (ex_in _ x).
apply (conj_in _ _).
apply H.
apply (eq_refl _).
intro a.
intro b.
intro.
intro.
unfold f_x_eq_y in H.
unfold f_x_eq_y in H2.
assert (a = f).
apply (ZF1_extension).
intro k.
apply (conj_in _ _). 
intro.
pose proof H1 k.
right H4.
apply H5.
apply (conj_in _ _).
pose proof H0 k.
right H6.
apply H7.
left H.
left H8.
left H9.
pose proof H10 k H3.
extract_iota (N × N) H11.
pose proof  iota_prop k.
left H12.
apply (H13 H11).
right H.
left H.
left H7.
left H8.
pose proof H9 k H3.
extract_iota (N × N) H10.
pose proof iota_prop k.
left H11.
pose proof H12 H10.
destruct_ex H13 x.
left H14.
right H14.
destruct_ex H16 y.
left H17.
right H17.
apply (ex_in _ x).
apply (conj_in _ _).
apply H15.
repl H19 H3.
right H.
pose proof H21 x H15.
right H7.
pose proof H23  x y (S x) H20 H22.
repl H24 H19.
apply H25.
intro.
pose proof H1 k.
left H4.
pose proof H5 H3.
left H6.
right H6.
clear H6.
pose proof H0 k.
left H6.
pose proof H9 H7.
clear H6 H9 H7.
clear H4 H5 H3.
destruct_ex H8 z.
left H3.
right H3.
clear H3.
apply ((eq_subs (fun k=>k ∈ a)) _ _ (eq_symm _ _ H5)).
right H.
pose proof H3 z H4.
apply H6.
rename H3 into result1.
assert (b = f).
apply (ZF1_extension).
intro k.
apply (conj_in _ _). 
intro.
pose proof H1 k.
right H4.
apply H5.
apply (conj_in _ _).
pose proof H0 k.
right H6.
apply H7.
left H2.
left H8.
left H9.
pose proof H10 k H3.
extract_iota (N × N) H11.
pose proof  iota_prop k.
left H12.
apply (H13 H11).
right H.
left H2.
left H7.
left H8.
pose proof H9 k H3.
extract_iota (N × N) H10.
pose proof iota_prop k.
left H11.
pose proof H12 H10.
destruct_ex H13 x.
left H14.
right H14.
destruct_ex H16 y.
left H17.
right H17.
apply (ex_in _ x).
apply (conj_in _ _).
apply H15.
repl H19 H3.
right H2.
pose proof H21 x H15.
right H7.
pose proof H23  x y (S x) H20 H22.
repl H24 H19.
apply H25.
intro.
pose proof H1 k.
left H4.
pose proof H5 H3.
left H6.
right H6.
clear H6.
pose proof H0 k.
left H6.
pose proof H9 H7.
clear H6 H9 H7.
clear H4 H5 H3.
destruct_ex H8 z.
left H3.
right H3.
clear H3.
apply ((eq_subs (fun k=>k ∈ b)) _ _ (eq_symm _ _ H5)).
right H2.
pose proof H3 z H4.
apply H6.
pose proof eq_trans _ _ _ result1 (eq_symm _ _ H3).
apply H4.
Defined.

Definition inc_set := ι _ (inc_set_ex).

Definition inc_set_is_function: (is_function inc_set N N).
extract_iota_from_goal (inc_set).
left iota_prop.
apply H.
Defined.

Definition inc (x: Set) (x_in_N: x ∈ N) := 
ι _ (f_appl_ex (inc_set) N N (inc_set_is_function) x x_in_N).

Definition inc_ex_alt_simple (x: Set) (x_in_N: x ∈ N): ∃1y. y = S (x).
apply (conj_in _ _).
pose proof inc_set_ex.
left H.
clear H.
rename H0 into H.
destruct_ex H f.
left H0.
right H0.
clear H0.
refine (_: ∃ y. y = S x).
pose proof f_appl_ex f N N H1 x x_in_N.
left H0.
destruct_ex H3 y.
right H4.
apply (ex_in _ y).
unfold f_x_eq_y in H2.
pose proof H2 x x_in_N.
right H1.
pose proof H7 x y (S x).
cbv beta in H8.
apply H8.
apply H5.
apply H6.
intro a.
intro b.
intro.
intro.
pose proof (eq_trans _ _ _ H (eq_symm _ _ H0)).
apply H1.
Defined.

Definition inc_ex_alt_super_simple (x: Set) (x_in_N: x ∈ N): ∃1y. y = S (x).
apply (conj_in _ _).
apply (ex_in _ (S x)).
apply (eq_refl _).
intro a.
intro b.
intro.
intro.
apply (eq_trans _ _ _ H (eq_symm _ _ H0)).
Defined.

Definition inc_alt (x: Set) (x_in_N: x ∈ N):= ι _ (inc_ex_alt_super_simple x x_in_N).

Definition zero_in_N : 0 ∈ N := PN1_empty_set.

Ltac apply_succ_recursively H n :=
match eval cbn delta in n with
| 1 => do 1 apply PN2_succ in H
| 2 => do 2 apply PN2_succ in H
| 3 => do 3 apply PN2_succ in H
| 4 => do 4 apply PN2_succ in H
| 5 => do 5 apply PN2_succ in H
| 0 => idtac 
end.

(* to get something like "7 ∈ N" fast *)
Ltac prove_natural_number_in_N n :=
pose proof PN1_empty_set as H;
apply_succ_recursively H n; 
change (n ∈ N) in H.

Definition one_in_N : 1 ∈ N.
prove_natural_number_in_N 1.
apply H.
Defined.

Definition two_in_N : 2 ∈ N.
prove_natural_number_in_N 2.
apply H.
Defined.

Definition three_in_N : 3 ∈ N.
prove_natural_number_in_N 3.
apply H.
Defined.

Definition four_in_N : 4 ∈ N.
prove_natural_number_in_N 4.
apply H.
Defined.

Definition five_in_N : 5 ∈ N.
prove_natural_number_in_N 5.
apply H.
Defined.

Definition inc_one_eq_two: (inc 1 one_in_N) = 2.
extract_iota_from_goal (inc 1 one_in_N).
right iota_prop.
extract_iota inc_set H.
right iota_prop0.
unfold f_x_eq_y in H0.
pose proof one_in_N.
pose proof H0 1 H1.
left iota_prop0.
right H3.
pose proof H4 1 s (S 1) H H2.
unfold two.
apply H5.
Defined.

Ltac set_el_1 H x L :=
let h_el := fresh H in
let applied_H := fresh "applied_H" in
let left_H := fresh "left_H" in
match type of H with
| ∀ x . (_ ⇔ _) => 
pose proof H x as applied_H;
pose proof conj_el_1 _ _ applied_H as left_H;
pose proof left_H L as h_el;
clear applied_H left_H
| _ => fail "First argument is not in form ∀ x . (_ ⇔ _)"
end.

Ltac set_el_2 H x R :=
let h_el := fresh H in
let applied_H := fresh "applied_H" in
let right_H := fresh "right_H" in
match type of H with
| ∀ x . (_ ⇔ _) => 
pose proof H x as applied_H;
pose proof conj_el_2 _ _ applied_H as right_H;
pose proof right_H R as h_el;
clear applied_H right_H
| _ => fail "First argument is not in form ∀ x . (_ ⇔ _)"
end.

Ltac set_left H x :=
let biimpl_with_x := fresh "biimpl_with_x" in
let left_part := fresh H in
pose proof H x as biimpl_with_x;
pose proof conj_el_1 _ _ biimpl_with_x as left_part;
clear biimpl_with_x.

Ltac set_right H x :=
let biimpl_with_x := fresh "biimpl_with_x" in
let right_part := fresh H in
pose proof H x as biimpl_with_x;
pose proof conj_el_2 _ _ biimpl_with_x as right_part;
clear biimpl_with_x.

Definition non_empty_subsets_of (a: Set) := { x ε (𝒫 a) | (¬(x = ∅)) }.

Definition in_non_empty_subsets_of_union(w x: Set) (not_empty: ¬ (w = ∅)):
w ∈ x -> w ∈ non_empty_subsets_of (union x).
intro.
unfold non_empty_subsets_of.
extract_iota_from_goal ({x0 ε 𝒫 union x | ¬ (x0 = ∅)}).
pose proof iota_prop w.
right H0.
apply H1.
apply (conj_in _ _).
extract_iota_from_goal (𝒫 union x).
pose proof iota_prop0 w.
right H2.
apply H3.
extract_iota_from_goal (union x).
intro z.
intro.
pose proof iota_prop1 z.
right H5.
apply H6.
apply (ex_in _ w).
apply (conj_in _ _).
apply H4.
apply H.
apply not_empty.
Defined.

(* They say that "Formally, ZFC is a one-sorted theory in first-order logic."
Howerver, in this version of axiom from a textbook, they definitely pass proofs of "is_function" and "b_in_domain".
Without these proofs, the f(x) application will not exists because iota denotes existance.
Maybe math people do this in mind when they see the context and maybe it is possible to improve
the theorem prover to see the context of expression and "catch" all the proofs needed implicitly.
Anyway, the PAT-notation when I pass proof objects is clear enough and compatible with CoC
*)

Axiom ZF7_choice: ∀a. ∃f. @ex (is_function f (non_empty_subsets_of a) 
a) (fun f_is_func =>
∀b. @all (b ∈ (non_empty_subsets_of a)) ( fun b_in_domain => 
(f_appl f (non_empty_subsets_of a) a f_is_func b b_in_domain) ∈ b)).

Definition choice_simplified: ∀x. (¬(∅ ∈ x)) -> ∃f. @ex (is_function f x (union x)) 
(fun f_is_func => (∀a. @all (a ∈ x) 
(fun a_in_x => (f_appl f x (union x) f_is_func a a_in_x) ∈ a))).
intro x.
intro no_empty_set_in_x.
pose proof ZF7_choice (union x).
cbv beta in H.
destruct_ex H f.
destruct_ex H0 f_is_func.
clear H H0.
pose proof ZF2_subsets (fun p => (∀c. ∀d. (⟨c,d⟩ = p) -> c ∈ x)) f.
cbv beta in H.
destruct_ex H g.
clear H.
assert (g ⊆ f) as g_subset_of_f.
intro z.
intro.
pose proof H0 z.
left H2.
pose proof H3 H.
left H4.
apply H5.
apply (ex_in _ g).
assert (is_function g x (union x)).
apply (conj_in _ _).
apply (conj_in _ _).
unfold relation_on_cp.
left f_is_func.
left H.
unfold relation_on_cp in H2.
intro w.
intro.
set_el_1 H0 w H3.
left H4.
left f_is_func.
left H6.
clear H6.
unfold relation_on_cp in H7.
pose proof H7 w H5.
extract_iota_from_goal (x × union x).
pose proof iota_prop w.
right H8.
apply H9.
clear H8 H9.
extract_iota (non_empty_subsets_of (union x) × union x) H6.
pose proof iota_prop0 w.
left H8.
pose proof H9 H6.
cbv beta in H10.
clear H8 H9.
destruct_ex H10 a.
left H8.
right H8.
clear H8.
destruct_ex H11 b.
left H8.
right H8.
clear H8.
right H4.
pose proof H8 a b.
cbv beta in H14.
pose proof eq_symm _ _ H13.
pose proof H14 H15.
apply (ex_in _ a).
apply (conj_in _ _).
apply H16.
apply (ex_in _ b).
apply (conj_in _ _).
apply H12.
apply H13.
intro a.
intro.
left f_is_func .
right H2.
clear H2.
pose proof H3 a.
cbv beta in H2.
assert (¬ (a = ∅)).
intro.
repl H4 H.
apply no_empty_set_in_x.
apply H5.
pose proof in_non_empty_subsets_of_union a x H4 H.
pose proof H2 H5.
destruct_ex H6 y.
apply (ex_in _ y).
apply (conj_in _ _).
left H7.
apply H8.
right H7.
pose proof H0 (⟨ a, y ⟩).
right H9.
apply H10.
apply (conj_in _ _).
apply H8.
intro c.
intro d.
intro.
pose proof pair_property H11.
left H12.
repl H13 H.
apply H14.
intros a b c.
intro.
intro.
right f_is_func .
pose proof H3 a b c.
cbv beta in H4.
apply H4.
apply (g_subset_of_f (⟨ a, b ⟩) H).
apply (g_subset_of_f (⟨ a, c ⟩) H2).
apply (ex_in _ H).
intro a.
intro.
extract_iota_from_goal (f_appl g x (union x) H a x0).
assert (a ∈ non_empty_subsets_of (union x)).
pose proof in_non_empty_subsets_of_union a x.
apply H2.
intro.
repl H3 x0.
apply no_empty_set_in_x.
apply x1.
apply x0.
pose proof H1 a H2.
cbv beta in H3.
extract_iota (f_appl f (non_empty_subsets_of (union x)) 
(union x) f_is_func a H2) H3.
right iota_prop.
pose proof g_subset_of_f _ H4.
right iota_prop0.
right f_is_func.
pose proof H7 a s s0 H5 H6.
repl H8 H3.
apply H9.
Defined.

Definition distributivity_backward (A B C: Prop): 
((B ∨ A) ∧ (C ∨ A)) -> (A ∨ (B ∧ C)).
intro.
left H.
right H.
apply (disj_el _ _ _ H0).
intro.
apply (disj_el _ _ _ H1).
intro.
pose proof (conj_in _ _ H2 H3).
apply (disj_in_2 _ _ H4).
intro.
apply (disj_in_1 _ _ H3).
intro.
apply (disj_in_1 _ _ H2).
Defined.

Definition functional_application_works_for_equality_deprecated 
{f X Y: Set} (f_is_func: is_function f X Y) 
(a: Set) (a_in_X: a ∈ X)  
(b: Set) (b_in_X: b ∈ X) (equality: a = b): 
(f_appl f X Y f_is_func a a_in_X) = (f_appl f X Y f_is_func b b_in_X).
extract_iota_from_goal (f_appl f X Y f_is_func a a_in_X).
extract_iota_from_goal (f_appl f X Y f_is_func b b_in_X).
right iota_prop. 
right iota_prop0.
repl equality H0.
right f_is_func.
pose proof H2 a s s0.
apply H3.
apply H.
apply H1.
Defined. 


(* https://en.wikipedia.org/wiki/Diaconescu%27s_theorem *)
Definition diaconescusTheorem:  forall P, P ∨ (¬ P).
pose proof pair_unord_exists 0 1.
left H.
destruct_ex H0 zero_or_one.
clear H H0.
intro P.
pose proof unique_subset_exists (fun x => (x = 0) ∨ P) zero_or_one.
cbv beta in H.
left H.
destruct_ex H0 U.
clear H H0.
rename H1 into zero_or_one_prop.
rename H2 into U_prop.
pose proof unique_subset_exists (fun x => (x = 1) ∨ P) zero_or_one.
left H.
destruct_ex H0 V.
rename H1 into V_prop.
clear H H0.
assert (P -> U = V).
intro p.
assert (U = zero_or_one).
apply (ZF1_extension).
intro x.
apply (conj_in _ _).
intro.
set_el_1 U_prop x H.
left U_prop0.
apply H0.
intro.
assert ((x ∈ zero_or_one ∧ (x = 0 ∨ P))).
apply (conj_in _ _).
apply H.
apply (disj_in_2 _ _ p).
set_el_2 U_prop x H0.
apply U_prop0.
assert (V = zero_or_one).
apply (ZF1_extension).
intro x.
apply (conj_in _ _).
intro.
set_el_1 V_prop x H0.
left V_prop0.
apply H1.
intro.
assert ((x ∈ zero_or_one ∧ (x = 1 ∨ P))).
apply (conj_in _ _).
apply H0.
apply (disj_in_2 _ _ p).
set_el_2 V_prop x H1.
apply V_prop0.
apply (eq_trans _ _ _ H (eq_symm _ _ H0)).
pose proof pair_unord_exists U V.
left H0.
destruct_ex H1 X.
rename H2 into X_prop.
clear H0 H1.
pose proof choice_simplified X.
cbv beta in H0.
assert (¬ (∅ ∈ X)).
intro.
pose proof X_prop ∅.
left H2.
pose proof H3 H1.
apply (disj_el _ _ _ H4).
intro.
extract_iota ∅ H5.
pose proof iota_prop 0.
cbv beta in H6.
repl H5 H6.
assert (0 ∈ zero_or_one).
pose proof zero_or_one_prop 0.
right H8.
apply H9.
apply (disj_in_1 _ _).
apply(eq_refl 0).
pose proof U_prop 0.
right H9.
apply H7.
apply H10.
apply (conj_in _ _).
apply H8.
apply (disj_in_1 _ _).
apply(eq_refl 0).
intro.
extract_iota ∅ H5.
pose proof iota_prop 1.
cbv beta in H6.
repl H5 H6.
assert (1 ∈ zero_or_one).
pose proof zero_or_one_prop 1.
right H8.
apply H9.
apply (disj_in_2 _ _).
apply(eq_refl 1).
pose proof V_prop 1.
right H9.
apply H7.
apply H10.
apply (conj_in _ _).
apply H8.
apply (disj_in_1 _ _).
apply(eq_refl 1).
pose proof H0 H1.
destruct_ex H2 f.
clear H0 H1 H2.
destruct_ex H3 f_is_func.
clear H3.
rename H0 into choice_prop.
pose proof choice_prop U.
assert (U ∈ X).
pose proof X_prop U.
right H1.
apply H2.
apply (disj_in_1 _ _).
apply (eq_refl U).
pose proof H0 H1.
cbv beta in H2.
clear H0.
rename H1 into U_in_x.
rename H2 into f_U_in_U.
assert (V ∈ X).
pose proof X_prop V.
right H0.
apply H1.
apply (disj_in_2 _ _).
apply (eq_refl V).
rename H0 into V_in_x.
pose proof choice_prop V V_in_x.
cbv beta in H0.
rename H0 into f_V_in_V.
refine (let f_V := (f_appl f X (union X) f_is_func V V_in_x) in _).
pose proof f_V_in_V: (f_V ∈ V).
clear f_V_in_V.
rename H0 into f_V_in_V.
refine (let f_U := (f_appl f X (union X) f_is_func U U_in_x) in _).
pose proof f_U_in_U: (f_U ∈ U).
clear f_U_in_U.
rename H0 into f_U_in_U.
pose proof U_prop f_U.
left H0.
pose proof H1 f_U_in_U.
right H2.
pose proof V_prop f_V.
left H4.
pose proof H5 f_V_in_V.
right H6.
clear H0 H1 H2 H4 H5 H6.
pose proof (conj_in _ _ H3 H7).
pose proof distributivity_backward _ _ _ H0.
assert (P ∨ (¬(f_U = f_V))).
apply (disj_el _ _ _ H1).
intro.
apply (disj_in_1 _ _ H2).
intro.
apply (disj_in_2).
intro.
left H2.
right H2.
repl H5 H4.
repl H6 H8.
unfold one in H9.
pose proof PN3_not_zero 0 (PN1_empty_set).
apply (H10 (eq_symm _ _ H9)).
assert (P -> f_U = f_V).
intro.
unfold f_U.
unfold f_V.
pose proof functional_application_works_for_equality_deprecated f_is_func 
U U_in_x V V_in_x (H H4).
apply H5.
pose proof contrapositive H4.
clear H4.
apply (disj_el _ _ _ H2).
intro.
apply (disj_in_1).
apply H4.
intro.
apply (disj_in_2).
apply H5.
apply H4.
Defined.

Definition zero_in_every_natual_number (n:Set) (n_in_N: n ∈ N ): (¬(n = 0)) -> 0 ∈ n.
pose proof PN5_induction (fun k => (¬(k = 0)) -> 0 ∈ k).
cbv beta in H.
assert ((¬ (0 = 0) -> 0 ∈ 0)).
intro.
pose proof (eq_refl 0).
apply (abs_el _ (H0 H1)).
pose proof H H0.
assert ((∀ x :: N
. (¬ (x = 0) -> 0 ∈ x) ->
¬ (S x = 0) -> 0 ∈ S x)).
intro.
intro.
intro.
intro.
unfold S.
extract_iota_from_goal ((x ∪ {`x})).
pose proof iota_prop 0.
right H5.
apply H6.
pose proof exc_thrd ((x = 0)).
apply (disj_el _ _ _ H7).
intro.
apply (disj_in_2).
pose proof every_set_is_in_unit_set x.
cbv beta in H9.
pose proof eq_subs (fun k=>  k ∈ {`x}) _ _ H8 H9.
apply H10.
intro.
pose proof H3 H8.
apply (disj_in_1).
apply H9.
pose proof H1 H2.
pose proof H3 n n_in_N.
apply H4.
Defined.

Definition zero_is_not_in_itself: ¬ (0 ∈ 0).
intro.
unfold zero in H.
extract_iota ∅ H.
apply (abs_el _ (iota_prop s H)).
Defined.

Definition set_in_zero_causes_contradiction {n: Set}: (n ∈ 0) -> ⊥.
intro.
unfold zero in H.
extract_iota ∅ H.
pose proof iota_prop n.
pose proof H0 H.
apply H1.
Defined.

Definition any_set_in_empty_set_causes_contradiction 
{n: Set}: (n ∈ 0) -> ⊥ :=
set_in_zero_causes_contradiction.

Definition unfold_S_into_disj 
{a: Set} {b: Set} 
: (a ∈ S b) -> ((a = b) ∨ (a ∈ b)).
intro.
unfold S in H.
extract_iota ((b ∪ {`b})) H.
pose proof iota_prop a.
left H0.
pose proof H1 H.
cbv beta in H2.
apply (disj_el _ _ _ H2).
intro.
apply (disj_in_2).
apply H3.
intro.
extract_iota {`b} H3.
pose proof iota_prop0 a.
left H4.
pose proof H5 H3.
apply (disj_in_1).
apply H6.
Defined.

Definition any_set_belongs_to_successor (a: Set): a ∈ (S a).
unfold S.
extract_iota_from_goal (a ∪ {`a}).
extract_iota {`a} iota_prop.
pose proof iota_prop a.
right H.
apply H0.
pose proof iota_prop0 a.
right H1.
apply (disj_in_2).
apply H2.
apply (eq_refl a).
Defined.

Definition any_set_is_subset_of_its_successor (a: Set): a ⊆ (S a).
intro m.
intro.
unfold S.
extract_iota_from_goal (a ∪ {`a}).
extract_iota {`a} iota_prop.
pose proof iota_prop m.
right H0.
apply H1.
pose proof iota_prop0 m.
cbv beta in H2.
apply (disj_in_1).
apply H.
Defined.

Definition in_or_equal (a b: Set) := (a ∈ b) ∨ (a = b).

Definition transitive_set_deprecated (A: Set) := ∀x. ∀a. ((x ∈ a) ∧ (a ∈ A)) -> (x ∈ A).

Definition every_natual_number_is_transitive: ∀n::N. transitive_set_deprecated n.
apply (PN5_induction (fun n => transitive_set_deprecated n)).
unfold transitive_set_deprecated.
intro.
intro.
intro.
right H.
pose proof set_in_zero_causes_contradiction H0.
apply (abs_el _ H1).
intro n.
intro.
unfold transitive_set_deprecated.
intro.
intro x.
intro a.
intro.
pose proof H0 x a.
cbv beta in H2.
unfold S.
extract_iota_from_goal (n ∪ {`n}).
extract_iota {`n} iota_prop.
pose proof iota_prop x.
right H3.
apply H4.
pose proof iota_prop0 x.
right H5.
cbv beta in H6.
left H1.
right H1.
pose proof unfold_S_into_disj H8.
apply (disj_el _ _ _ H9).
intro.
repl H10 H7.
apply (disj_in_1).
apply H11.
intro.
apply (disj_in_1).
apply H2.
apply (conj_in _ _).
apply H7.
apply H10.
Defined.



(* Lemma 4L (a) from Enderton's "Elements of set theory" *)
Definition m_in_n_equiv_Sm_in_Sn
(m: Set) (m_is_natual_number: m ∈ N) 
(n: Set) (n_is_natual_number: n ∈ N)
: (m ∈ n) ⇔ ((S m) ∈ (S n)).
apply (conj_in _ _).
intro.
unfold S.
pose proof ZF2_subsets (fun n=> ∀ m::n. (S m) ∈ (S n)) N.
cbv beta in H0.
destruct_ex H0 T.
assert (is_successor_set T).
apply (conj_in _ _).
pose proof H1 ∅ .
right H2.
apply H3.
apply (conj_in _ _).
apply (PN1_empty_set).
intro g.
intro.
extract_iota ∅ H4.
pose proof iota_prop g H4.
apply (abs_el _ H5).
intro k.
intro.
pose proof H1 k.
left H3.
pose proof H4 H2.
left H5.
pose proof PN2_succ k H6.
pose proof H1 (S k).
right H8.
apply H9.
apply (conj_in _ _).
apply H7.
intro m'.
intro.
pose proof unfold_S_into_disj H10.
apply (disj_el _ _ _ H11).
intro.
pose proof eq_subs (fun k=> S m' ∈ S (S k)) _ _ H12.
apply H13.
apply (any_set_belongs_to_successor (S m')).
intro.
cbv beta in H8.
right H5.
pose proof H13 m' H12.
pose proof (any_set_is_subset_of_its_successor (S k)) (S m') H14.
apply H15.
pose proof n_is_subset_of_any_successor_set T H2.
assert (T ⊆ N).
intro t.
intro.
pose proof H1 t.
left H5.
pose proof H6 H4.
left H7.
apply H8.
assert (T = N).
apply (extensionality_for_subsets H4 H3).
repl H5 H1.
pose proof H6 n.
left H7.
pose proof H8 n_is_natual_number.
right H9.
pose proof H10 m H.
apply H11.
intro.
pose proof any_set_belongs_to_successor m.
assert (in_or_equal (S m) n).
unfold in_or_equal.
pose proof unfold_S_into_disj H.
apply disj_comm.
apply H1.
unfold in_or_equal in H1.
apply (disj_el _ _ _ H1).
intro.
pose proof every_natual_number_is_transitive n n_is_natual_number m (S m).
apply H3.
apply (conj_in).
apply H0.
apply H2.
intro.
pose proof any_set_belongs_to_successor m.
pose proof eq_subs (fun k=> m ∈ k) _ _ H2.
apply H4.
apply H3.
Defined.

(* Lemma 4L (b) from Enderton's "Elements of set theory" *)
Definition no_natural_number_is_member_of_itself
(m: Set) (m_is_natual_number: m ∈ N) 
: ¬ (m ∈ m).
apply (PN5_induction (fun m => ¬ (m ∈ m))).
intro.
pose proof set_in_zero_causes_contradiction H.
apply H0.
intro.
intro.
intro.
pose proof m_in_n_equiv_Sm_in_Sn x H x H.
right H1.
pose proof contrapositive H2.
apply H3.
apply H0.
apply m_is_natual_number.
Defined.


Definition belongs_to_set_then_belongs_to_successor (a b: Set): 
(a ∈ b) -> (a ∈ (S b)).
intro.
unfold S.
extract_iota_from_goal (b ∪ {`b}).
extract_iota {`b} iota_prop.
pose proof iota_prop a.
right H0.
apply H1.
apply (disj_in_1).
apply H.
Defined.

Definition trichotomy_for_set_inclusion_only_disj
(m: Set) (m_is_natual_number: m ∈ N) 
(n: Set) (n_is_natual_number: n ∈ N):
(m ∈ n ∨ m = n ∨ n ∈ m).
pose proof PN5_induction (fun n => (m ∈ n ∨ m = n) ∨ n ∈ m).
cbv beta in H.
apply H.
pose proof exc_thrd (m = 0).
apply (disj_el _ _ _ H0).
intro.
apply (disj_in_1).
apply (disj_in_2).
apply H1.
intro.
apply (disj_in_2).
pose proof (zero_in_every_natual_number m m_is_natual_number H1).
apply H2.
intro.
intro.
intro.
apply (disj_el _ _ _ H1).
intro.
apply (disj_el _ _ _ H2).
intro.
rename H3 into case1.
pose proof belongs_to_set_then_belongs_to_successor m x case1.
apply (disj_in_1).
apply (disj_in_1).
apply H3.
intro.
pose proof any_set_belongs_to_successor m.
pose proof eq_subs (fun k => m ∈ S k) _ _ H3 H4.
cbv beta in H5.
apply (disj_in_1).
apply (disj_in_1).
apply H5.
intro.
pose proof m_in_n_equiv_Sm_in_Sn x H0 m m_is_natual_number.
left H3.
pose proof H4 H2.
assert (in_or_equal (S x) m).
unfold in_or_equal.
pose proof unfold_S_into_disj H5.
pose proof disj_comm _ _ H6.
apply H7.
apply (disj_el _ _ _ H6).
intro.
apply (disj_in_2).
apply H7.
intro.
apply (disj_in_1).
apply (disj_in_2).
apply (eq_symm _ _ H7).
apply n_is_natual_number.
Defined.

(* Lemma 4.3 
The authors of "Set Theory and Logic" textbook specified this theorem as 
"easily derivable" from the other two lemmas, but they were WRONG.
It required me to look up another textbook (Enderton's "Elements of set theory")
and add 7 extra lemmas (!!!) in order to make things correct and fit in.
*)
Definition trichotomy_for_set_inclusion 
(m: Set) (m_is_natual_number: m ∈ N) 
(n: Set) (n_is_natual_number: n ∈ N):
((m ∈ n) ⊽ (m = n) ⊽ (n ∈ m)).
apply (disj_exclusive_triple_in).
apply (trichotomy_for_set_inclusion_only_disj m
m_is_natual_number n n_is_natual_number).
apply (conj_in _ _).
apply (conj_in _ _).
intro.
left H.
right H.
repl H1 H0.
pose proof no_natural_number_is_member_of_itself m m_is_natual_number H2.
apply H3.
intro.
left H.
right H.
pose proof every_natural_number_is_complete n n_is_natual_number m H0.
pose proof every_natural_number_is_complete m m_is_natual_number n H1.
pose proof extensionality_for_subsets H2 H3.
repl H4 H0.
pose proof no_natural_number_is_member_of_itself m m_is_natual_number H5.
apply H6.
intro.
left H.
right H.
repl H0 H1.
pose proof no_natural_number_is_member_of_itself m m_is_natual_number H2.
apply H3.
Defined.

Definition subset_of_cartesian_exists (A B: Set)(P: Set -> Prop): 
∃1 c. ∀ w . w ∈ c ⇔ ((∃ x :: A . ∃ y :: B . (w = (⟨ x, y ⟩))) ∧ (P w)).
apply conj_in.
pose proof cartesian_product_exists A B.
left H.
destruct_ex H0 cartesian.
pose proof ZF2_subsets (fun w => P w) cartesian.
cbv beta in H2.
destruct_ex H2 subset_of_cartesian.
clear H H0 H2.
apply (ex_in _ subset_of_cartesian).
intro w.
apply conj_in.
intro.
apply conj_in.
pose proof H1 w.
left H0.
pose proof H3 w.
left H4.
pose proof H5 H.
left H6.
pose proof H2 H7.
apply H8.
pose proof H3 w.
left H0.
pose proof H2 H.
right H4.
apply H5.
intro.
pose proof H3 w.
right H0.
apply H2.
apply conj_in.
pose proof H1 w.
right H4.
apply H5.
left H.
apply H6.
right H.
apply H4.
pose proof any_biimpl_set_is_no_more_than_one 
(fun w=> ((∃ x0 :: A . ∃ y :: B . w = (⟨ x0, y ⟩)) ∧ P w)).
apply H.
Defined.


Definition subset_of_cartesian5_for_2_args_exists (X Y A B C: Set)(P: Set -> Prop): 
∃1 c. ∀ w . w ∈ c ⇔ ((∃ x :: X . ∃ y :: Y . ∃ a :: A . 
∃ b :: B . ∃ c :: C . (w = (⟨⟨ x, y ⟩, ⟨ a, b, c ⟩⟩))) ∧ (P w)).
apply conj_in.
pose proof cartesian_product_exists X Y as x_y_exists.
left x_y_exists.
destruct_ex H x_y.
rename H0 into x_y_prop. 
pose proof cartesian_product_exists A B as a_b_exists.
left a_b_exists.
destruct_ex H0 a_b.
rename H1 into a_b_prop.
pose proof cartesian_product_exists a_b C as a_b_c_exists.
left a_b_c_exists.
destruct_ex H1 a_b_c.
rename H2 into a_b_c_prop.
pose proof cartesian_product_exists x_y a_b_c as x_y_a_b_c_exists.
left x_y_a_b_c_exists.
destruct_ex H2 x_y_a_b_c.
rename H3 into x_y_a_b_c_prop.
clear x_y_exists x_y_a_b_c_exists H a_b_exists H0 
a_b_c_exists H1 x_y_a_b_c_exists H2.
2: apply any_biimpl_set_is_no_more_than_one.
pose proof ZF2_subsets (fun w => P w) x_y_a_b_c as subset_exists.
cbv beta in subset_exists.
destruct_ex subset_exists x_y_a_b_c_subset.
clear subset_exists.
rename H into subset_prop.
apply (ex_in _ x_y_a_b_c_subset).
intro w.
apply conj_in.
intro.
set_el_1 subset_prop w H.
left subset_prop0.
right subset_prop0.
set_el_1 x_y_a_b_c_prop w H0.
destruct_ex x_y_a_b_c_prop0 x_y_el.
conj_el H2.
clear H2.
set_el_1 x_y_prop x_y_el H3.
destruct_ex x_y_prop0 x.
conj_el H2.
clear H2.
destruct_ex H6 y.
conj_el H2.
clear H2.
clear H6.
destruct_ex H4 a_b_c_el.
conj_el H2.
clear H2.
set_el_1 a_b_c_prop a_b_c_el H6.
destruct_ex a_b_c_prop0 a_b_el.
conj_el H2.
clear H2.
set_el_1 a_b_prop a_b_el H10.
destruct_ex a_b_prop0 a.
conj_el H2.
clear H2.
destruct_ex H13 b.
conj_el H2.
clear H2.
destruct_ex H11 c.
conj_el H2.
clear H2.
repl H15 H17.
repl H2 H9.
repl H8 H18.
pose proof H1.
apply (conj_in).
apply (ex_in _ x).
apply (conj_in).
apply H5.
apply (ex_in _ y).
apply (conj_in).
apply H7.
apply (ex_in _ a).
apply (conj_in).
apply H12.
apply (ex_in _ b).
apply (conj_in).
apply H14.
apply (ex_in _ c).
apply (conj_in).
apply H16.
apply H19.
apply H20.
intro.
conj_el H.
clear H.
destruct_ex H0 x.
conj_el H.
destruct_ex H3 y.
conj_el H4.
destruct_ex H6 a.
conj_el H7.
destruct_ex H9 b.
conj_el H10.
destruct_ex H12 c.
conj_el H13.
set_right subset_prop w.
apply subset_prop0.
apply (conj_in).
set_right x_y_a_b_c_prop w.
apply x_y_a_b_c_prop0.
apply (ex_in _ (⟨ x, y ⟩)).
apply (conj_in).
set_right x_y_prop (⟨ x, y ⟩).
apply x_y_prop0.
apply (ex_in _ x).
apply (conj_in).
apply H2.
apply (ex_in _ y).
apply (conj_in).
apply H5.
apply eq_refl.
apply (ex_in _ (⟨ a, b, c ⟩)).
apply (conj_in).
set_right a_b_c_prop (⟨ a, b, c ⟩).
apply a_b_c_prop0.
apply (ex_in _ (⟨ a, b⟩)).
apply (conj_in).
set_right a_b_prop (⟨ a, b⟩).
apply a_b_prop0.
apply (ex_in _ a).
apply (conj_in).
apply H8.
apply (ex_in _ b).
apply (conj_in).
apply H11.
apply eq_refl.
apply (ex_in _ c).
apply (conj_in).
apply H14.
apply (eq_refl).
right H13.
apply H16.
apply H1.
Defined.


Definition zero_not_equals_to_two: ¬ (0 = 2).
intro.
unfold zero in H.
pose proof extension_backwards H.
set_right H0 1.
extract_iota ∅ H1.
pose proof iota_prop 1.
apply H2.
apply H1.
unfold two.
unfold S.
extract_iota_from_goal (1 ∪ {`1}).
set_right iota_prop0 1.
apply iota_prop1.
apply (disj_in_2).
apply every_set_is_in_unit_set.
Defined.


Definition divide_n_into_pieces(x: Set) (x_in_N : x ∈ N): 
(x = 0) ∨ (x = 1) ∨ (x = 2) ∨ (2 < x).
unfold lt.
pose proof trichotomy_for_set_inclusion x x_in_N 2 two_in_N.
left H.
left H0.
left H1.
apply (disj_el _ _ _ H2).
intro.
apply (disj_el _ _ _ H3).
intro.
unfold two in H4.
unfold S in H4.
extract_iota ((1 ∪ {`1})) H4.
pose proof iota_prop x.
left H5.
pose proof H6 H4.
apply (disj_el _ _ _ H7).
intro.
unfold one in H8.
unfold S in H8.
extract_iota ((0 ∪ {`0})) H8.
pose proof iota_prop0 x.
left H9.
pose proof H10 H8.
apply (disj_el _ _ _ H11).
intro.
pose proof set_in_zero_causes_contradiction H12.
apply H13.
intro.
pose proof element_of_unit_set x 0 H12.
apply disj_in_1. apply disj_in_1. apply disj_in_1.
apply H13.
intro.
pose proof element_of_unit_set x 1 H8.
apply disj_in_1. apply disj_in_1. apply disj_in_2.
apply H9.
intro.
apply disj_in_1. apply disj_in_2.
apply H4.
intro.
apply disj_in_2.
apply H3.
Defined.

Definition two_lt_three: 2 < 3.
unfold two.
unfold three.
unfold two.
unfold S.
unfold lt.
extract_iota_from_goal ((1 ∪ {`1} ∪ {`1 ∪ {`1}})).
pose proof iota_prop (1 ∪ {`1}).
right H.
apply H0.
apply disj_in_2.
refine (_: (1 ∪ {`1}) ∈ {`  (1 ∪ {`1})}).
extract_iota_from_goal ({`1 ∪ {`1}}).
pose proof iota_prop0 (1 ∪ {`1}).
right H1.
apply H2.
apply eq_refl.
Defined.

(* Simple arithmetic equalities and inequalities*)
Definition zero_not_equal_to_two: ¬ (0 = 2).
intro. 
unfold zero in H.
unfold two in H.
unfold S in H.
extract_iota ∅ H.
extract_iota (1 ∪ {`1}) H.
set_right iota_prop0 1.
repl H iota_prop.
pose proof iota_prop2 1.
apply H0.
apply iota_prop1.
pose proof every_set_is_in_unit_set 1.
apply (disj_in_2).
apply H1.
Defined.

Definition zero_not_equals_to_one: ¬ (0 = 1).
intro. 
unfold zero in H.
unfold one in H.
unfold S in H.
extract_iota ∅ H.
extract_iota (0 ∪ {`0}) H.
set_right iota_prop0 0.
repl H iota_prop.
pose proof iota_prop2 0.
apply H0.
apply iota_prop1.
pose proof every_set_is_in_unit_set 0.
apply (disj_in_2).
apply H1.
Defined.

Definition one_not_equals_to_two: ¬ (1 = 2).
intro.
unfold two in H.
pose proof PN4_injection 0 zero_in_N 1 one_in_N.
pose proof zero_not_equals_to_one.
apply H1.
apply H0.
apply H.
Qed.

Definition three_not_equals_to_two: ¬ (2 = 3).
intro.
pose proof PN4_injection 1 one_in_N 2 two_in_N H.
apply one_not_equals_to_two.
apply H0.
Defined.


Definition three_not_equals_to_one: ¬ (3 = 1).
intro.
unfold two in H.
pose proof PN4_injection 2 two_in_N 0 zero_in_N.
pose proof H0 H.
pose proof extension_backwards H1 0.
simpl in H2.
left H2.
unfold zero in H3.
pose proof (@any_set_in_empty_set_causes_contradiction ∅).
apply H4.
apply H3.
pose proof any_set_belongs_to_successor 0.
pose proof any_set_belongs_to_successor 1.
fold one in H5.
fold two in H6.
pose proof any_set_is_subset_of_its_successor 1.
fold two in H7.
pose proof H7 0.
apply H8.
apply H5.
Defined.

Definition two_is_not_lt_than_zero: ¬ (2 < 0).
unfold lt.
intro.
unfold zero.
pose proof any_set_in_empty_set_causes_contradiction H.
apply H0.
Defined.

Definition two_is_not_lt_than_one: ¬ (2 < 1).
unfold lt.
intro.
pose proof only_zero_is_less_than_one 2 two_in_N H.
pose proof eq_symm _ _ H0.
apply (zero_not_equal_to_two H1).
Defined.

Definition two_is_not_lt_than_two: ¬ (2 < 2).
unfold lt.
intro.
pose proof no_natural_number_is_member_of_itself 2 two_in_N.
apply H0.
apply H.
Defined.


Definition one_is_not_lt_than_zero: ¬ (1 < 0).
unfold lt.
intro.
unfold zero.
pose proof any_set_in_empty_set_causes_contradiction H.
apply H0.
Defined.

(* Function Theory*)

(* Will result in sequence a b c blank blank blank ...*)
Definition piecewise_function_nat_3_elements_exists (a b c blank: Set) (range: Set)
(a_in_range: a ∈ range) (b_in_range: b ∈ range)
(c_in_range: c ∈ range) (blank_in_range: blank ∈ range):
∃1f. (∀x. ((x ∈ f) ⇔
((x = ⟨0, a⟩) ∨ (x = ⟨1, b⟩) ∨ (x = ⟨2, c⟩) ∨
(∃n. (n ∈ N) ∧ (2 < n) ∧ (x = ⟨n, blank⟩))))).
pose proof subset_of_cartesian_exists N range (fun x => 
(x = (⟨ 0, a ⟩) ∨ x = (⟨ 1, b ⟩)) ∨ x = (⟨ 2, c ⟩)
 ∨ (∃n. (n ∈ N) ∧ (2 < n) ∧ (x = ⟨n, blank⟩))).
cbv beta in H.
apply conj_in.
left H.
destruct_ex H0 subset_of_cartesian.
clear H H0.
apply (ex_in _ subset_of_cartesian).
intro w.
apply conj_in.
intro.
set_left H1 w.
pose proof H0 H.
right H2.
apply H3.
intro.
set_right H1 w.
apply H0.
apply conj_in.
destruct_4_disj H.
apply (pair_obviously_exists w 0 a d_1 PN1_empty_set a_in_range).
apply (pair_obviously_exists w 1 b d_2 one_in_N b_in_range).
apply (pair_obviously_exists w 2 c d_3 two_in_N c_in_range).
destruct_ex d_4 n.
right H.
left H.
left H3.
right H3.
apply (pair_obviously_exists w n blank H2 H4 blank_in_range).
apply H.
apply (any_biimpl_set_is_no_more_than_one).
Defined.

Definition piecewise_function_nat_3_elements (a b c blank: Set)
(range: Set)
(a_in_range: a ∈ range) (b_in_range: b ∈ range)
(c_in_range: c ∈ range) (blank_in_range: blank ∈ range):=
ι _ (piecewise_function_nat_3_elements_exists a b c blank range
a_in_range b_in_range c_in_range blank_in_range).

Definition piecewise_function_sanity_check: 
⟨3, 0⟩ ∈ (piecewise_function_nat_3_elements 1 1 1 0 N
one_in_N one_in_N one_in_N PN1_empty_set).
extract_iota_from_goal (piecewise_function_nat_3_elements 1 1 1 0 N one_in_N one_in_N
one_in_N PN1_empty_set).
pose proof iota_prop (⟨3, 0⟩).
right H.
apply H0.
apply (disj_in_2).
apply (ex_in _ 3).
apply conj_in.
apply conj_in.
apply three_in_N.
apply two_lt_three.
apply eq_refl.
Defined.

Definition pairs_not_equal_if_pr1_is_not (a b c d: Set) (NE: ¬ (a = b)):
(¬ (⟨ a, c ⟩ = ⟨ b, d ⟩)).
intro.
pose proof pair_property H.
left H0.
apply (NE H1).
Defined.

Definition pr1_not_equal_in_pairs_leads_to_contradiction {a b c d: Set}
(P: ⟨ a, c ⟩ = ⟨ b, d ⟩) (NE: ¬ (a = b)): ⊥.
pose proof pairs_not_equal_if_pr1_is_not a b c d NE.
apply (H P).
Defined.

Definition piecewise_function_nat_3_elements_is_function (a b c blank: Set)
(range: Set)
(a_in_range: a ∈ range) (b_in_range: b ∈ range)
(c_in_range: c ∈ range) (blank_in_range: blank ∈ range):
(is_function (
  piecewise_function_nat_3_elements a b c blank range 
a_in_range b_in_range c_in_range blank_in_range
) N range).
extract_iota_from_goal (piecewise_function_nat_3_elements a b c blank range a_in_range
b_in_range c_in_range blank_in_range).
rename s into f.
rename iota_prop into H1.
apply conj_in.
apply conj_in.
unfold relation_on_cp.
intro z.
intro.
extract_iota_from_goal (N × range).
pose proof iota_prop z.
right H0.
apply H2.
pose proof H1 z.
left H3.
pose proof H4 H.
pose proof H1 z.
left H6.
pose proof H7 H.
destruct_4_disj H8.
apply (pair_obviously_exists z 0 a d_1 PN1_empty_set a_in_range).
apply (pair_obviously_exists z 1 b d_2 one_in_N b_in_range).
apply (pair_obviously_exists z 2 c d_3 two_in_N c_in_range).
destruct_ex d_4 n.
left H8.
left H9.
right H9.
right H8.
apply (pair_obviously_exists z n blank H12 H10 blank_in_range).
intro.
intro x_in_N.
pose proof divide_n_into_pieces x x_in_N.
destruct_4_disj H.
set_right H1 (⟨ x, a ⟩).
apply (ex_in _ a).
apply conj_in.
apply a_in_range.
apply H0.
apply (disj_in_1).
apply (disj_in_1).
apply (disj_in_1).
pose proof eq_subs (fun g => (⟨ g, a ⟩) = (⟨ 0, a ⟩)) _ _ 
(eq_symm _ _ d_1).
apply H.
apply (eq_refl).
repl_in_goal d_2.
apply (ex_in _ b).
apply conj_in.
apply b_in_range.
set_right H1 (⟨ 1, b ⟩).
apply H0.
apply (disj_in_1).
apply (disj_in_1).
apply (disj_in_2).
apply eq_refl.
apply (ex_in _ c).
apply conj_in.
apply c_in_range.
repl_in_goal d_3.
set_right H1 (⟨ 2, c ⟩ ).
apply H0.
apply (disj_in_1).
apply (disj_in_2).
apply eq_refl.
apply (ex_in _ blank ).
apply conj_in.
apply blank_in_range.
set_right H1 (⟨ x, blank ⟩).
apply H0.
apply (disj_in_2).
apply (ex_in _ x).
apply conj_in.
apply conj_in.
apply x_in_N.
apply d_4.
apply eq_refl.
intros x y z.
intro.
intro.
set_left H1 (⟨ x, y ⟩).
pose proof H2 H.
clear H2.
destruct_4_disj H3.
pose proof pair_property d_1.
right H2.
repl H3 H.
left H2.
repl H5 H0.
repl H5 H.
repl_in_goal H3.
repl H3 H7.
clear H7.
set_left H1 (⟨ 0, z ⟩).
pose proof H7 H6.
destruct_4_disj H9.
pose proof pair_property d_0.
right H9.
pose proof eq_symm _ _ H10.
apply H11.
pose proof pair_property d_2.
left H9.
pose proof PN3_not_zero 0 zero_in_N (eq_symm _ _ H10).
apply H11.
pose proof pair_property d_3.
left H9.
apply (zero_not_equal_to_two H10).
pose proof H7 H6.
assert (¬((∃ n. (n ∈ N ∧ 2 < n)
∧ (⟨ 0, z ⟩) = (⟨ n, blank ⟩)))).
intro.
destruct_ex H10 n.
left H11.
right H11.
right H12.
assert (¬(0 = n)).
intro.
repl H15 H14.
unfold lt in H16.
unfold zero in H16.
extract_iota ∅ H16.
pose proof iota_prop 2.
pose proof H17 H16.
apply H18.
apply (pr1_not_equal_in_pairs_leads_to_contradiction H13 H15).
pose proof eliminate_disjunct_if_leads_to_contradiction_2 H9 H10.
pose proof zero_not_equals_to_two.
pose proof pairs_not_equal_if_pr1_is_not 0 2 z c H12.
pose proof eliminate_disjunct_if_leads_to_contradiction_2 H11 H13.
pose proof zero_not_equals_to_one.
pose proof pairs_not_equal_if_pr1_is_not 0 1 z b H15.
pose proof eliminate_disjunct_if_leads_to_contradiction_2 H14 H16.
pose proof pair_property H17.
right H18.
pose proof eq_symm _ _ H19.
apply H20.
pose proof pair_property d_2.
left H2.
right H2.
repl H3 H.
repl H3 H0.
set_left H1 (⟨ 1, z ⟩).
pose proof H7 H6.
destruct_4_disj H8.
pose proof zero_not_equals_to_one.
pose proof eq_symm _ _ d_1.
apply (pr1_not_equal_in_pairs_leads_to_contradiction H9 H8).
pose proof pair_property d_0.
right H8.
repl H4 H9.
apply (eq_symm _ _ H10).
pose proof one_not_equals_to_two.
apply (pr1_not_equal_in_pairs_leads_to_contradiction d_3 H8).
destruct_ex d_4 n.
left H8.
right H8.
left H9.
right H9.
unfold lt in H12.
assert (¬(1 = n)).
intro.
pose proof extension_backwards H13.
set_right H14 2.
pose proof H15 H12.
apply (two_is_not_lt_than_one H16).
apply (pr1_not_equal_in_pairs_leads_to_contradiction H10 H13).
pose proof pair_property d_3.
left H2.
right H2.
repl H3 H.
repl H3 H0.
repl_in_goal H4.
set_left H1 (⟨ 2, z ⟩).
pose proof H7 H6.
destruct_4_disj H8.
pose proof pair_property d_1.
left H8.
pose proof eq_symm _ _ H9.
apply (zero_not_equal_to_two H10).
pose proof (eq_symm _ _ d_2).
pose proof one_not_equals_to_two.
apply (pr1_not_equal_in_pairs_leads_to_contradiction H8 H9).
pose proof pair_property d_0.
right H8.
pose proof (eq_symm _ _ H9).
apply H10.
destruct_ex d_4 n.
left H8.
right H8.
left H9.
right H9.
pose proof pair_property H10.
left H13.
repl H14 H12.
unfold lt in H15.
pose proof no_natural_number_is_member_of_itself 2 two_in_N.
apply (H16 H15).
destruct_ex d_4 n.
left H2.
right H2.
pose proof pair_property H4.
left H5.
right H5.
repl H6 H.
repl H6 H0.
set_left H1 (⟨ n, z ⟩).
pose proof H10 H9.
destruct_4_disj H11.
assert (¬(n = 0)).
intro.
right H3.
repl H11 H12.
pose proof set_in_zero_causes_contradiction H13.
apply H14.
apply (pr1_not_equal_in_pairs_leads_to_contradiction d_1 H11).
pose proof pair_property d_2.
left H11.
right H3.
repl H12 H13.
pose proof two_is_not_lt_than_one.
apply (H15 H14).
pose proof pair_property d_3.
left H11.
right H3.
repl H12 H13.
unfold lt in H14.
pose proof no_natural_number_is_member_of_itself 2 two_in_N.
apply (H15 H14).
destruct_ex d_0 n2.
right H11.
pose proof pair_property H12.
left H13.
right H13.
right H5.
pose proof (eq_symm _ _ H15).
pose proof (eq_trans _ _ _ H16 H17).
apply H18.
Defined.
