Require Import Ltac.
From BASE Require Import MathLogic.

Parameter In: Set -> Set -> Prop.
Notation "a ∈ b" := (In a b)(at level 80, left associativity).

Axiom ZF1_extension: ∀ a. ∀ b. (∀ x. x ∈ a ⇔ x ∈ b) -> a = b.

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

Notation "a ⊆ b" := (subset a b)(at level 80, left associativity).

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

Definition set (A: (Set -> Prop)) (b: Set) := ∀ x. ((x ∈ b) ⇔ A x).

Notation "b ≔ { x | A }" := (set (fun x => A) b)
(at level 0, x binder).

Definition any_biimpl_set_is_no_more_than_one (A: (Set -> Prop))
: ∃≤1 s. s ≔ {x | A x}.
unfold set.
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

Definition pair_unord_exists (a b: Set): ∃1p. (p ≔ { x | (x = a) ∨ (x = b) }).
unfold ex_unique.
apply (conj_in _ _).
pose proof ZF3_pairing_equiv a b.
cbv beta in H.
apply H.
intro x1.
intro x2.
intro.
intro.
unfold set in H.
unfold set in H0.
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

Definition unit_set_exists (a: Set): ∃1p. (p ≔ { x | (x = a) }).
unfold set.
pose proof pair_unord_exists a a.
unfold set in H.
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

Notation "{ a }" := (unit_set a).

Definition everySetIsElementOfSomeSet: ∀ a . ∃b. a ∈ b.
intro.
pose proof pair_unord_exists x x.
left H.
cbv beta in H0.
unfold set in H0.
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

Definition union_exists (c: Set): ∃1u. (u ≔ { x | (∃y. (x ∈ y) ∧ (y ∈ c)) }).
apply (conj_in _ _).
refine ((_): (∃ u. u ≔ {x | ∃ y . x ∈ y ∧ y ∈ c})).
pose proof ZF4_union c.
destruct_ex H a.
clear H.
pose proof unique_subset_exists_eq (fun x => (∃y. (x ∈ y) ∧ (y ∈ c))) a.
destruct_ex H s.
apply (ex_in _ s).
unfold set.
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
unfold set in H.
unfold set in H0.
apply (ZF1_extension x1 x2).
intro.
pose proof H x.
pose proof H0 x.
pose proof biimpl_symm _ _ H2.
pose proof biimpl_trans _ _ _ H1 H3.
apply H4.
Defined.

Definition union (c: Set): Set := ι _ (union_exists c).

Definition union2_exists (a b: Set): ∃1u. (u ≔ { x | (x ∈ a) ∨ (x ∈ b) }).
pose proof pair_unord_exists a b.
left H.
destruct_ex H0 p.
clear H H0.
unfold set in H1.
pose proof union_exists p.
unfold set in H.
left H.
destruct_ex H0 u.
clear H H0.
apply (conj_in _ _).
apply (ex_in _ u).
unfold set.
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

Notation " a ∪ b " := (union2 a b)(at level 80, left associativity).

Axiom ZF6_infinity: ∃a. (∃e.  (∀ x . ¬(x ∈ e)) ∧ (e ∈ a)
∧ (∀ x . (x ∈ a) -> (x ∪ (unit_set x)) ∈ a)).

Definition empty_set_unique: ∃1e.  (∀ x . ¬(x ∈ e)).
apply (conj_in _ _).
pose proof ZF6_infinity.
destruct_ex H a.
destruct_ex H0 e.
left H1.
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

Definition intersection_exists (c: Set) (not_empty: ¬(c = ∅)): ∃1a. a ≔ {x | ∀y. (y ∈ c -> x ∈ y)}.
pose proof non_empty_set_has_element c not_empty.
destruct_ex H a.
pose proof unique_subset_exists (fun x=>∀y. (y ∈ c -> x ∈ y)) a.
cbv beta in H1.
apply (conj_in _ _).
unfold set.
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


Definition intersection2_exists (a b: Set): ∃1i. i ≔ {x | x ∈ a ∧ x ∈ b}.
pose proof unique_subset_exists (fun x=>x ∈ b) a.
cbv beta in H.
unfold set.
apply H.
Defined.

Notation " a ∩ b " := (intersection2_exists a b)(at level 80, left associativity).

Definition triple_unord_exists (a b c: Set): ∃1t. 
(t ≔ { x | (x = a) ∨ (x = b) ∨ (x = c) }).
pose proof unit_set_exists a as unit_a_ex.
unfold set in unit_a_ex.
left unit_a_ex.
destruct_ex H unit_a.
clear H.
rename H0 into unit_a_prop.
pose proof unit_set_exists b as unit_b_ex.
unfold set in unit_b_ex.
left unit_b_ex.
destruct_ex H unit_b.
clear H.
rename H0 into unit_b_prop.
pose proof unit_set_exists c as unit_c_ex.
unfold set in unit_c_ex.
left unit_c_ex.
destruct_ex H unit_c.
clear H.
rename H0 into unit_c_prop.
pose proof union2_exists unit_a unit_b as union_a_b_ex.
left union_a_b_ex.
destruct_ex H union_a_b.
clear H.
rename H0 into union_a_b_prop.
unfold set in union_a_b_prop.
pose proof union2_exists union_a_b unit_c as union_a_b_c_ex.
left union_a_b_c_ex.
destruct_ex H union_a_b_c.
clear H.
unfold set in H0.
rename H0 into union_a_b_c_prop.
apply (conj_in _ _).
unfold set.
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

Definition relative_complement_exists (a b: Set): ∃1c. 
(c ≔ { x | (x ∈ a) ∧ ¬(x ∈ b) }).
pose proof unique_subset_exists (fun x => ¬(x ∈ b) ) a.
cbv beta in H.
unfold set.
apply H.
Defined.

Definition relative_complement (a b: Set) := 
ι _ (relative_complement_exists a b). 

Definition symmetric_difference (a b: Set) :=
(relative_complement a b) ∪ (relative_complement b a).

Definition pair (a b: Set) := { (unit_set a) , { a, b } }. 

Notation "< a , b >" := (pair a b)(at level 80, left associativity).

Definition element_of_unit_set (k u: Set): k ∈ (unit_set u) -> k = u.
intro.
pose proof unit_set_exists u.
left H0.
destruct_ex H1 a.
pose proof lemma_12_7_1 _ (unit_set_exists u) a H2.
pose proof eq_subs (fun g => k ∈ (g)) _ _ (eq_symm _ _ H3) H.
cbv beta in H4.
unfold set in H2.
pose proof H2 k.
left H5.
apply H6.
apply H4.
Defined.

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
pose proof pair_unord_exists u u.
left H0.
destruct_ex H1 p.
pose proof lemma_12_7_1 _ (pair_unord_exists u u) p H2.
pose proof eq_subs _ _ _ (eq_symm _ _ H3) H.
unfold set in H2.
pose proof unit_set_exists u.
left H5.
destruct_ex H6 n.
pose proof lemma_12_7_1 _ (unit_set_exists u) n H7.
pose proof eq_subs (fun g => k ∈ (g)) _ _ (H8).
cbv beta in H9.
apply H9.
pose proof H7 k.
cbv beta in H10.
right H10.
apply H11.
pose proof H2 k.
left H12.
pose proof H13 H4.
apply (disj_el _ _ (k = u) H14).
intro.
apply H15.
intro.
apply H15.
intro.
pose proof element_of_unit_set k u.
pose proof H0 H.
pose proof eq_subs (fun g => g ∈ ({u, u})) u k (eq_symm _ _ H1).
apply H2.
pose proof pair_unord_exists u u.
left H3.
destruct_ex H4 p.
pose proof lemma_12_7_1 _ (pair_unord_exists u u) p H5.
pose proof eq_subs (fun g => u ∈ g) _ _ H6.
cbv beta in H7.
apply H7.
unfold set in H5.
pose proof H5 u.
right H8.
apply H9.
apply (disj_in_1 _ _ (eq_refl u)).
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
unfold set in H2.
unfold set in H7.
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
unfold set in H2.
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
unfold set in H2.
pose proof unit_set_exists y.
left H6.
destruct_ex H7 q.
pose proof lemma_12_7_1 _ (unit_set_exists y) q H8.
pose proof eq_symm _ _ H9.
pose proof eq_subs (fun g => p = g) _ _ H10 H5.
cbv beta in H11.
unfold set in H8.
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

Definition pair_property (x y u v: Set): (<x,y> =  <u,v>) -> (x = u) ∧ (y = v).
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
unfold set in H11.
pose proof lemma_12_7_1 _ (pair_unord_exists (unit_set x) {x, y}) p H11.
pose proof eq_symm _ _ H12.
pose proof eq_subs (fun g => {(unit_set u), {u, v}} = g) _ _ H13 H8.
cbv beta in H14.
pose proof pair_equals_to_set ({u}) ({u,v}) p H14.
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




