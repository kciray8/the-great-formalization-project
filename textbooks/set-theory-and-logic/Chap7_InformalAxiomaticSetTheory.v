Require Import Ltac.
From BASE Require Import MathLogic.

Parameter In: Set -> Set -> Prop.
Notation "a ∈ b" := (In a b)(at level 80, left associativity).

Notation "∀ x :: S . p" := (all (fun x => ((x ∈ S) -> p)))
  (at level 200, x binder).

Notation "∃ x :: S . p" := (ex (fun x => ((x ∈ S) ∧ p)))
  (at level 200, x binder, right associativity).

(* not working! *)
Definition biimpl_el_left {A: Prop} {s: Set} {x: Set} 
(H: (∀z . (z ∈ s) ⇔ A)) (u: x ∈ s)  : A.
pose proof H x.
left H0.
pose proof H1 u.
apply H2.
Defined.

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

(* '`' is used to prevent collision with coq { } *)
Notation "{` a }" := (unit_set a).

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

Inductive extraction_param :=
|full_clean
|retain_equality
.

Ltac extract_iota_ex obj H param :=
let uniqueness_proof := fresh in
let s := fresh "s" in
let iota_prop := fresh "iota_prop" in
let eq_to_iota := fresh "eq_to_iota" in
let eq_to_iota_backwards := fresh "eq_to_iota_backwards" in
let replaced_H := fresh "replaced_H" in
let h_expanded := fresh "h_expanded" in
let temp := fresh "temp" in
match obj with
| context [ (?t) ] =>
match eval unfold t in obj with
| context [ι ?P ?u] => 
pose proof u as uniqueness_proof; 
pose proof conj_el_1 _ _ uniqueness_proof as ex_proof;
clear uniqueness_proof;
apply (ex_proof  _); 
intro s; 
intro iota_prop;
clear ex_proof;
pose proof lemma_12_7_1 P u s iota_prop as eq_to_iota;
pose proof eq_symm _ _ eq_to_iota as eq_to_iota_backwards;
pose proof H as h_expanded;
pattern obj in h_expanded;
match type of h_expanded with
| ?a ?b => 
pose proof eq_subs a _ _ (eq_to_iota_backwards) H as replaced_H;
cbv beta in replaced_H;
move replaced_H after H;
clear H;
rename replaced_H into H;
match param with
| retain_equality => 
rename eq_to_iota into temp;
pose proof (temp: s = obj) as eq_to_iota;
clear temp;
clear eq_to_iota_backwards;
clear h_expanded
| full_clean =>
clear eq_to_iota;
clear eq_to_iota_backwards;
clear h_expanded
end;
move iota_prop before H
end
| _ => idtac "error inside nested match"
end
| _ => idtac "error inside outer match"
end.

Tactic Notation "extract_iota" constr(obj) constr(H) := extract_iota_ex obj H full_clean.

Ltac extract_iota_from_goal_ex obj param :=
let uniqueness_proof := fresh "uniqueness_proof" in
let s := fresh "s" in
let prop := fresh "iota_prop" in
let eq_to_iota := fresh "eq_to_iota" in
let eq_to_iota_backwards := fresh "eq_to_iota_backwards" in
let replaced_H := fresh "replaced_H" in
let temp := fresh "temp" in
match obj with
|context [ (?t) ] =>
match eval unfold t in obj with
| ι ?P ?u => 
pose proof u as uniqueness_proof; 
pose proof conj_el_1 _ _ uniqueness_proof as ex_proof;
clear uniqueness_proof;
apply (ex_proof  _); 
intro s; 
intro prop;
clear ex_proof;
pose proof lemma_12_7_1 P u s prop as eq_to_iota;
pose proof eq_symm _ _ eq_to_iota as eq_to_iota_backwards;
pattern obj;
match goal with
| |- ?a ?B => apply(eq_subs a _ _ eq_to_iota);
match param with
| retain_equality => 
rename eq_to_iota into temp;
pose proof (temp: s = obj) as eq_to_iota;
clear temp;
clear eq_to_iota_backwards
| full_clean =>
clear eq_to_iota;
clear eq_to_iota_backwards
end
end
| _ => idtac "error inside nested match"
end
| _ => idtac "error inside outer match"
end.

Tactic Notation "extract_iota_from_goal" constr(obj) := 
extract_iota_from_goal_ex obj full_clean.

Definition collapse_unit (u: Set): {u, u} = (unit_set u).
apply (ZF1_extension ({u, u}) (unit_set u)).
intro k.
apply (conj_in _ _).
intro.
extract_iota ({u, u}) H.
unfold set in iota_prop .
extract_iota_from_goal {`u}.
cbv beta in iota_prop0 .
unfold set in iota_prop0.
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
unfold set in iota_prop.
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
(b ≔ { x | (x ⊆ a) }).
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
unfold set.
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

Notation "'𝒫' a " := (power_set a)(at level 70, left associativity).

Definition cartesian_product_exists (a b: Set): ∃1c. 
(c ≔ { w | (∃x. (x ∈ a) ∧ (∃y. (y ∈ b) ∧ w = <x,y>))}).
pose proof ZF2_subsets (
    fun w => (∃x. ∃y. ((¬(x = y)) ∧ (x ∈ a) ∧ (y ∈ b) ∧ (∀z. (z ∈ w) ⇔ 
    (z = {`x} ∨ z = {x, y}))))
     ∨ (∃x. (x ∈ a) ∧ (x ∈ b) ∧ (∀z. (z ∈ w) ⇔ z = {`x})
)) (𝒫(𝒫((a ∪ b)))).
refine (conj_in _ _ _ (any_biimpl_set_is_no_more_than_one _)).
destruct_ex H big.
apply (ex_in _ big).
clear H.
unfold set.
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
unfold set in iota_prop.
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
unfold set in iota_prop .
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
Focus 2.
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
pose proof eq_subs (fun g=>w = (< x, g >)) _ _ (eq_symm _ _ H5) H4.
cbv beta in H9.
unfold pair in H9.
extract_iota ({{`x}, {x, x}}) H9.
unfold set in iota_prop.
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
(ι (set (fun x0 : Set => x0 = x ∨ x0 = y))
(pair_unord_exists x y))).
left H8.
destruct_ex H9 r.
unfold set in H10.
pose proof lemma_12_7_1 _ (pair_unord_exists {`x}
(ι (set (fun x0 : Set => x0 = x ∨ x0 = y))
(pair_unord_exists x y))) r H10.
pose proof eq_symm _ _ H11.
pose proof eq_subs (fun g=> g = w) _ _ H12 H6.
cbv beta in H13.
pose proof (H10 :∀ z. z ∈ r⇔ (z = {`x}∨ z ={x, y})).
pose proof eq_subs (fun g => ∀ z . z ∈ g ⇔ (z = {`x} ∨ z = {x, y})) r w H13 H14.
cbv beta in H15.
apply H15.
clear H3.
assert ({`x} ⊆ a).
intro m.
intro.
extract_iota {`x} H.
unfold set in iota_prop.
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
unfold set in iota_prop.
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
unfold set in iota_prop.
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
unfold set in iota_prop.
pose proof eq_subs (fun g => ∀ x . x ∈ g ⇔ (x ∈ a ∨ x ∈ b)) 
_ _ (eq_symm _ _ H7) iota_prop.
cbv beta in H9.
clear H7 iota_prop.
clear s.

pose proof H8.
extract_iota (𝒫 (a ∪ b)) H7.
unfold set in iota_prop.
pose proof eq_subs (fun g => ∀ x . x ∈ g ⇔ x ⊆ (a ∪ b)) 
_ _ (eq_symm _ _ H7) iota_prop.
cbv beta in H11.
clear H7 iota_prop s.

pose proof H6.
extract_iota (𝒫 (𝒫 (a ∪ b))) H7.
unfold set in iota_prop.
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
unfold set in iota_prop.
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
unfold set in iota_prop0.
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
unfold set in iota_prop0.
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

Definition relation (a: Set) := ∀x. (x ∈ a) -> ∃m. ∃n. x = <m,n>.

Definition relation_is_subset_of_cp_with_itself: ∀r. (relation r) ->  
r ⊆ (union (union r)) × (union (union r)).
intro r.
intro.
unfold relation in H.
intro m.
intro.
extract_iota_from_goal (union (union r) × union (union r)).
unfold set in iota_prop.
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
unfold set in iota_prop0.
pose proof iota_prop0: ∀ x. x ∈ s0⇔ (∃ y. x ∈ y∧ y∈ union r).
clear iota_prop0.
pose proof H7 x.
right H8.
apply H9.
unfold pair in H6.
pose proof pair_unord_exists x y.
left H10.
destruct_ex H11 x_y.
unfold set in H12.
apply (ex_in _ x_y).
apply (conj_in _ _).
pose proof H12 x.
right H13.
apply H14.
apply (disj_in_1 _ _ (eq_refl x)).
extract_iota_from_goal (union r).
unfold set in iota_prop0.
pose proof iota_prop0 x_y.
right H13.
apply H14.
apply (ex_in _ m).
apply (conj_in _ _).
extract_iota ({{`x}, {x, y}}) H6.
unfold set in iota_prop1.
pose proof iota_prop1:∀ x0. x0 ∈ s2⇔ (x0 = {`x}∨ x0 ={x, y}).
pose proof H15 x_y.
right H16.
pose proof eq_subs(fun g=>(x_y = {`x} ∨ x_y = {x, y}) ⇒ (x_y ∈ g)) _ _
(eq_symm _ _ H6) H17.
apply H18.
refine (disj_in_2 _ _ _).
extract_iota_from_goal ({x, y}).
unfold set in iota_prop2.
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
unfold set in iota_prop0.
pose proof iota_prop0 : ∀ x. x ∈ s0⇔ (∃ y
. x ∈ y ∧ y ∈ union r).
pose proof H7 y.
right H8.
apply H9.
pose proof pair_unord_exists x y.
left H10.
unfold set in H11.
destruct_ex H11 x_y.
apply (ex_in _ x_y).
apply (conj_in _ _).
pose proof H12 y.
right H13.
apply H14.
refine (disj_in_2 _ _ (eq_refl y)).
extract_iota_from_goal (union r).
unfold set in iota_prop1.
pose proof iota_prop1 x_y.
right H13.
apply H14.
apply (ex_in _ m).
apply (conj_in _ _).
unfold pair in H6.
extract_iota ({{`x}, {x, y}}) H6.
unfold set in iota_prop2.
pose proof iota_prop2:∀ x0. x0 ∈ s2⇔ (x0 = {`x}∨ x0 ={x, y}).
pose proof H15 x_y.
right H16.
pose proof eq_subs(fun g=>(x_y = {`x} ∨ x_y = {x, y}) ⇒ (x_y ∈ g)) _ _
(eq_symm _ _ H6) H17.
apply H18.
refine (disj_in_2 _ _ _).
extract_iota_from_goal ({x, y}).
unfold set in iota_prop3.
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


Definition domain_exists (r: Set) (is_relation: relation r): ∃1d. 
(d ≔ { x | (∃y. <x,y> ∈ r )}).
unfold relation in is_relation .
apply (conj_in _ _).
unfold set.
pose proof ZF2_subsets (fun x => (∃y. <x,y> ∈ r ))
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
unfold set in H5.
destruct_ex H5 q_y.
pose proof lemma_12_7_1 _ (pair_unord_exists {`q} {q, y}) q_y H6.
pose proof eq_symm _ _ H7.
pose proof eq_subs (fun g=> g ∈ r) _ _ H8 H4.
cbv beta in H9.
clear H7 H8.
extract_iota_from_goal (union (union r)).
unfold set in iota_prop.
pose proof iota_prop : ∀ x. x ∈ s⇔ (∃ y
. x ∈ y ∧ y ∈ (union r)).
clear iota_prop.
pose proof H7 q.
right H8.
apply H10.
pose proof pair_unord_exists q y.
unfold set in H11.
left H11.
destruct_ex H12 q_y_unord.
apply (ex_in _ q_y_unord).
apply (conj_in _ _).
pose proof H13 q.
right H14.
apply H15.
apply (disj_in_1 _ _ (eq_refl q)).
extract_iota_from_goal (union r).
unfold set in iota_prop.
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
unfold set in iota_prop0.
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

Definition domain (r: Set) (is_relation: relation r): ι _ (domain_exists r is_relation).

Definition range_exists (r: Set) (is_relation: relation r): ∃1d. 
(d ≔ { y | (∃x. <x,y> ∈ r )}).
unfold relation in is_relation .
apply (conj_in _ _).
unfold set.
pose proof ZF2_subsets (fun y => (∃x. <x,y> ∈ r ))
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
unfold set in H5.
destruct_ex H5 q_y.
pose proof lemma_12_7_1 _ (pair_unord_exists {`y} {y, q}) q_y H6.
pose proof eq_symm _ _ H7.
pose proof eq_subs (fun g=> g ∈ r) _ _ H8 H4.
cbv beta in H9.
clear H7 H8.
extract_iota_from_goal (union (union r)).
unfold set in iota_prop.
pose proof iota_prop : ∀ x. x ∈ s⇔ (∃ y
. x ∈ y ∧ y ∈ (union r)).
clear iota_prop.
pose proof H7 q.
right H8.
apply H10.
pose proof pair_unord_exists y q.
unfold set in H11.
left H11.
destruct_ex H12 q_y_unord.
apply (ex_in _ q_y_unord).
apply (conj_in _ _).
pose proof H13 q.
right H14.
apply H15.
apply (disj_in_2 _ _ (eq_refl q)).
extract_iota_from_goal (union r).
unfold set in iota_prop.
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
unfold set in iota_prop0.
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

(*
eq_hyp: empty_set' = ∅
target_hyp: empty_set' ∈ some_successor_set
*)
Ltac repl eq_hyp target_hyp :=
let symmetric_eq := fresh "symmetric_eq" in
let target_hyp_repl := fresh target_hyp in
match type of eq_hyp with
| eq ?a ?b =>
match type of target_hyp with
|context g[ b ] => 
let my_func := (context g [a]) in 
pose proof eq_symm _ _ eq_hyp as symmetric_eq;
pose proof (eq_subs (fun k => _)
b a symmetric_eq target_hyp) : my_func as target_hyp_repl;
clear symmetric_eq

|context g[ a ] => 
let my_func := (context g [b]) in 
pose proof (eq_subs (fun k => _)
a b eq_hyp target_hyp) : my_func as target_hyp_repl

| _ => idtac "error inside nested matches"
end
end.

Definition subset_ref (a: Set): a ⊆ a.
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
unfold set in pa_prop.
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
apply (subset_ref some_successor_set).
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
unfold set in H1.
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
unfold set in H1.
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
unfold set in iota_prop0.
repl H0 iota_prop0.
pose proof iota_prop1 n.
right H1.
pose proof iota_prop n.
apply H3.
apply H2.
apply (disj_in_2 _ _).
extract_iota_from_goal ({`n}).
unfold set in iota_prop2.
pose proof iota_prop2 n.
right H4.
apply H5.
apply (eq_refl n).
Defined.

(* TODO repeat again to understand better*)
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
apply (subset_ref N).
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

Definition every_set_is_in_unit_set: ∀m. m ∈ {`m}.
intro.
extract_iota_from_goal {`x}.
pose proof iota_prop x.
right H.
apply H0.
apply (eq_refl x).
Defined.

Definition lt (a b: Set) := a ∈ b.

Notation "a < b" := (lt a b)(at level 70).

Definition le (a b: Set) := (a < b) ∨ (a = b).

Notation "a ≤ b" := (le a b)(at level 70).

Definition ordinary_induction:= forall (P: Set->Prop), 
(P 0) -> 
(∀x :: N. P x -> (P (S x))) ->  
(∀x :: N. P x).

Definition strong_induction:= forall (P: Set->Prop), 
(P 0) -> 
(∀x :: N. (∀k :: N. (k ≤ x) -> P k) -> (P (S x))) -> 
(∀x :: N. P x).

Definition only_zero_is_less_than_one (k: Set) 
(k_is_nn: k ∈ N) (H: k < S 0): k = 0.
unfold lt in H.
unfold S in H.
unfold zero in H.
extract_iota (∅ ∪ {`∅}) H.
unfold set in iota_prop.
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
unfold set in iota_prop0.
pose proof iota_prop0 ∅.
right H4.
apply H5.
apply (disj_in_1 _ _).
apply H2.
intro.
pose proof element_of_unit_set ∅ x H2.
apply (disj_in_1 _ _).
extract_iota_from_goal (x ∪ {`x}).
unfold set in iota_prop0.
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
ordinary_induction ⇔ strong_induction.
unfold ordinary_induction.
unfold strong_induction.
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
repl H7 H8.
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
unfold set in iota_prop.
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
pose proof subset_ref n.
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
unfold set in iota_prop.
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
unfold set in iota_prop .
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
unfold set in iota_prop0.
unfold set in iota_prop.
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
pose proof subset_ref n.
pose proof no_nat_is_subset_of_any_its_elements n n_nat n H21.
apply (H23 H22).
Defined.

Definition relation_on_cp (f: Set) (X Y: Set) := f ⊆ (X × Y).

Definition is_function (f: Set) (X Y: Set) := 
(relation_on_cp f X Y) ∧ 
(∀ x :: X. ∃ y :: Y. (<x,y> ∈ f)) ∧ 
(∀ x. ∀ y. ∀ z. (<x,y> ∈ f) -> (<x,z> ∈ f) -> (y = z)).

Definition f_appl_ex (f: Set) (X Y: Set) (H: is_function f X Y) (x: Set) 
(x_in_X: x ∈ X):
 ∃1y. (y ∈ Y) ∧ (<x,y> ∈ f).
apply (conj_in _ _).
left H.
refine (_: ∃ y. (y ∈ Y) ∧ < x, y > ∈ f).
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

Definition f_x_eq_y (f: Set) (x y: Set) := (<x, y> ∈ f).

Notation "f [ x ] ≔ y" := (f_x_eq_y f x y)(at level 70).

Definition inc_set_ex: ∃1f. (is_function f N N) ∧ 
(∀x :: N. (f [x] ≔ (S x))).
pose proof cartesian_product_exists N N as NN_ex.
unfold set in NN_ex.
left NN_ex.
destruct_ex H NN.
clear H.
pose proof ZF2_subsets 
(* made it simple a bit *)
(fun g => ∃ a :: N . g = (< a, (S a) >)) NN.
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
pose proof H1 (< x, S x >).
right H3.
apply H4.
apply (conj_in _ _).
pose proof H0 (< x, S x >).
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
pose proof H1 (< x, y >).
pose proof H1 (< x, z >).
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
pose proof pair_property _ _ _ _ H14.
left H16.
pose proof eq_subs (fun a2 => (< x, z >) = (< a2, S a2 >))
_ _ (eq_symm _ _ H17) H14.
cbv beta in H18.
pose proof pair_property _ _ _ _ H15.
left H19.
pose proof eq_subs (fun a2 => (< x, y >) = (< a2, S a2 >))
_ _ (eq_symm _ _ H20) H15.
cbv beta in H21.
pose proof eq_trans _ _ _ H18 (eq_symm _ _ H21).
pose proof pair_property _ _ _ _ H22.
right H23.
apply (eq_symm _ _ H24).
intro x.
intro.
unfold f_x_eq_y.
pose proof H1 (< x, S x >).
right H2.
apply H3.
apply (conj_in _ _).
pose proof H0 (< x, S x >).
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

Definition one_in_N : 1 ∈ N.
unfold one.
pose proof PN1_empty_set.
pose proof PN2_succ ∅ H.
apply H0.
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
| _ => idtac "First argument is not in form ∀ x . (_ ⇔ _)"
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
| _ => idtac "First argument is not in form ∀ x . (_ ⇔ _)"
end.

Definition function_result_is_in_arg(f x: Set):
∀y. (f[x] ≔ y) -> y ∈ x.

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
pose proof ZF2_subsets (fun p => (∀c. ∀d. (<c,d> = p) -> c ∈ x)) f.
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
unfold set in iota_prop.
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
pose proof H0 (< a, y >).
right H9.
apply H10.
apply (conj_in _ _).
apply H8.
intro c.
intro d.
intro.
pose proof pair_property _ _ _ _ H11.
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
apply (g_subset_of_f (< a, b >) H).
apply (g_subset_of_f (< a, c >) H2).
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

Definition functional_application_works_for_equality 
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
unfold set in H1.
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
unfold set in X_prop.
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
pose proof functional_application_works_for_equality f_is_func 
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

