Require Import Ltac.
From BASE Require Import MathLogic.
From BASE Require Import Chap7_InformalAxiomaticSetTheory.


Ltac take_core a :=
let H := fresh "H" in
pose proof a as H;
simpl in H.

Tactic Notation "take" uconstr(a) :=
  take_core (a).

Tactic Notation "take" uconstr(a) uconstr(b) :=
  take_core (a b).

Tactic Notation "take" uconstr(a) uconstr(b) uconstr(c) :=
  take_core (a b c).

Tactic Notation "take" uconstr(a) uconstr(b) uconstr(c) uconstr(d) :=
  take_core (a b c d).

Tactic Notation "take" uconstr(a) uconstr(b) uconstr(c) uconstr(d) uconstr(e) :=
  take_core (a b c d e).

Tactic Notation "take" uconstr(a) uconstr(b) uconstr(c) uconstr(d) uconstr(e) uconstr(f) :=
  take_core (a b c d e f).

Axiom intuitive_abstraction: forall A: (Set -> Prop), 
∃b. ∀ x. ((x ∈ b) ⇔ (A x)).

(* Exercise 2.1 *)
Theorem simple_in: 2 ∈ (triple_unord 1 2 3).
extract_iota_from_goal (triple_unord 1 2 3).
pose proof biimpl_el_2 _ _ (iota_prop 2).
apply H.
apply disj_in_1.
apply disj_in_2.
apply eq_refl.
Qed.

Ltac last_hyp :=
match goal with
  | H : _ |- _ => constr:(H)        (* returns the newest hypothesis’ name *)
end.

Ltac destr :=
let Hlast := last_hyp in  
let forward := fresh "forward" in  
let backward := fresh "backward" in  
match type of Hlast with
| ?A ⇔ ?B => pose proof conj_el_1 _ _ Hlast as forward;
pose proof conj_el_2 _ _ Hlast as backward;
clear Hlast
| ?A ∨ ?B => apply (disj_el _ _ _ Hlast); 
intro; 
clear Hlast
end.

Ltac swap_biimpl H:=
let H := last_hyp in  
let temp := fresh "temp" in  
match type of H with
| ?A ⇔ ?B => pose proof biimpl_symm _ _ H as temp;
clear H;
rename temp into H
end.

(* Exercise 2.2 *)
Theorem simple_in_2: ¬({1,2} ∈ {{1, 2, 3}, {1, 3}, 1, 2}).
intro.
extract_iota ({{1, 2, 3}, {1, 3}, 1, 2}) H.
pose proof iota_prop ({1, 2}).
simpl in H0.
pose proof biimpl_el_1 _ _ H0 H.
apply (disj_el _ _ _ H1).
intro.
apply (disj_el _ _ _ H2).
intro.
apply (disj_el _ _ _ H3).
intro.
extract_iota ({1, 2}) H4.
take iota_prop0 3.
destr.
extract_iota ({1, 2, 3}) H4.
repl H4 iota_prop0.
take iota_prop1 3.
take iota_prop2 3.
swap_biimpl H5.
right H5.
take eq_refl 3.
take disj_in_2 (3 = 1 ∨ 3 = 2) (3 = 3) H8.
take H7 H9.
repl H4 H10.
take forward H11.
destr.
apply three_not_equals_to_one.
apply H13.
take eq_symm _ _ H13.
apply three_not_equals_to_two.
apply H12.
intro.
extract_iota ({1, 2}) H4.
extract_iota ({1, 3}) H4.
repl H4 iota_prop1.
take iota_prop0 2.
take iota_prop2 2.
take biimpl_el_2 _ _ H5.
take eq_refl 2.
take disj_in_2 (2 = 1) (2 = 2) H8.
take H7 H9.
take biimpl_el_1 _ _ H6.
take H11 H10.
destr.
apply one_not_equals_to_two.
apply eq_symm.
apply H13.
apply three_not_equals_to_two.
apply H13.
intro.
take extension_backwards H3.
take H4 2.
take biimpl_el_1 _ _ H5.
take two_is_not_lt_than_one.
unfold lt in H7.
apply H7.
apply H6.
extract_iota_from_goal ({1, 2}).
take iota_prop0 2.
take biimpl_el_2 _ _ H8.
apply H9.
apply disj_in_2.
apply eq_refl.
intro.
extract_iota ({1, 2}) H2.
repl H2 iota_prop0.
take iota_prop1 2.
destr.
apply two_is_not_lt_than_two.
apply backward.
apply disj_in_2.
apply eq_refl.
Qed.

(* Exercise 2.3 *)
Theorem there_is_set_member_of_itself: ∃s. s ∈ s.
take intuitive_abstraction (fun x=>x=x).
destruct_ex H b.
apply (ex_in (fun x=>x∈x) b).
take H0 b.
destr.
apply backward.
apply eq_refl.
Qed.

Ltac split := apply conj_in.

(* Exercise 2.4 *)
Theorem there_are_specific_sets: ∃A. ∃B. ∃C. (A ∈ B) ∧ (B ∈ C) ∧ (A ∉ C).
apply (ex_in _ ∅).
apply (ex_in _ {`∅}).
apply (ex_in _ {`{`∅}}).
split.
split.
take every_set_is_in_unit_set ∅.
apply H.
take every_set_is_in_unit_set {`∅}.
apply H.
intro.
extract_iota ({`{`∅}}) H.
take iota_prop ∅.
change (∅ ∈ s ⇔ ∅ = {`∅}) in H0.
destr.
take forward H.
take extension_backwards H0 ∅.
destr.
apply (@
any_set_in_empty_set_causes_contradiction ∅).
apply backward0.
extract_iota_from_goal ({`∅}).
take iota_prop0 ∅.
destr.
apply backward1.
apply eq_refl.
Qed.

(* Exercise 2.5
a) set of all integers divisible both by 2 and by 3
b) set of elements which are members of both A and B
c) set of elements which are members of either A or B
d) set of positive integers divisible both by 2 and by 3
e) set of square of primes
f) set of rational numbers where quotient and divisor sum is equal to 1
g) circle with R = 1
h) intersection of two lines = {(0,0)}
*)

(* Exercise 2.6 *)
Theorem pair_property_naked: ∀a. ∀b. ∀c. ∀d.
 { (unit_set a) , {a, b}} = {{`c}, {c, d}} ⇔ (a = c ∧ b = d).
intros a b c d.
apply conj_in.
intro.
take (@pair_property a b c d) H.
apply H0.
intro.
conj_el H.
repl_in_goal H0.
repl_in_goal H1.
apply eq_refl.
Qed.

Notation "A ≠ B" := (¬(A = B))(at level 51, right associativity).

Definition proper_subset(a b: Set) := (a ⊆ b) ∧ (a ≠ b).
Notation "a ⊂ b" := (proper_subset a b)(at level 70, left associativity).

Definition subset_backward(a b: Set) := b ⊆ a.
Notation "a ⊇ b" := (subset_backward a b)(at level 70, left associativity).

(* Exercise 3.1 
a) (->) assume x is from set A, then it is divisible by 6. then it is divisible by 2 and 3. take u = x/2 and v = x/3, OK
(<-) assume x is from set B, then it is divisible by 2 and 3 at the same time. It is possible only if it is divisible by 6, thus take y = x/6 and we are done
b) assume x is from A, then y = sqrt x, thus x >= 0 and belongs to B
assume x is from B, then x >= 0, thus exists its square root and it belongs to A
c) take x from A. Then it is divisible by 6. Thus divisible by 2 and 3. we can find integer y = x/2 so we are in set B
*)

(* Exercise 3.2 *)
Theorem subset_transitive: ∀A. ∀B. ∀C. (A ⊆ B) -> (B ⊆ C) -> (A ⊆ C).
intros A B C.
intros.
intros x.
intro.
take H x H1.
take H0 x H2.
apply H3.
Qed.

Ltac swap_eq H:=
let temp := fresh "temp" in  
match type of H with
| ?A = ?B => pose proof eq_symm _ _ H as temp;
move temp before H;
clear H;
rename temp into H
end.

Theorem subset_proper_proper_transitive: ∀A. ∀B. ∀C. (A ⊆ B) -> (B ⊂ C) -> (A ⊂ C).
intros A B C.
intros.
split.
intros x.
intro.
take H x H1.
conj_el H0.
take H3 x H2.
apply H5.
intro.
conj_el H0.
apply H3.
clear H3.
repl H1 H2.
take extensionality_for_subsets H H3.
swap_eq H4.
take eq_trans _ _ _ H4 H1.
apply H5.
Qed.

Theorem subset_proper_ordinary_proper_transitive: 
∀A. ∀B. ∀C. (A ⊂ B) -> (B ⊆ C) -> (A ⊂ C).
intros A B C.
intros.
split.
conj_el H.
apply (subset_trans _ _ _ H1 H0).
intro.
conj_el H.
clear H.
swap_eq H1.
repl H1 H0.
take extensionality_for_subsets H2 H4.
apply H3.
apply H.
Qed.

Theorem proper_subset_transitive: 
∀A. ∀B. ∀C. (A ⊂ B) -> (B ⊂ C) -> (A ⊂ C).
intros A B C.
intros.
split.
conj_el H.
conj_el H0.
apply (subset_trans _ _ _ H1 H3).
intro.
conj_el H.
conj_el H0.
repl H1 H4.
repl H1 H5.
clear H H0 H4 H5.
take extensionality_for_subsets H2 H6.
swap_eq H.
apply H7.
apply H.
Qed.

Theorem set_in_unord_pair_1: ∀A. ∀B. A ∈ {A, B}.
intros A B.
extract_iota_from_goal ({A, B}).
take iota_prop A.
destr.
apply backward.
apply disj_in_1.
apply eq_refl.
Qed.

Theorem set_in_unord_pair_2: ∀A. ∀B. B ∈ {A, B}.
intros A B.
extract_iota_from_goal ({A, B}).
take iota_prop B.
destr.
apply backward.
apply disj_in_2.
apply eq_refl.
Qed.

Theorem set_in_unord_triple_last: ∀A. ∀B. ∀C. C ∈ {A, B, C}.
intros A B C. 
extract_iota_from_goal ({A, B, C}).
take iota_prop C.
destr.
apply backward.
apply disj_in_2.
apply eq_refl.
Qed.

Theorem unit_set_never_equals_to_empty_set:
∀A. ({`A} = ∅) -> ⊥.
intros A.
intro.
extract_iota ({`A}) H.
repl H iota_prop.
take iota_prop0 A.
take biimpl_el_2 _ _ H0.
apply (@any_set_in_empty_set_causes_contradiction A).
apply H1.
apply eq_refl.
Qed.

Theorem unit_set_injection:
∀A. ∀B. ({`A} = {`B}) -> A = B.
intros A B.
intro.
extract_iota {`A} H.
extract_iota {`B} H.
repl H iota_prop0.
clear iota_prop0.
take iota_prop A.
take iota_prop1 A.
swap_biimpl H1.
take biimpl_trans _ _ _ H1 H0.
take biimpl_el_2 _ _ H2.
apply H3.
apply eq_refl.
Qed.


(* Exercise 3.3 *)
Theorem there_are_specific_sets_proper: 
∃A. ∃B. ∃C. ∃D. ∃E. (A ⊂ B) ∧ (B ∈ C) ∧ (C ⊂ D) ∧ (D ⊂ E).
apply (ex_in _ ∅). (* A *)
apply (ex_in _ {`∅}). (* B *)
apply (ex_in _ {`{`∅}}). (* C *)
apply (ex_in _ {∅,{`∅}}). (* D *)
apply (ex_in _ {∅, {`∅}, {`{`∅}} }). (* E *)
split.
split.
split.
split.
intro x.
intro.
take any_set_in_empty_set_causes_contradiction H (x ∈ {`∅}).
apply H0.
intro.
take extension_backwards H ∅.
take biimpl_el_2 _ _ H0.
take @any_set_in_empty_set_causes_contradiction ∅.
apply H2.
apply H1.
apply every_set_is_in_unit_set.
apply every_set_is_in_unit_set.
split.
intro.
intro.
extract_iota ({`{`∅}}) H.
change (∀ x. x ∈ s ⇔ x ={`∅}) in iota_prop.
extract_iota_from_goal ({∅, {`∅}}).
take iota_prop0 x.
take biimpl_el_2 _ _ H0.
apply H1.
apply disj_in_2.
take iota_prop x.
destr.
apply forward.
apply H.
intro.
take extension_backwards H.
take H0 ∅.
destr.
take backward  (set_in_unord_pair_1 ∅ {`∅}).
extract_iota ({`∅}) H1.
extract_iota ({`s}) H1.
take iota_prop0 ∅.
destr.
take forward0 H1.
take biimpl_el_2 _ _ (iota_prop ∅).
swap_eq H2.
repl H2 H3.
take eq_refl ∅.
take H4 H5.
apply (@any_set_in_empty_set_causes_contradiction ∅).
apply H6.
split.
intro x.
intro.
extract_iota ({∅, {`∅}}) H.
take iota_prop x.
destr.
take forward H.
clear forward backward.
apply (disj_el _ _ _ H0).
intro.
extract_iota_from_goal ({∅, {`∅}, {`{`∅}}}).
take biimpl_el_2 _ _ (iota_prop0 x).
apply H2.
apply disj_in_1.
apply disj_in_1.
apply H1.
intro.
extract_iota_from_goal ({∅, {`∅}, {`{`∅}}}).
take biimpl_el_2 _ _ (iota_prop0 x).
apply H2.
apply disj_in_1.
apply disj_in_2.
apply H1.
intro.
take extension_backwards H ({`{`∅}}).
take biimpl_el_2 _ _ H0.
take set_in_unord_pair_1 ∅ {`∅}.
take set_in_unord_triple_last ∅ {`∅} ({`{`∅}}).
take H1 H3.
extract_iota ({∅, {`∅}}) H4.
take iota_prop {`{`∅}}.
take biimpl_el_1 _ _ H5 H4.
apply (disj_el _ _ _ H6).
intro.
apply (unit_set_never_equals_to_empty_set {`∅}).
apply H7.
intro.
take unit_set_injection _ _ H7.
apply (unit_set_never_equals_to_empty_set ∅).
apply H8.
Qed.

Lemma empty_set_doesnt_contain_itself: ¬(∅ ∈ ∅).
intro.
apply (@any_set_in_empty_set_causes_contradiction ∅).
apply H.
Qed.

Ltac ass := assumption.

(* Exercise 3.4. Answer: Only (D) case is correct! *)
Theorem exercise_3_4_a: 
¬(∀A. ∀B. ∀C. (A ∉ B) -> (B ∉ C) -> (A ∉ C)).
intro.
take H ∅ ({`{`∅}}) {`∅}.
assert (∅ ∉ {`{`∅}}).
extract_iota_from_goal ({`∅}).
extract_iota_from_goal ({`s}).
intro.
take iota_prop0 ∅.
left H2.
take H3 H1.
take iota_prop s.
swap_eq H4.
right H5.
take H6 H4.
take eq_subs (fun s =>s ∈ s) s ∅ H4 H7.
apply empty_set_doesnt_contain_itself.
ass.
assert ({`{`∅}} ∉ {`∅}).
intro.
extract_iota ({`∅}) H2. (* s *)
extract_iota ({`s}) H2. (* s0 *)
(* s is in so but not in s*)
take iota_prop0 s.
right H3.
take H4 (eq_refl s).
take iota_prop s0.
left H6.
take H7 H2.
repl H8 H5.
apply (@any_set_in_empty_set_causes_contradiction s).
apply H9.
take H0 H1 H2.
apply H3.
apply every_set_is_in_unit_set.
Qed.

Theorem exercise_3_4_b: 
¬(∀A. ∀B. ∀C. (A ≠ B) -> (B ≠ C) -> (A ≠ C)).
intro.
take H ∅ ({`∅}) ∅.
assert (∅ ≠ {`∅}).
intro.
take unit_set_never_equals_to_empty_set ∅.
apply H2.
swap_eq H1.
apply H1.
assert ({`∅} ≠ ∅).
intro.
take unit_set_never_equals_to_empty_set ∅.
apply H3.
apply H2.
take H0 H1 H2.
apply H3.
apply eq_refl.
Qed.

Theorem exercise_3_4_c: 
¬(∀A. ∀B. ∀C. (A ∈ B) -> (¬(B ⊆ C)) -> (A ∉ C)).
intro.
take H ∅ {∅, {`∅}} {`∅}.
assert (∅ ∈ {∅, {`∅}}).
extract_iota_from_goal ({∅, {`∅}}).
take iota_prop ∅.
right H1.
apply H2.
apply disj_in_1.
apply eq_refl.
assert (¬ ({∅, {`∅}} ⊆ {`∅})).
intro.
take H2 {`∅}.
take set_in_unord_pair_2 ∅ {`∅}.
take H3 H4.
extract_iota ({`∅}) H5.
take iota_prop s.
left H6.
take H7 H5.
take eq_subs _ s ∅ H8 H5.
repl H8 H9.
apply empty_set_doesnt_contain_itself.
ass.
take H0 H1 H2.
apply H3.
apply every_set_is_in_unit_set.
Qed.

Lemma proper_subset_exists_element:  ∀A. ∀B.
(A ⊂ B) -> ∃x. (x ∈ B) ∧ (x ∉ A).
intros A B.
intro.
left H.
right H.
apply DN_el.
intro.
apply not_ex_implies_all_not in H2.
apply H1.
assert (B ⊆ A).
intro x.
take H2 x.
intro.
take deMorganNotAnd _ _ H3.
take (disj_el_alt_1 _ (¬ (x ∉ A))) H5.
apply DN_el.
apply H6.
apply DN_in.
ass.
apply (extensionality_for_subsets H0 H3).
Qed.

Theorem exercise_3_4_d: 
(∀A. ∀B. ∀C. (A ⊂ B) -> (B ⊆ C) -> (C ⊈ A)).
intros A B C.
intro.
intro.
intro.
take proper_subset_exists_element _ _ H.
apply (ex_el _ H2).
intro.
intro.
left H3.
right H3.
left H.
take subset_trans _ _ _ H0 H1.
take H7 x H4.
apply H5.
ass.
Qed.

Theorem exercise_3_4_e: 
(¬(∀A. ∀B. ∀C. (A ⊆ B) -> (B ∈ C) -> (A ∉ C))).
intro.
take H ∅ ∅ {`∅}.
take subset_refl ∅.
take (every_set_is_in_unit_set ∅).
take H0 H1 H2.
apply H3.
ass.
Qed.

Theorem exercise_3_5: 
(∀A. A ⊆ ∅ ⇔ A = ∅).
intro A.
split.
intro.
apply ZF1_extension.
intro.
split.
intro.
take H x H0.
ass.
intro.
take any_set_in_empty_set_causes_contradiction H0.
apply H1.
intro.
repl_in_goal H.
apply subset_refl.
Qed.

(* Exercise 3.6. Skipped, need lists!!! *)

Theorem exercise_3_7: ∃s. ∀x. x∈s -> x⊆s.
apply (ex_in _ {∅, {`∅}}).
intro.
intro.
extract_iota ({`∅}) H. (* s = {`∅} *)
extract_iota ({∅, s}) H. (* s0 = {∅, {`∅}} *)
take iota_prop0 x.
take biimpl_el_1 _ _ H0.
take H1 H.
apply (disj_el _ _ _ H2).
intro.
intro k.
intro.
repl H3 H4.
take @any_set_in_empty_set_causes_contradiction k H5.
apply H6.
intro.
intro k.
intro.
take iota_prop k.
take biimpl_el_1 _ _ H5.
repl H3 H4.
take H6 H7.
repl_in_goal H8.
apply set_in_unord_pair_1.
Qed.

(* Exercise 3.8. 
A = {{1, 2}, {3}, 1}
000 - {}
001 - {1}
010 - {{3}}
011 - {{3}, 1}
100 - {{1, 2}}
101 - {{1, 2}, 1}
110 - {{1, 2}, {3}}
111 - {{1, 2}, {3}, 1}
---
Skipped prove this is the only power set. Maybe cardinality needed
*)

(* Exercise 3.9. 
An = {∅, {∅}, {{∅}, ∅}, {{{∅}, ∅}, ∅, {∅}} etc... }
*)

Definition disjoint (A B: Set) := ((A ∩ B) = ∅).
Definition intersect (A B: Set) := ((A ∩ B) ≠ ∅).
Definition disjoint_collection (A: Set) := 
∀x::A. ∀y::A. (x ≠ y) -> disjoint x y.

Definition partition (X P: Set) := (disjoint_collection P) ∧ 
(∀s. (s ⊆ X) -> (s ≠ ∅) -> s ∈ P) ∧ (∀x::X. ∃p::P. x ∈ p).

Definition absolute_compelement_exists (A: Set): 
∃1c. ∀ x. ((x ∈ c) ⇔ (x ∉ A)).
take intuitive_abstraction (fun x => x ∉ A).
split.
apply H.
take any_biimpl_set_is_no_more_than_one (fun x =>x ∉ A).
apply H0.
Qed.

Definition absolute_compelement (A: Set): Set 
:= ι _ (absolute_compelement_exists A).

Definition universal_set_exists: 
∃1u. ∀ x. ((x ∈ c) ⇔ (x ∉ A)).


