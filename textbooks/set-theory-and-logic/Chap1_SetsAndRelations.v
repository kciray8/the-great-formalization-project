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

Tactic Notation "take" uconstr(a) uconstr(b) uconstr(c) uconstr(d) uconstr(e) uconstr(f) uconstr(g) :=
  take_core (a b c d e f g).

Tactic Notation "take" uconstr(a) uconstr(b) uconstr(c) uconstr(d) uconstr(e) uconstr(f) uconstr(g) uconstr(h) :=
  take_core (a b c d e f g h).

Tactic Notation "take" uconstr(a) uconstr(b) uconstr(c) uconstr(d) uconstr(e) uconstr(f) uconstr(g) uconstr(h) uconstr(i) :=
  take_core (a b c d e f g h i).

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

Definition extension_trans (a b: Set) (P: Set->Prop) 
(H1: ∀x. (x ∈ a) ⇔ P x) 
(H2: ∀x. (x ∈ b) ⇔ P x): a = b.
apply ZF1_extension.
intros g.
take H1 g.
take H2 g.
swap_biimpl H0.
take biimpl_trans _ _ _ H H0.
assumption.
Qed.

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
Notation "a ⊂ b" := (proper_subset a b)(at level 71, left associativity).

Definition subset_backward(a b: Set) := b ⊆ a.
Notation "a ⊇ b" := (subset_backward a b)(at level 71, left associativity).

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

Definition disjoint (A B: Set) := 
∃1e. empty_set_p e ∧
∃1i. intersection2_p A B i ∧
(i = e).

Definition intersect (A B: Set) := 
∃1e. empty_set_p e ∧
∃1i. intersection2_p A B i ∧
(i ≠ e).

Definition disjoint_collection (A: Set) := 
∀x::A. ∀y::A. (x ≠ y) -> disjoint x y.

Definition collection_of_nonempty_sets (A: Set) := 
∀x::A. ¬ empty_set_p x.

Definition partition_p (P X: Set) := 
∃1e. empty_set_p e ∧
((disjoint_collection P) ∧ 
(collection_of_nonempty_sets P) ∧
(∀s. s ∈ P -> (s ⊆ X)) ∧
(∀x::X. ∃p::P. x ∈ p)).

Tactic Notation "left" := apply (disj_in_1).
Tactic Notation "right" := apply (disj_in_2).

Ltac both_old H := left H; right H.

Section AbsoluteComplementation.

Local Definition absolute_compelement_exists (A: Set): 
∃1c. ∀ x. ((x ∈ c) ⇔ (x ∉ A)).
take intuitive_abstraction (fun x => x ∉ A).
split.
apply H.
take any_biimpl_set_is_no_more_than_one (fun x =>x ∉ A).
apply H0.
Qed.

Local Definition absolute_compelement (A: Set): Set 
:= ι _ (absolute_compelement_exists A).

Local Notation ac A := (absolute_compelement A).

Local Definition universal_set_exists: 
∃1u. ∀k. k ⊆ u.
split.
take intuitive_abstraction (fun x => x = x).
destruct_ex H b.
apply (ex_in _ b).
intro k.
intro g.
intro.
take H0 g.
right H2.
take (eq_refl g).
take H3 H4.
ass.
intros q w.
intros H1 H2.
apply ZF1_extension.
intro t.
split.
intro.
take H2 q t.
apply H0.
ass.
intro.
take H1 w t.
apply H0.
ass.
Qed.

Local Definition U_global: Set := ι _ (universal_set_exists).
Local Notation U := (U_global).

Theorem exercise_4_1: ∀A. ∀B. (∅ ⊆ (A ∩ B)) ∧ ((A ∩ B) ⊆ (A ∪ B)).
intros A B.
split.
intro g.
intro.
take any_set_in_empty_set_causes_contradiction H.
apply H0.
intro k.
intro.
extract_iota_from_goal ((A ∪ B)).
take iota_prop k.
right H0.
apply H1.
extract_iota ((A ∩ B)) H.
take iota_prop0 k.
left H2.
take H3 H.
left.
left H4.
ass.
Qed.

(* Exercise 4.2. 
A - even numbers except 0 = {2, 4, 6 ...}
B - odd numbers = {1, 3, 5, ...}
C - all integers of Z < 10, C = {9, 8, 7, ..., 0, -1, -2, ...}
A union B - positive integers
not (A union B) - negative integers and zero
not C = Z - C = {10, 11, 12, ...}
A - (not C) = {2, 4, 6, 8}
C - (A union B) = {0, -1, -2, ...}
*)

(* Exercise 4.3. a
Z+ = {1, 2, 3, 4, ...}
A = {2, 4, 6, 8, 10, 12...}
B = {1, 3, 5, 7, 9 ...}
C = {3, 6, 9, 12, 15 ...}
A intersect C = divisors both 2 and 3 = {6, 12, 18, ...}
A union C - numbers divised by 2 OR 3 = {2, 3, 4, 6, ...}
B - C = complement of C relative to B = odd but not divisible by 3 = {1, 5, ...}
*)

Theorem intersection_el: ∀A. ∀B. ∀x. x ∈ (A ∩ B) -> (x ∈ A) ∧ (x ∈ B).
intros A B x.
intro.
extract_iota ((A ∩ B)) H.
take iota_prop x.
left H0.
apply H1.
ass.
Qed.

Theorem intersection_in: ∀A. ∀B. ∀x. (x ∈ A) ∧ (x ∈ B) -> x ∈ (A ∩ B).
intros A B x.
intro.
extract_iota_from_goal ((A ∩ B)).
take iota_prop x.
right H0.
apply H1.
ass.
Qed.

Theorem union_el: ∀A. ∀B. ∀x. x ∈ (A ∪ B) -> (x ∈ A) ∨ (x ∈ B).
intros A B x.
intro.
extract_iota ((A ∪ B)) H.
take iota_prop x.
left H0.
apply H1.
ass.
Qed.

Theorem union_in: ∀A. ∀B. ∀x. (x ∈ A) ∨ (x ∈ B) -> x ∈ (A ∪ B).
intros A B x.
intro.
extract_iota_from_goal ((A ∪ B)).
take iota_prop x.
right H0.
apply H1.
ass.
Qed.

(* Exercise 4.3. b *)
Theorem inversection_distr: ∀A. ∀B. ∀C. (A ∩ (B ∪ C)) = ((A ∩ B) ∪ (A ∩ C)).
intros A B C.
apply ZF1_extension.
intro x.
split.
intro.
apply intersection_el in H.
conj_el H.
apply union_el in H1.
apply union_in.
apply (disj_el _ _ _ H1).
intro.
left.
apply intersection_in.
split.
ass.
ass.
intro.
right.
apply intersection_in.
split.
ass.
ass.
intro.
apply union_el in H.
apply intersection_in.
split.
apply (disj_el _ _ _ H).
intro.
apply intersection_el in H0.
conj_el H0.
ass.
intro.
apply intersection_el in H0.
conj_el H0.
ass.
apply union_in.
apply (disj_el _ _ _ H).
intro.
apply intersection_el in H0.
conj_el H0.
left.
ass.
intro.
apply intersection_el in H0.
conj_el H0.
right.
ass.
Qed.


Lemma intersection_of_two_unit_sets: ∀A. ({`A} ∩ {`A}) = {`A}.
intro A.
apply ZF1_extension.
intros x.
split.
intro.
take intersection_el _ _ _ H.
left H0.
apply H1.
intro.
apply intersection_in.
split.
apply H.
apply H.
Qed.

Lemma relative_complement_el: ∀A. ∀B. ∀x. 
(x ∈ (A - B)) ->  (x ∈ A) ∧ (x ∉ B).
intros A B x.
intro.
extract_iota ((A - B)) H.
take iota_prop x.
left H0.
take H1 H.
apply H2.
Qed.

Lemma relative_complement_in: ∀A. ∀B. ∀x. 
((x ∈ A) ∧ (x ∉ B) -> x ∈ (A - B)).
intros A B x.
intro.
extract_iota_from_goal ((A - B)).
take iota_prop x.
right H0.
take H1 H.
apply H2.
Qed.

Lemma pair_el: ∀A. ∀B. ∀x. (x ∈ {A, B}) -> (x = A) ∨ (x = B).
intros A B x.
intro.
extract_iota ({A, B}) H.
take iota_prop x.
left H0.
take H1 H.
apply H2.
Qed.

Lemma pair_in: ∀A. ∀B. ∀x. ((x = A) ∨ (x = B)) -> (x ∈ {A, B}).
intros A B x.
intro.
extract_iota_from_goal ({A, B}).
take iota_prop x.
right H0.
take H1 H.
apply H2.
Qed.


Lemma unit_set_el: ∀A. ∀x. (x ∈ {`A}) -> x = A.
intros A x.
apply element_of_unit_set.
Qed.

Lemma unit_set_in: ∀A. ∀x. (x = A) -> (x ∈ {`A}).
intros A x H.
repl_in_goal H.
apply every_set_is_in_unit_set.
Qed.

(* Exercise 4.4  *)
Goal ∀A. ((A ∩ ∅) = ∅).
intro A.
apply ZF1_extension.
intro x.
split.
intro.
apply intersection_el in H.
both_old H.
apply H1.
intro.
take any_set_in_empty_set_causes_contradiction H.
apply H0.
Qed.

Goal ∀A. ((A ∪ ∅) = A).
intro A.
apply ZF1_extension.
intro x.
split.
intro.
apply union_el in H.
apply (disj_el _ _ _ H).
intro.
ass.
intro.
take any_set_in_empty_set_causes_contradiction H0.
apply H1.
intro.
apply union_in.
left.
ass.
Qed.

Lemma empty_set_el: ∀A. A ∉ ∅.
intro A.
intro.
take any_set_in_empty_set_causes_contradiction H.
apply H0.
Qed.

Lemma empty_set_in: ∀A. ⊥ -> (A ∈ ∅).
intro A.
intro.
apply H.
Qed.

Goal ∀A. ((A - ∅) = A).
intro A.
apply ZF1_extension.
intro x.
split.
intro.
apply relative_complement_el in H.
left H.
ass.
intro.
apply relative_complement_in.
split.
ass.
apply empty_set_el.
Qed.

Goal ∀A. ((A - A) = ∅).
intro A.
apply ZF1_extension.
intro x.
split.
intro.
apply relative_complement_el in H.
both_old H.
take H1 H0.
apply H2.
intro.
take empty_set_el x H.
apply H0.
Qed.

Goal ∀A. ((∅ - A) = ∅).
intro A.
apply ZF1_extension.
intro x.
split.
intro.
apply relative_complement_el in H.
left H.
apply H0.
intro.
take empty_set_el x H.
apply H0.
Qed.

(* Exercise 4.5 *)

Goal ((∅ ∩ {`∅}) = ∅).
apply ZF1_extension.
intro x.
split.
intro.
extract_iota ({`∅}) H.
extract_iota ((∅ ∩ s)) H.
take iota_prop x.
take iota_prop0 x.
left H1.
take H2 H.
left H3.
apply H4.
intro.
take any_set_in_empty_set_causes_contradiction H.
apply H0.
Qed.

Goal (({`∅} ∩ {`∅}) = {`∅}).
apply intersection_of_two_unit_sets.
Qed.


Goal (({∅, {`∅}} - ∅) = {∅, {`∅}}).
apply ZF1_extension.
intro x.
split.
intro.
apply relative_complement_el in H.
left H.
right H.
apply pair_el in H0.
apply (disj_el _ _ _ H0).
intro.
repl_in_goal H2.
apply set_in_unord_pair_1.
intro.
repl_in_goal H2.
apply set_in_unord_pair_2.
intro.
apply relative_complement_in.
split.
apply H.
intro.
take (@any_set_in_empty_set_causes_contradiction x).
take H1 H0.
ass.
Qed.


Goal (({∅, {`∅}} - {`∅}) = {`{`∅}}).
apply ZF1_extension.
intro x.
split.
intro.
apply relative_complement_el in H.
both_old H.
apply pair_el in H0.
apply (disj_el _ _ _ H0).
intro.
repl H2 H1.
take every_set_is_in_unit_set ∅.
take H3 H4.
apply H5.
intro.
apply unit_set_in.
apply H2.
intro.
apply relative_complement_in.
split.
apply unit_set_el in H.
repl_in_goal H.
apply set_in_unord_pair_2.
apply unit_set_el in H.
repl_in_goal H.
intro.
apply unit_set_el in H0.
take extension_backwards H0 ∅.
left H1.
take eq_refl ∅.
take unit_set_in _ _ H3.
take H2 H4.
take (any_set_in_empty_set_causes_contradiction H5).
apply H6.
Qed.

Goal (({∅, {`∅}} - {`{`∅}}) = {`∅}).
apply ZF1_extension.
intro x.
split.
intro.
apply relative_complement_el in H.
both_old H.
apply pair_el in H0.
apply (disj_el _ _ _ H0).
intro.
repl_in_goal H2.
apply every_set_is_in_unit_set.
intro.
take unit_set_in _ _ H2.
take H1 H3.
apply H4.
intro.
apply relative_complement_in.
split.
apply pair_in.
apply unit_set_el in H.
left.
ass.
apply unit_set_el in H.
intro.
apply unit_set_el in H0.
repl H H0.
apply extension_backwards in H1.
take H1 ∅.
right H2.
apply (@any_set_in_empty_set_causes_contradiction ∅).
apply H3.
apply every_set_is_in_unit_set.
Qed.

Lemma ac_el: ∀A. ∀x. (x ∈ ac A) -> (x ∉ A).
intros A x H.
extract_iota (ac A) H.
take iota_prop x.
left H0.
apply H1.
apply H.
Qed.

Lemma ac_in: ∀A. ∀x. (x ∉ A) -> (x ∈ ac A).
intros A x H.
extract_iota_from_goal (ac A).
take iota_prop x.
right H0.
apply H1.
apply H.
Qed.

Lemma ac_el_alt: ∀A. ∀x. (x ∉ ac A) -> (x ∈ A).
intros A x H.
extract_iota (ac A) H.
take iota_prop x.
left H0.
right H0.
clear H0.
take exc_thrd (x ∈ A).
apply (disj_el _ _ _ H0).
intro.
ass.
intro.
take H2 H3.
take H H4.
apply H5.
Qed.

(* Exercise 4.6 a *)
Goal ∀A. ∀B. ((A ⊆ B) -> (ac A) ⊇ (ac B)).
intros A B H.
intros x H2.
extract_iota (ac B) H2.
take iota_prop x.
left H0.
take H1 H2.
apply ac_in.
take H x.
take contrapositive H4.
apply H5.
apply H3.
Qed.

Goal ∀A. ∀B. ((ac A) ⊇ (ac B)) -> ((A ∪ B) = B).
intros A B H.
apply ZF1_extension.
intros x.
split.
intro.
apply union_el in H0.
apply (disj_el _ _ _ H0).
intro.
take H x.
take contrapositive H2.
apply ac_el_alt.
apply H3.
intro.
apply ac_el in H4.
apply H4.
apply H1.
intro.
apply H1.
intro.
apply union_in.
right.
apply H0.
Qed.

Lemma eq_el_1: ∀A. ∀B. (A = B) -> ∀x. x ∈ A -> x ∈ B.
intros A B H x.
intro.
take extension_backwards H.
take H1 x.
left H2.
take H3 H0.
apply H4.
Qed.

Lemma eq_el_2: ∀A. ∀B. (A = B) -> ∀x. x ∈ B -> x ∈ A.
intros A B H x.
intro.
take extension_backwards H.
take H1 x.
right H2.
take H3 H0.
apply H4.
Qed.

Lemma eq_in: ∀A. ∀B. A ⊆ B -> B ⊆ A -> A = B.
intros A B H.
apply extensionality_for_subsets.
ass.
Qed.

Goal ∀A. ∀B. ((A ∪ B) = B) -> ((A ∩ B) = A).
intros A B H.
apply ZF1_extension.
intros x.
split.
intro.
apply intersection_el in H0.
left H0.
apply H1.
intro.
apply intersection_in.
split.
apply H0.
apply eq_el_1 in H.
apply H.
apply union_in.
left.
apply H0.
Qed.

Goal ∀A. ∀B. ((A ∩ B) = A) -> (A ⊆ B).
intros A B H x H2.
apply eq_el_2 in H.
take H x H2.
apply intersection_el in H0.
right H0.
ass.
Qed.

(* Exercise 4.6 b *)
Goal ∀A. ∀B. ((A ∩ B) = ∅) -> (A ⊆ ac B).
intros A B H x H2.
apply ac_in.
intro.
apply eq_el_1 in H.
take H x.
apply (@any_set_in_empty_set_causes_contradiction x).
apply H1.
apply intersection_in.
split.
ass.
ass.
Qed.

Goal ∀A. ∀B. (A ⊆ ac B) -> (B ⊆ ac A).
intros A B H x H2.
apply ac_in.
intro.
take H x H0.
apply ac_el in H1.
apply H1.
ass.
Qed.


Goal ∀A. ∀B. (B ⊆ ac A) -> ((A ∩ B) = ∅) .
intros A B H.
apply eq_in.
intros x H1.
apply intersection_el in H1.
both_old H1.
take H x H2.
apply ac_el in H3.
apply H3.
ass.
intros x H2.
apply abs_el.
apply (empty_set_el x).
ass.
Qed.

Lemma u_in: ∀A. A ∈ U.
intro A.
extract_iota_from_goal U.
take iota_prop {`A} A.
apply H.
apply unit_set_in.
apply eq_refl.
Qed.

Lemma impl_in_tauto (H: Prop): H ⇒ H.
intro.
apply H0.
Qed.


(* Exercise 4.6 c *)
Goal ∀A. ∀B. ((A ∪ B) = U) -> (ac A ⊆ B) .
intros A B H x H2.
apply ac_el in H2.
apply eq_el_2 in H.
take u_in x.
take H x H0.
apply union_el in H1.
apply (disj_el _ _ _ H1).
intro.
apply H2.
ass.
apply impl_in_tauto.
Qed.

Goal ∀A. ∀B. (ac A ⊆ B) -> (ac B ⊆ A).
intros A B H x H2.
apply ac_el in H2.
take H x.
take contrapositive H0.
take H1 H2.
apply ac_el_alt.
apply H3.
Qed.

Goal ∀A. ∀B. (ac B ⊆ A) -> (A ∪ B) = U.
intros A B H.
apply eq_in.
intros x H2.
apply u_in.
intros x H3.
apply union_in.
take H x.
take exc_thrd (x ∈ B).
apply (disj_el _ _ _ H1).
intro.
right.
ass.
intro.
apply ac_in in H2.
take H0 H2.
left.
ass.
Qed.

(* My first actual iotaless success*)
Theorem check_iotaless: ∃1 e. (∀ x . x ∉ e) ∧
∀A. ∀B. (B ⊆ ac A) -> ((A ∩ B) = e).
apply ex_unique_in.
apply empty_set_unique.
intros e H.
intros A B H2.
apply eq_in.
intro g.
intro.
apply intersection_el in H0.
both_old H0.
take H2 g H3.
apply ac_el in H4.
apply abs_el.
apply H4.
apply H1.
intros g H3.
take H g.
apply abs_el.
apply H0.
apply H3.
Qed.

Theorem union_in_1: 
∀ A . (∀ B . (∀ x . (x ∈ A) -> x ∈ (A ∪ B))).
intros A B x H.
take disj_in_1 (x ∈ A) (x ∈ B) H.
apply union_in.
ass.
Qed.

Theorem union_in_2: 
∀ A . (∀ B . (∀ x . (x ∈ B) -> x ∈ (A ∪ B))).
intros A B x H.
take disj_in_2 (x ∈ A) (x ∈ B) H.
apply union_in.
ass.
Qed.

(* Exercise 4.7 *)
Theorem union_intersection_assoc: 
∀A. ∀B. ∀C. ((((A ∩ B) ∪ C) = (A ∩ (B ∪ C))) ⇔ (C ⊆ A)) .
intros A B C.
split.
intro.
intro x.
intro.
apply eq_el_1 in H.
take H x.
take union_in_2 (A ∩ B) C x H0.
take H1 H2.
take intersection_el _ _ _ H3.
left H4.
ass.
intro.
apply eq_in.
intro x.
intro.
take union_el _ _ _ H0. 
apply (disj_el _ _ _ H1).
intro.
apply intersection_el in H2.
left H2.
right H2.
take union_in_1 B C x H4.
apply intersection_in.
split.
ass.
ass.
intro.
take H x H2.
take union_in_2 B C x H2.
apply intersection_in.
split.
ass.
ass.
intros x.
intro.
take intersection_el _ _ _ H0.
both_old H1.
apply union_in.
apply union_el in H3.
apply (disj_el _ _ _ H3).
intro.
left.
apply intersection_in.
split.
ass.
ass.
intro.
right.
ass.
Qed.

(* Exercise 4.8 *)
Theorem relative_complement_distr: 
∀A. ∀B. ∀C. (((A-B)-C) = ((A-C) - (B-C))) .
intros A B C.
apply eq_in.
intro x.
intro.
apply relative_complement_in.
split.
apply relative_complement_el in H.
apply relative_complement_in.
split.
left H.
apply relative_complement_el in H0.
left H0.
ass.
right H.
ass.
apply relative_complement_el in H.
both_old H.
apply relative_complement_el in H0.
both_old H0.
intro.
apply relative_complement_el in H4.
left H4.
apply H3.
ass.
intro x.
intro.
apply relative_complement_el in H.
both_old H.
apply relative_complement_el in H0.
both_old H0.
apply relative_complement_in.
split.
apply relative_complement_in.
split.
ass.
intro.
apply H1.
apply relative_complement_in.
split.
ass.
ass.
ass.
Qed.

(* Exercises 4.9 a b, 4.10, 4.11 - did them on paper *)

Lemma symmetric_difference_el: ∀A. ∀B. ∀x. x ∈ (A + B) ->
((x ∈ A) ∧ (x ∉ B)) ∨ ((x ∈ B) ∧ (x ∉ A)).
intros A B x H.
unfold symmetric_difference in H.
apply union_el in H.
apply (disj_el _ _ _ H).
intro.
apply relative_complement_el in H0.
left.
ass.
intro.
apply relative_complement_el in H0.
right.
ass.
Qed.

Lemma symmetric_difference_in: ∀A. ∀B. ∀x.
((x ∈ A) ∧ (x ∉ B)) ∨ ((x ∈ B) ∧ (x ∉ A)) -> (x ∈ (A + B)).
intros A B x H.
apply (disj_el _ _ _ H).
intro.
unfold symmetric_difference.
apply union_in.
left.
apply relative_complement_in.
ass.
intro.
unfold symmetric_difference.
apply union_in.
right.
apply relative_complement_in.
ass.
Qed.


(* Exercises 4.9 c *)
Theorem symmetric_difference_algebra: 
∀A. (((A + A) = ∅) ∧ ((A + ∅) = A)).
intros A.
split.
apply eq_in.
intros x H.
apply symmetric_difference_el in H.
apply (disj_el _ _ _ H).
intro.
both_old H0.
apply H2.
ass.
intro.
both_old H0.
apply H2.
ass.
intros x H.
apply abs_el.
apply (@any_set_in_empty_set_causes_contradiction x).
ass.
apply eq_in.
intros x H.
unfold symmetric_difference in H.
apply union_el in H.
apply (disj_el _ _ _ H).
intro.
apply relative_complement_el in H0.
left H0.
ass.
intro.
apply relative_complement_el in H0.
left H0.
apply empty_set_el in H1.
apply H1.
intros x H.
apply symmetric_difference_in.
left.
split.
ass.
apply empty_set_el.
Qed.

Theorem symmetric_difference_eq_to_empty_set: 
∀A. ((A + A) = ∅).
intros A.
take symmetric_difference_algebra A.
left H.
apply H0.
Qed.

Theorem symmetric_difference_with_empty_set: 
∀A. ((A + ∅) = A).
intros A.
take symmetric_difference_algebra A.
right H.
apply H0.
Qed.

(* Exercises 4.11 - a - valid*)
Goal ∀A. ∀B. ∀C. (((A ∩ B) ⊆ (ac C)) ∧ ((A ∪ C) ⊆ B)) -> 
((A ∩ C)) = ∅.
intros A B C H.
apply eq_in.
intros x H2.
apply intersection_el in H2.
both_old H2.
apply abs_el.
both_old H.
take H3 x.
take H4 x.
take union_in_1 A C x H0.
take H6 H7.
take conj_in _ _ H0 H8.
take intersection_in A B x H9.
take H5 H10.
apply ac_el in H11.
apply H11.
ass.
intros x H2.
apply abs_el.
take empty_set_el x H2.
ass.
Qed. 

Lemma empty_set_is_subset_of_any_iota: ∀A. (∅ ⊆ A).
intros A x H.
apply abs_el.
apply (any_set_in_empty_set_causes_contradiction H).
Qed.

(* Exercises 4.11 - b - not valid*)
Goal ¬(∀A. ∀B. ∀C. ((A ⊆ (ac (B ∪ C))) ∧ (B ⊆ (ac A ∪ C))) -> B = ∅).
intro.
take (H ∅ {`∅} ∅).
apply (unit_set_never_equals_to_empty_set ∅).
apply H0.
split.
apply empty_set_is_subset_of_any_iota.
intros x H1.
apply element_of_unit_set in H1.
apply union_in.
left.
apply ac_in.
apply empty_set_el.
Qed.

End AbsoluteComplementation.

Ltac disj H := 
let H_name := fresh "H" in
apply (disj_el _ _ _ H); intro H_name; move H_name before H; clear H.

(* Theorem 5.1 - 1 *)
Lemma union_assoc: ∀A. ∀B. ∀C. (A ∪ (B ∪ C)) = ((A ∪ B) ∪ C). 
intros A B C.
apply eq_in.
intros x H.
apply union_in.
apply union_el in H.
apply (disj_el _ _ _ H).
intro.
left.
apply union_in_1.
ass.
intro.
apply union_el in H0.
disj H0.
take union_in_2 A B x H1.
left.
ass.
right.
ass.
intros x H.
apply union_el in H.
disj H.
apply union_el in H0.
disj H0.
apply union_in_1.
ass.
apply union_in_2.
apply union_in_1.
ass.
apply union_in_2.
apply union_in_2.
ass.
Qed.

Ltac eq_in :=
let x := fresh "x" in
let H := fresh "H" in
apply eq_in; intros x H.

(* Theorem 5.1 - 1' *)
Lemma intersection_assoc: ∀A. ∀B. ∀C. (A ∩ (B ∩ C)) = ((A ∩ B) ∩ C). 
intros A B C.
eq_in.
apply intersection_in.
apply intersection_el in H.
both_old H.
apply intersection_el in H1.
both_old H1.
split.
apply intersection_in.
split; ass.
ass.
apply intersection_in.
split.
apply intersection_el in H.
both_old H.
apply intersection_el in H0.
both_old H0.
ass.
apply intersection_el in H.
both_old H.
apply intersection_el in H0.
both_old H0.
apply intersection_in.
split; ass.
Qed.

(* Theorem 5.1 - 2 *)
Lemma union_comm: ∀A. ∀B. (A ∪ B) = (B ∪ A). 
intros A B.
eq_in.
apply union_in.
apply union_el in H.
disj H.
right.
ass.
left.
ass.
apply union_in.
apply union_el in H.
disj H.
right.
ass.
left.
ass.
Qed.

(* Theorem 5.1 - 2' *)
Lemma intersection_comm: ∀A. ∀B. (A ∩ B) = (B ∩ A). 
intros A B.
eq_in.
apply intersection_in.
apply intersection_el in H.
both_old H.
split.
ass.
ass.
apply intersection_in.
split.
apply intersection_el in H.
both_old H.
ass.
apply intersection_el in H.
both_old H.
ass.
Qed.

(* Theorem 5.1 - 3 *)
Lemma union_intersection_distr: ∀A. ∀B. ∀C. 
(A ∪ (B ∩ C)) = ((A ∪ B) ∩ (A ∪ C)). 
intros A B C.
eq_in.
apply intersection_in.
split.
apply union_in.
apply union_el in H.
disj H.
left.
ass.
apply intersection_el in H0.
both_old H0.
right.
ass.
apply union_el in H.
disj H.
apply union_in.
left.
ass.
apply intersection_el in H0.
both_old H0.
apply union_in.
right.
ass.
apply union_in.
apply intersection_el in H.
both_old H.
apply union_el in H0, H1.
disj H0.
left.
ass.
disj H1.
left.
ass.
right.
apply intersection_in.
split; ass.
Qed.

Ltac both H := left H; right H; clear H.

(* Theorem 5.1 - 3' *)
(* exercise 5.1*)
Lemma intersection_union_distr: ∀A. ∀B. ∀C. 
(A ∩ (B ∪ C)) = ((A ∩ B) ∪ (A ∩ C)). 
intros A B C.
eq_in.
apply intersection_el in H.
both H.
apply union_el in H1.
disj H1.
apply union_in.
left.
apply intersection_in.
split; ass.
apply union_in.
right.
apply intersection_in.
split; ass.
apply union_el in H.
disj H.
apply intersection_el in H0.
both H0.
apply intersection_in.
split.
ass.
apply union_in.
left.
ass.
apply intersection_el in H0.
both H0.
apply intersection_in.
split.
ass.
apply union_in.
right.
ass.
Qed.

(* Theorem 5.1 - 4 *)
Lemma empty_set_absorption: ∀A. ((A ∪ ∅) = A). 
intro A.
eq_in.
apply union_el in H.
disj H.
ass.
apply empty_set_el in H0.
apply H0.
apply union_in.
left.
ass.
Qed.

(* Theorem 5.1 - 4' *)
(* exercise 5.1*)
Lemma universal_set_absorption: ∀A. ∀U. (A ⊆ U) -> ((A ∩ U) = A). 
intros A U.
intro H.
eq_in.
apply intersection_el in H0.
left H0.
ass.
apply intersection_in.
split.
ass.
apply (H x).
ass.
Qed.

Definition rc_el := relative_complement_el.
Definition rc_in := relative_complement_in.

(* Theorem 5.1 - 5 *)
Lemma union_with_complement: ∀A. ∀U. ((A ⊆ U) -> ((A ∪ (U - A)) = U)). 
intros A U H.
eq_in.
apply union_el in H0.
disj H0.
apply (H x).
ass.
apply rc_el in H1.
both H1.
ass.
apply union_in.
take exc_thrd (x ∈ A).
disj H1.
left.
ass.
right.
apply rc_in.
split; ass.
Qed.

(* Theorem 5.1 - 5' *)
(* exercise 5.1 *)
Lemma intersection_with_complement: ∀A. ∀U. ((A ⊆ U) -> ((A ∩ (U - A)) = ∅)). 
intros A U H.
eq_in.
apply intersection_el in H0.
both H0.
apply rc_el in H2.
both H2.
apply abs_el.
apply H3.
ass.
apply empty_set_el in H0.
apply H0.
Qed.

(* Theorem 5.2 - 6 *)
Lemma union_with_empty_set: ∀B. (∀A. ((A ∪ B) = A)) -> B = ∅.
intros B H.
eq_in.
apply abs_el.
take H ∅.
apply eq_el_1 in H1.
take H1 x.
take empty_set_el x.
apply H3.
apply H2.
apply union_in.
right.
ass.
apply (empty_set_el x).
ass.
Qed.

(* Theorem 5.2 - 6' *)
Lemma intersection_with_universal_set: ∀U. 
(∀B. (B ⊆ U) -> (∀A. ((A ∩ B) = A)) -> B = U).
intros U B H H2.
eq_in.
apply (H x H0).
take H2 {`x}.
apply eq_el_2 in H1.
take H1 x.
take every_set_is_in_unit_set x.
take H3 H4.
apply intersection_el in H5.
both H5.
ass.
Qed.

(* Theorem 5.2 - 7 and 7' *)
Lemma one_set_is_complement_of_another: ∀U. 
∀A. ∀B. (A ⊆ U) -> (B ⊆ U) -> 
((((A ∪ B) = U) ∧ ((A ∩ B) = ∅)) -> B = (U - A)).
intros U A B u1 u2 H.
both H.
eq_in.
apply rc_in.
split.
apply (u2 x H).
intro.
take conj_in _ _ H2 H.
take intersection_in A B x H3.
take eq_el_1 _ _ H1 x H4.
apply empty_set_el in H5.
ass.
apply rc_el in H.
both H.
apply eq_el_2 in H0.
take H0 x H2.
apply union_el in H.
disj H.
apply abs_el.
apply H3.
ass.
ass.
Qed.

Lemma rc_el_neg: ∀A. ∀B. ∀x. (x ∉ (A - B)) -> (x ∉ A) ∨ (x ∈ B).
intros A B x H.
extract_iota (A - B) H.
take iota_prop x.
right H0.
take contrapositive H1 H.
apply deMorganNotAnd in H2.
disj H2.
left.
ass.
right.
apply DN_el.
ass.
Qed.

Lemma rc_in_neg: ∀A. ∀B. ∀x. ((x ∉ A) ∨ (x ∈ B)) -> x ∉ (A - B).
intros A B X H.
disj H.
intro.
apply rc_el in H.
left H.
apply (H0 H1).
intro.
apply rc_el in H.
right H.
apply (H1 H0).
Qed.



Print Assumptions rc_el_neg. (* not constructive*)

(* Theorem 5.2 - 8 and 8' *)
Lemma double_complement: ∀U. ∀A. (A ⊆ U) -> (U - (U - A)) = A.
intros U A H.
eq_in.
apply rc_el in H0.
both H0.
apply rc_el_neg in H2.
disj H2.
apply H0.
ass.
ass.
apply rc_in.
split.
apply (H x H0).
intro.
apply rc_el in H1.
both H1.
apply (H3 H0).
Qed.

(* Theorem 5.2 - 9 *)
Lemma complement_of_empty_set: 
∀U. (U - ∅) = U.
intro U.
apply eq_in.
intros x H.
apply rc_el in H.
left H.
ass.
intros x H.
apply rc_in.
split.
ass.
apply (empty_set_el x).
Qed.

(* Theorem 5.2 - 9' *)
Lemma complement_of_universal_set: 
∀U. (U - U) = ∅.
intro U.
apply eq_in.
intros x H.
apply abs_el.
apply rc_el in H.
both H.
apply (H1 H0).
intros x H.
apply rc_in.
split.
apply (empty_set_el x).
ass.
apply (empty_set_el x).
ass.
Qed.

(* Theorem 5.2 - 10 *)
Lemma union_idempotent: ∀A. ((A ∪ A) = A).
intros A.
apply eq_in.
intros x H.
apply union_el in H.
disj H.
ass.
ass.
intros x H.
apply union_in.
left.
ass.
Qed.

(* Theorem 5.2 - 10' *)
Lemma intersection_idempotent_old: ∀A. ((A ∩ A) = A).
intro A.
apply eq_in.
intros x H.
apply intersection_el in H.
left H.
ass.
intros x H.
apply intersection_in.
split; ass.
Qed.

(* Theorem 5.2 - 11 *)
Lemma union_with_universal_set: ∀A. ∀U.
(A ⊆ U) -> ((A ∪ U) = U).
intros A U H.
apply eq_in.
intros x H2.
apply union_el in H2.
disj H2.
apply (H x H0).
ass.
intros x H2.
apply union_in.
right.
ass.
Qed.

(* Theorem 5.2 - 11' *)
Lemma intersection_with_empty_set: ∀A. ((A ∩ ∅) = ∅).
intros A.
apply eq_in.
intros x H.
apply intersection_el in H.
both H.
ass.
intros x H.
apply (empty_set_el x).
ass.
Qed.


(* Theorem 5.2 - 12 *)
Lemma absorption_law_union_intersection: ∀A. ∀B. ((A ∪ (A ∩ B)) = A).
intros A B.
apply eq_in.
intros x H.
apply union_el in H.
disj H.
ass.
apply intersection_el in H0.
left H0.
ass.
intros x H.
apply union_in.
left.
ass.
Qed.

(* Theorem 5.2 - 12' *)
Lemma absorption_law_intersection_union: ∀A. ∀B. ((A ∩ (A ∪ B)) = A).
intros A B.
eq_in.
apply intersection_el in H.
left H.
ass.
apply intersection_in.
split.
ass.
apply union_in.
left.
ass.
Qed.

Lemma union_el_neg: ∀A. ∀B. ∀x. (x ∉ (A ∪ B)) -> (x ∉ A) ∧ (x ∉ B).
intros A B x H.
split.
intro.
take union_in_1 A B x H0.
apply (H H1).
intro.
take union_in_2 A B x H0.
apply (H H1).
Qed.

Lemma union_in_neg: ∀A. ∀B. ∀x. ((x ∉ A) ∧ (x ∉ B)) -> (x ∉ (A ∪ B)).
intros A B x H.
both H.
intro.
apply union_el in H.
disj H.
apply (H0 H2).
apply (H1 H2).
Qed.

Lemma intersection_el_neg: ∀A. ∀B. ∀x. (x ∉ (A ∩ B)) 
-> (x ∉ A) ∨ (x ∉ B).
intros A B x H.
extract_iota (A ∩ B) H.
take iota_prop x.
right H0.
take contrapositive H1 H.
apply deMorganNotAnd in H2.
ass.
Qed.

Lemma intersection_in_neg: ∀A. ∀B. ∀x. ((x ∉ A) ∨ (x ∉ B)) 
-> (x ∉ (A ∩ B)).
intros A B x H.
extract_iota_from_goal (A ∩ B).
take iota_prop x.
left H0.
take contrapositive H1.
apply H2.
intro.
both H3.
disj H.
apply (H3 H4).
apply (H3 H5).
Qed.

(* Theorem 5.2 - 13 *)
Lemma deMorganNotUnion: ∀A. ∀B. ∀U. (A ⊆ U) -> (B ⊆ U) ->
((U - (A ∪ B)) = ((U - A) ∩ (U - B))).
intros A B U u1 u2.
eq_in.
apply rc_el in H.
both H.
apply union_el_neg in H1.
both H1.
apply intersection_in.
split.
apply rc_in.
split.
ass.
ass.
apply rc_in.
split; ass.
apply intersection_el in H.
both H.
apply rc_el in H0, H1.
both H0.
both H1.
apply rc_in.
split.
ass.
apply union_in_neg.
split; ass.
Qed.

(* Theorem 5.2 - 13' *)
Lemma deMorganNotIntersection: ∀A. ∀B. ∀U. (A ⊆ U) -> (B ⊆ U) ->
((U - (A ∩ B)) = ((U - A) ∪ (U - B))).
intros A B U u1 u2.
eq_in.
apply rc_el in H.
both H.
apply intersection_el_neg in H1.
apply union_in.
disj H1.
left.
apply rc_in.
split; ass.
right.
apply rc_in.
split; ass.
apply union_el in H.
apply rc_in.
split.
disj H.
apply rc_el in H0.
both H0.
ass.
apply rc_el in H0.
both H0.
ass.
disj H.
apply rc_el in H0.
both H0.
intro.
apply intersection_el in H0.
both H0.
apply (H1 H2).
apply rc_el in H0.
both H0.
intro.
apply intersection_el in H0.
both H0.
apply (H1 H3).
Qed.

(* Theorem 5.3 (I) -> (II) *)
Lemma subset_el_intersection: ∀A. ∀B. (A ⊆ B) -> ((A ∩ B) = A).
intros A B H.
eq_in.
apply intersection_el in H0.
left H0.
ass.
apply intersection_in.
split.
ass.
apply (H x H0).
Qed.

(* Theorem 5.3 (I) -> (III) *)
Lemma subset_el_union: ∀A. ∀B. (A ⊆ B) -> ((A ∪ B) = B).
intros A B H.
eq_in.
apply union_el in H0.
disj H0.
apply (H x H1).
ass.
apply union_in.
right.
ass.
Qed.

(* Theorem 5.3 (II) -> (III) *)
Goal ∀A. ∀B. ((A ∩ B) = A) -> ((A ∪ B) = B). 
intros A B H.
eq_in.
apply union_el in H0.
disj H0.
apply eq_el_2 in H.
take H x H1.
apply intersection_el in H0.
right H0.
ass.
ass.
apply union_in.
right.
ass.
Qed.

(* Theorem 5.3 (III) -> (I) *)
Lemma subset_in_union: ∀A. ∀B. ((A ∪ B) = B) -> (A ⊆ B).
intros A B H.
intros x H2.
apply eq_el_1 in H.
take union_in_1 A B x H2.
take H x H0.
ass.
Qed.


Lemma eq_el_symm_diff: ∀A. ∀B. (A = B) -> ((A + B) = ∅).
intros A B H.
eq_in.
repl H H0.
take symmetric_difference_eq_to_empty_set A.
apply eq_el_1 in H2.
take H2 x H1.
ass.
apply empty_set_el in H0.
apply H0.
Qed.

Lemma symmetric_difference_el_neg: ∀A. ∀B. ∀x. x ∉ (A + B) ->
((x ∉ A) ∨ (x ∈ B)) ∧ ((x ∉ B) ∨ (x ∈ A)).
intros A B x H.
unfold symmetric_difference in H.
apply union_el_neg in H.
both H.
apply rc_el_neg in H0, H1.
disj H0.
disj H1.
split.
left.
ass.
left.
ass.
apply (H H0).
disj H1.
apply (H0 H).
split.
right.
ass.
right.
ass.
Qed.

Lemma symmetric_difference_symm: ∀A. ∀B. (A + B) = (B + A).
intros A B.
eq_in.
apply symmetric_difference_el in H.
apply disj_comm in H.
apply symmetric_difference_in.
apply H.
apply symmetric_difference_el in H.
apply disj_comm in H.
apply symmetric_difference_in.
apply H.
Qed.

Lemma eq_in_symm_diff: ∀A. ∀B. ((A + B) = ∅) -> (A = B).
intros A B H.
eq_in.
apply eq_el_1 in H.
take H x.
take contrapositive H1.
take (empty_set_el x).
take H2 H3.
apply symmetric_difference_el_neg in H4.
both H4.
disj H5.
disj H6.
apply (H4 H0).
apply (H4 H0).
disj H6.
ass.
ass.
take symmetric_difference_symm A B.
take eq_subs (fun g => g = ∅) _ _ H1 H.
clear H1 H.
rename H2 into H.
apply eq_el_1 in H.
take H x.
take contrapositive H1.
take (empty_set_el x).
take H2 H3.
apply symmetric_difference_el_neg in H4.
both H4.
disj H5.
disj H6.
apply (H4 H0).
apply (H4 H0).
disj H6.
ass.
ass.
Qed.

(* skipped equasion theory because I don't have structural induction yet
https://en.wikipedia.org/wiki/Knaster%E2%80%93Tarski_theorem maybe this
And good understanding of the relation theory
Can also do in Coq, but for now it seems not very comfortable
*)


Ltac repl_forward eq_hyp target_hyp :=
let symmetric_eq := fresh "symmetric_eq" in
let target_hyp_repl := fresh target_hyp in
match type of eq_hyp with
| eq ?a ?b => match type of target_hyp with
| context g[ a ] => let my_func := (context g [b]) in 
pattern a in target_hyp;
match type of target_hyp with
|?func ?arg => pose proof (eq_subs func
a b eq_hyp target_hyp):my_func as target_hyp_repl;
move target_hyp_repl before target_hyp;
clear target_hyp; 
rename target_hyp_repl into target_hyp
| _ => fail "error inside nested matches"
end
end
end.

Ltac repl_backward eq_hyp target_hyp :=
swap_eq eq_hyp; repl_forward eq_hyp target_hyp; swap_eq eq_hyp.

Ltac repl_in_goal eq_hyp :=
let symmetric_eq := fresh "symmetric_eq" in
let target_hyp_repl := fresh "target_hyp_repl" in
match type of eq_hyp with
| eq ?a ?b =>
pattern a;
match goal with
|- ?func ?arg => 
pose proof eq_symm _ _ eq_hyp as symmetric_eq;
apply (eq_subs func b a symmetric_eq);
clear symmetric_eq
| _ => fail "error inside goal matching"
end
end.

Ltac repl_in_goal_backward eq_hyp :=
let target_hyp_repl := fresh "target_hyp_repl" in
match type of eq_hyp with
| eq ?a ?b =>
pattern b;
match goal with
|- ?func ?arg => 
apply (eq_subs func a b eq_hyp)
| _ => fail "error inside goal matching"
end
end.

Tactic Notation "repl" constr(eq_hyp) "in" constr(target_hyp) 
:= repl_forward eq_hyp target_hyp.

Tactic Notation "repl" "<-" constr(eq_hyp) "in" constr(target_hyp) 
:= repl_backward eq_hyp target_hyp.

Tactic Notation "repl" constr(eq_hyp)
:= repl_in_goal eq_hyp.

Tactic Notation "repl" "<-" constr(eq_hyp)
:= repl_in_goal_backward eq_hyp.

(* Exercise 5.2 *)
(* Theorem 5.2 - 6 - reusing*)
Lemma union_with_empty_set_reusing: ∀B. (∀A. ((A ∪ B) = A)) -> B = ∅.
intros B A.
take A ∅.
take empty_set_absorption B.
take union_comm B ∅.
repl H1 in H0.
repl H0 in H.
apply H.
Qed.
(* I skipped the rest 11 examples because seems boring and not very useful*)

(* Exercise 5.3 - a *)

Goal ∀A. ∀B. ∀C. ∀X. ∀Y. ∀U. (A ⊆ U) ->
((A ∩ B ∩ X) ∪ (A ∩ B ∩ C ∩ X ∩ Y) ∪ (A ∩ X ∩ (U - A))) = (A ∩ B ∩ X).
intros A B C X Y U u1.
take intersection_with_complement A U u1.
take intersection_comm A X.
repl H0.
take intersection_assoc X A (U - A).
swap_eq H1.
repl H1.
repl H.
take intersection_with_empty_set X.
repl H2.
take empty_set_absorption (A ∩ B ∩ X ∪ (A ∩ B ∩ C ∩ X ∩ Y)).
repl H3.
take absorption_law_union_intersection (A ∩ B ∩ X) (C ∩ Y).
take intersection_assoc (A ∩ B) C X.
swap_eq H5.
repl H5.
take intersection_comm C X.
repl H6.
take intersection_assoc (A ∩ B) X C.
repl H7.
take intersection_assoc (((A ∩ B) ∩ X)) C Y.
repl <- H8.
repl H4.
apply eq_refl.
Qed.

Lemma get (x: Set): ∃g. g = x.
apply (ex_in _ x).
apply eq_refl.
Qed.

Ltac get_core s n :=
let ex_hyp := fresh "ex_hyp" in
let P := fresh "P" in
pose proof get s as ex_hyp;
apply (ex_el _ ex_hyp);
intro n;
intro P; 
clear ex_hyp.

Tactic Notation "get" uconstr(s) "as" ident(n) := get_core s n.

(* Exercise 5.3 - b *)

Goal ∀A. ∀B. ∀C. ∀U. (A ⊆ U) -> (B ⊆ U)->(C ⊆ U)->
(((A ∩ B ∩ C) ∪ (((U - A) ∩ B ∩ C) ∪ (U - B) ∪ (U - C))) = U).
intros A B C U u1 u2 u3.
get (B ∩ C) as bc.
take intersection_assoc A B C.
repl <- H.
take intersection_assoc (U - A) B C.
repl <- H0.
repl <- P. 
clear H H0.
take union_assoc ((U - A) ∩ bc) (U - B) (U - C).
repl <- H.
take union_assoc (A ∩ bc) (U - A ∩ bc) ((U - B) ∪ (U - C)). 
repl H0.
take intersection_union_distr bc A (U - A).
take intersection_comm A bc.
take intersection_comm (U - A) bc.
repl H2.
repl H3.
repl <- H1.
take union_with_complement A U u1.
repl H4.
take intersection_with_universal_set U bc.
assert (bc ⊆ U).
repl P.
intros x G.
apply intersection_el in G.
left G.
apply (u2 x H6).
take H5 H6.
take universal_set_absorption bc U H6.
repl H8.
take deMorganNotIntersection B C U u2 u3.
repl <- H9.
repl <- P.
take union_with_complement bc U H6.
apply H10.
Qed.

(* Exercise 5.3 - c *)
Goal ∀A. ∀B. ∀C. ∀X. ∀U. (A ⊆ U) -> (B ⊆ U)-> (C ⊆ U) -> (X ⊆ U) ->
(((A ∩ B ∩ C ∩ (U - X)) ∪ ((U - A) ∩ C) ∪ ((U - B) ∩ C) ∪ (C ∩ X)) = C).
intros A B C X U u1 u2 u3 u4.
take intersection_comm (A ∩ B) C.
repl H.
take intersection_assoc C (A ∩ B) (U - X).
repl <- H0.
take intersection_comm (U - A) C.
repl H1.
take intersection_union_distr C ((A ∩ B) ∩ (U - X)) (U - A).
repl <- H2.
take intersection_comm (U - B) C.
repl H3.
take intersection_union_distr C ((((A ∩ B) ∩ (U - X)) ∪ (U - A))) (U - B).
repl <- H4.
take intersection_union_distr C (((((A ∩ B) ∩ (U - X)) ∪ (U - A)) ∪ (U - B))) (X).
repl <- H5.
clear H0 H1 H2 H3 H4 H5.
take intersection_with_universal_set.
get (U - X) as nX.
repl <- P.
get (U - A) as nA.
repl <- P0.
clear H H0.
get (U - B) as nB.
repl <- P1.
take union_assoc ((A ∩ B) ∩ nX) nA nB.
repl <- H.
repl P0.
repl P1.
take deMorganNotIntersection A B U u1 u2.
repl <- H0.
get ((A ∩ B)) as AuB.
repl <- P2.
take union_intersection_distr (U - AuB) AuB nX. 
take union_comm (AuB ∩ nX) (U - AuB).
repl H2.
repl H1.
take union_with_complement AuB U.
assert (AuB ⊆ U).
intros x HH.
repl P2 in HH.
apply intersection_el in HH.
left HH.
apply (u1 x H4).
take H3 H4.
take union_comm AuB (U - AuB).
repl <- H6.
repl H5.
take universal_set_absorption ((U - AuB) ∪ nX) U.
assert  (((U - AuB) ∪ nX) ⊆ U).
intros x G1.
apply union_el in G1.
disj G1.
apply rc_el in H8.
left H8.
ass.
repl P in H8.
apply rc_el in H8.
left H8.
ass.
take H7 H8.
take intersection_comm U ((U - AuB) ∪ nX).
repl H10.
repl H9.
take union_assoc (U - AuB) nX X.
repl <- H11.
repl P.
take union_with_complement X U u4.
take union_comm X (U - X).
repl <- H13.
repl H12.
take union_with_universal_set (U - AuB) U.
assert ((U - AuB) ⊆ U).
intros k G2.
apply rc_el in G2.
left G2.
ass.
take H14 H15.
repl H16.
take universal_set_absorption C U u3.
ass.
Qed.

Lemma intersection_in_subset: ∀A. ∀B. ∀U.
(A ⊆ U) -> (B ⊆ U) -> (A ∩ B) ⊆ U.
intros A B U u1 u2.
intros x H.
apply intersection_el in H.
left H.
apply (u1 x H0).
Qed.

Lemma rc_in_subset: ∀A. ∀U.
(A ⊆ U) -> ((U - A) ⊆ U).
intros A U u1.
intros x H.
apply rc_el in H.
left H.
ass.
Qed.

(* Exercise 5.3 - d - SUPER LONG
I did it with membership relation --- PERFECTLY GOOD
Skipped doing using identities
*)

Goal ∀A. ∀B. ∀C. ∀X. ∀Y. ∀U. (A ⊆ U) -> (B ⊆ U)-> (C ⊆ U) -> (X ⊆ U) -> (Y ⊆ U) ->
 (((A ∩ B) ∪ (A ∩ C) ∪ ((U - A) ∩ (U - X) ∩ Y))
    ∩ (U - ((A ∩ (U - B) ∩ C) ∪ ((U - A) ∩ (U - X) ∩ (U - Y)) ∪ ((U - A) ∩ B ∩ Y))))
  = ((A ∩ B) ∪ ((U - A) ∩ (U - B) ∩ (U - X) ∩ Y)).
intros A B C X Y U aU bU cU xU yU.
eq_in.
apply union_in.
apply intersection_el in H.
both H.
apply rc_el in H1.
both H1.
apply union_el in H0.
disj H0.
apply union_el in H1.
disj H1.
left.
ass.
take exc_thrd (x ∈ B).
disj H1.
apply intersection_el in H0.
both H0.
left.
apply intersection_in.
split.
ass.
ass.
right.
apply intersection_in.
split.
apply intersection_in.
split.
apply intersection_in.
split.
take exc_thrd (x ∈ A).
disj H1.
apply rc_in.
split.
ass.
apply intersection_el in H0.
both H0.
clear H4.
apply abs_el.
apply H2.
apply union_in.
left.
apply union_in.
left.
apply intersection_in.
split.
apply intersection_in.
split.
ass.
apply rc_in.
split.
ass.
ass.
ass.
apply rc_in.
split.
ass.
ass.
apply rc_in.
split; ass.
apply rc_in.
split.
ass.
intro.
apply intersection_el in H0.
both H0.
apply H2.
apply union_in.
left.
apply union_in.
left.
apply intersection_in.
split.
apply intersection_in.
split.
ass.
apply rc_in.
split; ass.
ass.
take exc_thrd (x ∈ Y).
disj H1.
ass.
apply abs_el.
apply H2.
apply union_in.
left.
apply union_in.
left.
apply intersection_el in H0.
both H0.
apply intersection_in.
split.
apply intersection_in.
split.
ass.
apply rc_in.
split.
ass.
ass.
ass.
apply intersection_el in H1.
both H1.
apply intersection_el in H0.
both H0.
apply rc_el in H1, H4.
both H1.
both H4.
clear H0.
right.
apply intersection_in.
split.
apply intersection_in.
split.
apply intersection_in.
split.
apply rc_in.
split; ass.
apply rc_in.
split.
ass.
intro.
apply H2.
apply union_in.
right.
apply intersection_in.
split.
apply intersection_in.
split.
apply rc_in.
split.
ass.
ass.
ass.
ass.
apply rc_in.
split; ass.
ass.
apply union_el in H.
disj H.
apply intersection_el in H0.
both H0.
apply intersection_in.
split.
apply union_in.
left.
apply union_in.
left.
apply intersection_in.
split; ass.
apply rc_in.
split.
take aU x H.
ass.
intro.
apply union_el in H0.
disj H0.
apply union_el in H2.
disj H2.
apply intersection_el in H0.
both H0.
apply intersection_el in H2.
both H2.
apply rc_el in H4.
both H4.
apply H5.
ass.
apply intersection_el in H0.
both H0.
apply intersection_el in H2.
both H2.
apply rc_el in H0.
both H0.
apply H5.
ass.
apply intersection_el in H2.
both H2.
apply intersection_el in H0.
both H0.
apply rc_el in H2.
both H2.
apply H5.
ass.
apply intersection_el in H0.
both H0.
apply intersection_el in H.
both H.
apply intersection_el in H0.
both H0.
apply rc_el in H2.
both H2.
apply rc_el in H.
both H.
apply rc_el in H3.
both H3.
clear H2 H.
apply intersection_in.
split.
apply union_in.
right.
apply intersection_in.
split.
apply intersection_in.
split.
apply rc_in.
split; ass.
apply rc_in.
split; ass.
ass.
apply rc_in.
split.
ass.
apply union_in_neg.
split.
apply union_in_neg.
split.
apply intersection_in_neg.
left.
apply intersection_in_neg.
left.
ass.
apply intersection_in_neg.
right.
apply rc_in_neg.
right.
ass.
apply intersection_in_neg.
left.
apply intersection_in_neg.
right.
ass.
Qed.


(* Exercise 5.4 -- Rework Exercise 4.9 b 
Skipped symmetric_difference_assoc because seems extremely complicated
*)
Lemma symmetric_difference_comm: ∀A. ∀B. (A + B) = (B + A).
intros A B.
unfold symmetric_difference.
take union_comm (A - B) (B - A).
apply H.
Qed.


Lemma symmetric_difference_assoc: ∀A. ∀B. ∀C.
 ((A + B) + C) = (A + (B + C)).
intros A B C.
unfold symmetric_difference.
Admitted.

(* Exercise 5.5, 5.6 
Skipped because I need lists
 *)

(* Exercise 5.7 - a*)
Goal ∀A. ∀B. (A = B) ⇔ ((A + B) = ∅).
intros A B.
split.
intros H.
apply (eq_el_symm_diff A B).
apply H.
intros H.
apply (eq_in_symm_diff A B).
apply H.
Qed.

(* Exercise 5.7 - b - Skipped, need type theory inside sets*)

(* Exercise 5.7 - c *)
Goal ∀A. ∀B. ((A = B) ∧ (A = ∅)) ⇔ ((A ∪ B) = ∅).
intros A B.
split.
intros H.
both H.
eq_in.
apply union_el in H.
disj H.
repl H1 in H2.
apply H2.
repl H1 in H0.
repl <- H0 in H2.
apply H2.
apply (abs_el).
apply (empty_set_el x).
ass.
intros H.
split.
apply eq_in.
intros x H2.
apply eq_el_1 in H.
take H x.
apply abs_el.
apply (empty_set_el x).
apply H0.
apply union_in.
left.
ass.
intros x H2.
apply eq_el_1 in H.
take H x.
apply abs_el.
apply (empty_set_el x).
apply H0.
apply union_in.
right.
ass.
eq_in.
apply eq_el_1 in H.
take H x.
apply H1.
apply union_in.
left.
ass.
apply abs_el.
apply (empty_set_el x).
ass.
Qed.

(* Exercise 5.7 - d, e - Skipped, need type theory inside sets*)

(* Exercise 5.8 - a b c - boring, can redo later with joy*)

Goal ∀A. ∀B. ∀X. ∀U. (A ⊆ U) -> (B ⊆ U)-> (X ⊆ U) ->
(U - ((A ∩ X) ∪ (B ∩ (U - X)))) = (((U - A) ∩ X) ∪ ((U - B) ∩ (U - X))).
intros A B X U aU bU xU.
eq_in.
apply rc_el in H.
both H.
apply union_el_neg in H1.
both H1.
apply intersection_el_neg in H.
apply intersection_el_neg in H2.
apply union_in.
disj H.
disj H2.
Admitted.

(* Exercise 5.9 - Skipped, need type theory inside sets*)

Definition relation_from_x_to_y (p X Y: Set):= (relation p) ∧ (p ⊆ (X × Y)).
Definition relation_from_z_to_z (p Z: Set):= ∃X. ∃Y.
(relation_from_x_to_y p X Y) ∧ ((X ∪ Y) ⊆ Z).
Definition relation_in_z (p Z: Set) := relation_from_x_to_y p Z Z.

Definition universal_relation_in_x (X: Set) := (X × X).
Definition void_relation := ∅.

Definition identity_relation_exists (X: Set): ∃1i.
(∀p. ((p ∈ i) ⇔ (∃x:: X. p = <x, x>))).
split.
take cartesian_exists_old X X.
left H.
clear H.
cbv beta in H0.
change (∃ s1. (∀ w . ((w ∈ s1) ⇔ 
(∃ x :: X . (∃ y :: X . (w = (< x, y >))))))) in H0.
apply (ex_el _ H0).
intros s1 P.
clear H0.
take ZF2_subsets (fun g => (∃ z :: X . (g = (< z, z >)))) s1.
apply (ex_el _ H).
intros s2.
intros P0.
2:{
  apply any_biimpl_set_is_no_more_than_one.
}
change (∃ s. (∀ p . ((p ∈ s) ⇔ 
(∃ x :: X . (p = (< x, x >)))))).
apply (ex_in _ s2).
intros k.
split.
intro.
take P0 k.
left H1.
take H2 H0.
right H3.
apply H4.
intro.
take P0 k.
right H1.
apply H2.
split.
take P k.
right H3.
apply H4.
apply (ex_el _ H0).
intro.
intro.
both H5.
apply (ex_in _ x).
split.
ass.
apply (ex_in _ x).
split.
ass.
ass.
apply H0.
Qed.

Definition identity_relation (X: Set): Set := ι _ (identity_relation_exists X).
Definition id (X: Set): Set := ι _ (identity_relation_exists X).

Theorem identity_relation_prop(X: Set): ∀x::X. ∀y::X. 
(<x,y> ∈ (id X)) ⇔ (x = y).
intros x x_in_X y y_in_Y.
split.
intro.
extract_iota (id X) H.
take iota_prop (< x, y >).
left H0.
take H1 H.
apply (ex_el _ H2).
intro k.
intro.
both H3.
take pair_property H5.
both H3.
swap_eq H7.
take eq_trans _ _ _ H6 H7.
apply H3.
intro.
extract_iota_from_goal  (id X).
take iota_prop (< x, y >).
right H0.
apply H1.
apply (ex_in _ x).
split.
ass.
repl_in_goal H.
apply eq_refl.
Qed.

Definition identity_relation_p(X i: Set) := (∀p. ((p ∈ i) ⇔ (∃x:: X. p = <x, x>))).


Theorem identity_relation_prop_iota_free(X: Set): ∃1i. (identity_relation_p X i) 
∧ (∀x::X. ∀y::X. (<x,y> ∈ i) ⇔ (x = y)).
apply ex_unique_in.
apply identity_relation_exists.
intro i.
intro.
intros x x_in_X y y_in_Y.
split.
intro.
take H  (< x, y >).
left H1.
take H2 H0.
apply (ex_el _ H3).
intros x0.
intro.
right H4.
take pair_property H5.
both H6.
swap_eq H8.
take eq_trans _ _ _ H7 H8.
ass.
intro.
repl_in_goal H0.
take H (< y, y >).
right H1.
apply H2.
apply (ex_in _ y).
split.
ass.
apply eq_refl.
Qed.

Ltac ex_el H :=
match type of H with
|∃ x. _ =>
let V := fresh x in
let H2 := fresh "H2" in
apply (ex_el _ H);
intros V H2;
move V before H;
move H2 before V;
clear H;
rename H2 into H
|∃1 x. _ =>
let V := fresh x in
let H2 := fresh "H2" in
let H3 := fresh "H3" in
pose proof conj_el_1 _ _ H as H3;
apply (ex_el _ H3);
intros V H2;
move V before H;
move H2 before V;
move H3 before H2;
cbv beta in H3;
clear H H3;
rename H2 into H
end.

Ltac ex_unique_el H :=
match type of H with
|∃1 x. _ =>
let V := fresh x in
let H2 := fresh "H2" in
let H3 := fresh "H3" in
let U := fresh "U" in
pose proof conj_el_1 _ _ H as H3;
pose proof conj_el_2 _ _ H as U;
apply (ex_el _ H3);
intros V H2;
move V before H;
move H2 before V;
move H3 before H2;
move U before V;
cbv beta in H3;
cbv beta in U;
clear H H3;
rename H2 into H
end.

Definition p_relatives_ex_iota(A p: Set) (p_is_rel: relation p) : 
∃1s. (∀y. (y ∈ s) ⇔ ∃x::A. <x, y> ∈ p).
split; try apply any_biimpl_set_is_no_more_than_one.
take range_exists_iota p p_is_rel.
left H.
clear H.
cbv beta in H0.
ex_el H0.
take ZF2_subsets (fun g=> (∃ x1 :: A . < x1, g > ∈ p)) x.
ex_el H.
apply (ex_in _ b).
intro y.
split.
intro.
take H y.
left H2.
take H3 H1.
right H4.
apply H5.
(*part 2*)
intro.
ex_el H1.
both H1.
take H y.
right H1.
apply H4.
split.
take H0 y.
right H5.
apply H6.
apply (ex_in _ x0).
apply H3.
apply (ex_in _ x0).
split;ass.
Qed.

Definition p_relatives_iota(A p: Set) (p_is_rel: relation p) 
:= ι _ (p_relatives_ex_iota A p p_is_rel).

Ltac grab_from_context P :=
  lazymatch goal with
  | H : P |- _ => exact H
  | _ => fail "No hypothesis of type" P "in context"
  end.

Notation "p [ A ]" := 
(p_relatives_iota A p (ltac:(grab_from_context (relation p))))(at level 60, left associativity, only parsing).

Notation "p [ A ]" := 
(p_relatives_iota A p _)(at level 60, left associativity, only printing).

Notation "'Dom' X" := (domain X (ltac:(grab_from_context (relation X))))(at level 60, only parsing).
Notation "'Dom' X" := (domain X _)(only printing).

Notation "'Ran' X" := (range X (ltac:(grab_from_context (relation X))))(at level 60, only parsing).
Notation "'Ran' X" := (range X _)(only printing).

Theorem p_relatives_of_domain_is_range(A p: Set) (p_is_rel: relation p): 
(* -> *)
(p[Dom p]) = (Ran p).
apply eq_in.
intros x H.
extract_iota_from_goal (Ran p).
take iota_prop x.
right H0.
apply H1.
extract_iota (p [Dom p]) H.
take iota_prop0 x.
take H2.
left H2.
take H4 H.
ex_el H5.
both H5.
apply (ex_in _ x0).
apply H7.
intros x H.
(* <- *)
extract_iota (Ran p) H.
rename s into range_of_p.
rename iota_prop into range_prop.
extract_iota_from_goal (p [Dom p]).
rename s into relatives_of_domain.
rename iota_prop into relatives_of_domain_prop.
take relatives_of_domain_prop x.
right H0.
apply H1.
clear H0 H1.
take range_prop x.
left H0.
take H1 H.
clear H0 H1.
ex_el H2.
rename x0 into z.
apply (ex_in _ z).
split.
extract_iota_from_goal (Dom p).
right (iota_prop z).
apply H0.
apply (ex_in _ x).
apply H2.
apply H2.
Qed.

Theorem p_relatives_of_any_set_are_subset_of_raange(A p: Set) (p_is_rel: relation p): 
(p[A] ⊆ (Ran p)).
intros x H.
extract_iota (p [A]) H.
extract_iota_from_goal (Ran p).
take iota_prop0 x.
right H0.
apply H1.
take iota_prop x.
left H2.
take H3 H.
ex_el H4.
both H4.
apply (ex_in _ x0).
ass.
Qed.

Theorem cartesian_is_relation(X Y: Set): relation(X × Y).
intros z H.
extract_iota (X × Y) H.
take iota_prop z.
left H0.
take H1 H.
ex_el H2.
both H2.
ex_el H4.
both H4.
apply (ex_in _ x).
apply (ex_in _ y).
ass.
Qed.


Theorem domain_of_cartesian(X Y: Set) (H: Y ≠ ∅) 
(CR: relation(X × Y)): (Dom (X × Y)) = X.
extract_iota_from_goal (Dom (X × Y)).
rename s into domain.
extract_iota (X × Y) iota_prop.
rename s into cartesian.
eq_in.
take iota_prop x.
left H1.
take H2 H0.
ex_el H3.
take iota_prop0 (< x, y >).
left H4.
take H5 H3.
ex_el H6.
both H6.
ex_el H8.
both H8.
take pair_property H9.
both H8.
repl H10.
apply H7.
take iota_prop x.
right H1.
apply H2.
take non_empty_set_has_element _ H.
ex_el H3.
rename a into y.
take iota_prop0 (< x, y >).
apply (ex_in _ y).
right H4.
apply H5.
apply (ex_in _ x).
split.
ass.
apply (ex_in _ y).
split.
ass.
apply eq_refl.
Qed.

Ltac ex_unique_in H := 
match goal with 
|- ∃1 e. _ =>
let P := fresh "P" in  
let ee := fresh e in  
apply (ex_unique_in _ _ H);
intros ee P
end.

Definition non_empty_set_has_element2: ∃1e. (empty_set_p e) ∧ 
∀c. c ≠ e -> ∃a. a ∈ c.
ex_unique_in empty_set_exists.
intros c H.
take non_empty_set_has_element c.
assert (c ≠ ∅).
extract_iota_from_goal ∅.
assert (s = e).
eq_in.
apply abs_el.
apply (iota_prop x).
apply H1.
apply abs_el.
apply (P x).
intro.
take H2 H1.
apply H3.
repl H1.
apply H.
take H0 H1.
apply H2.
Defined.

Definition pair_p_definitions_equivalent(a b s: Set): 
(pair_p_traditional a b s) ⇔ (pair_p a b s).
unfold pair_p_traditional, pair_p.
apply conj_in.
intro.
intro x.
apply conj_in.
intro.
ex_el H.
both H.
ex_el H2.
both H2.
split.
apply (ex_in _ u).
split.
ass.
split.
apply (ex_in _ ab).
split.
ass.
take H3 x.
left H2.
take H4 H0.
apply H5.
apply ex_less_conj_in.
take pair_unord_exists a b.
right H2.
apply H4.
apply ex_less_conj_in.
take unit_set_exists a.
right H2.
apply H4.
intro.
ex_el H.
both H.
ex_el H0.
both H0.
take extension_trans _ _ _ H1 H.
repl H0 in H1.
repl H0 in H2.
clear H0 H.
ex_el H2.
ex_el H3.
both H2.
both H3.
take H0 x.
right H3.
take extension_trans _ _ _ H H2.
repl H6 in H5.
apply H5.
apply H4.
intro.
take unit_set_exists a.
ex_unique_el H0.
rename p into u.
split.
apply (ex_in _ u).
split.
apply H0.
split.
take pair_unord_exists a b.
ex_unique_el H1.
rename p into ab.
apply (ex_in _ ab).
split.
apply H1.
intro k.
split.
intro.
take H k.
left H3.
take H4 H2.
ex_unique_el H5.
both H5.
take extension_trans _ _ _ H0 H6.
repl_in_goal H5.
ex_unique_el H7.
both H7.
take extension_trans _ _ _ H1 H8.
repl_in_goal H7.
apply H9.
intro.
take H k.
right H3.
apply H4.
split.
apply (ex_in _ u).
split.
apply H0.
split.
apply (ex_in _ ab).
split.
apply H1.
apply H2.
apply ex_less_conj_in.
apply U0.
apply ex_less_conj_in.
apply U.
apply ex_less_conj_in.
apply any_biimpl_set_is_no_more_than_one.
apply ex_less_conj_in.
apply U.
Qed.

Definition bridge_pair_p(a b: Set): (∃p. (pair_p_traditional a b p)) 
-> (∃p. (pair_p a b p)).
intro.
ex_el H.
apply (ex_in _ p).
take pair_p_definitions_equivalent a b p.
left H0.
apply H1.
apply H.
Qed.

Definition relation_p (a: Set) := ∀x. (x ∈ a) -> ∃m. ∃n. pair_p m n x.

Definition domain_exists(r: Set) : ∃1domain. 
(∀ x. ((x ∈ domain) ⇔ ((∃y. ∃1xy. pair_p x y xy ∧ xy ∈ r )))).
take ZF4_union r.
ex_el H.
rename a into u_r.
take ZF4_union u_r.
ex_el H0.
rename a into u_u_r.
split.
take ZF2_subsets 
(fun x0 => (∃ y . ∃1 xy. pair_p x0 y xy ∧ xy ∈ r)) u_u_r.
ex_el H1.
apply (ex_in _ b).
intro.
split.
intro.
take H1 x.
left H3.
take H4 H2.
right H5.
apply H6.
intro.
take H1 x.
right H3.
apply H4.
split.
ex_el H2.
ex_el H2.
both H2.
(* xy = {x, y} *)
take H xy H6.
take pair_unord_exists x y.
ex_el H7.
take H2 p.
assert (p ∈ xy).
take H5 p.
right H9.
apply H10.
ex_unique_in (unit_set_exists x).
ex_unique_in (pair_unord_exists x y).
take extension_trans _ _ _  H7 P0.
right.
apply H11.
take H8 H9.
take H0 p H10.
apply H11.
take H7 x.
right H12.
apply H13.
left.
apply eq_refl.
apply H2.
apply any_biimpl_set_is_no_more_than_one.
Qed.

Definition range_exists(r: Set): ∃1range. 
(∀ y. ((y ∈ range) ⇔ ((∃x. ∃1xy. pair_p x y xy ∧ xy ∈ r )))).
take ZF4_union r.
ex_el H.
rename a into u_r.
take ZF4_union u_r.
ex_el H0.
rename a into u_u_r.
split.
take ZF2_subsets 
(fun y => (∃ x . ∃1 xy. pair_p x y xy ∧ xy ∈ r)) u_u_r.
ex_el H1.
apply (ex_in _ b).
intro.
split.
intro.
take H1 x.
left H3.
take H4 H2.
right H5.
apply H6.
intro.
take H1 x.
right H3.
apply H4.
split.
ex_el H2.
ex_el H2.
both H2.
(* xy = {x, y} *)
take H xy H6.
rename x into y.
rename x0 into x.
take pair_unord_exists x y.
ex_el H7.
take H2 p.
assert (p ∈ xy).
take H5 p.
right H9.
apply H10.
ex_unique_in (unit_set_exists x).
ex_unique_in (pair_unord_exists x y).
take extension_trans _ _ _  H7 P0.
right.
apply H11.
take H8 H9.
take H0 p H10.
apply H11.
take H7 y.
right H12.
apply H13.
right.
apply eq_refl.
apply H2.
apply any_biimpl_set_is_no_more_than_one.
Qed.

Lemma ex_less_ex_more_el (P Q: Set -> Prop):
(∃1x. P x) -> (∃≤1 x. ∃ y. (P x ∧ P y)).
intro.
intros q w H1 H2.
right H.
take H0 q w.
apply H3.
ex_el H1.
left H1.
apply H4.
ex_el H2.
left H2.
ass.
Qed.

Lemma ex_less_ex_more_el_2 (P: Set -> Prop) :
(∃1x. P x) -> (∃≤1 x. ∃ y. (P y ∧ P x)).
intro.
intros q w H1 H2.
right H.
take H0 q w.
apply H3.
ex_el H1.
right H1.
apply H4.
ex_el H2.
right H2.
ass.
Qed.


Definition unit_set_p_join(a u1 u2: Set):
(unit_set_p a u1) -> (unit_set_p a u2) -> u1 = u2.
intros.
take extension_trans _ _ _ H H0.
apply H1.
Qed.


Definition pair_exists(a b: Set) : ∃1p. (pair_p a b p).
split.
apply bridge_pair_p.
change (∃ x. pair_p_traditional a b x).
pose proof biimpl_trans as p.
unfold pair_p.
take unit_set_exists a.
right H.
rename H0 into l2.
ex_el H.
take pair_unord_exists a b.
right H0.
rename H1 into l3.
ex_el H0.
take pair_unord_exists p0 p1.
right H1.
rename H2 into l1.
ex_el H1.
apply (ex_in _ p2).
split.
apply (ex_in _ p0).
split.
apply H.
split.
apply (ex_in _ p1).
split.
apply H0.
apply H1.
apply ex_less_conj_in.
apply l3.
apply ex_less_conj_in.
apply l2.
apply any_biimpl_set_is_no_more_than_one.
Qed.

Notation "p := < a , b >" := (pair_p a b p)(at level 81, left associativity).

Definition pair_property_p_hard (x y u v: Set): 
∃1p1. pair_p x y p1 ∧
∃1p2. pair_p u v p2 ∧
((p1 = p2) -> (x = u) ∧ (y = v)).
ex_unique_in (pair_exists x y).
ex_unique_in (pair_exists u v).
take pair_p_definitions_equivalent x y p1.
right H.
take H0 P.
clear P H H0.
rename H1 into P.
take pair_p_definitions_equivalent u v p2.
right H.
take H0 P0.
clear P0 H H0.
rename H1 into P0.
intro.
unfold pair_p_traditional in P.
ex_el P.
both P.
unfold pair_p_traditional in P0.
ex_el P0.
both P0.
ex_el H1.
both H1.
ex_el H3.
both H3.
rename ab into xy.
rename ab0 into uv.
take pair_property_naked x y u v.
left H3.
apply H7.
clear H3 H7.
extract_iota_from_goal ({`x}).
take extension_trans _ _ _ H0 iota_prop.
swap_eq H3.
repl H3.
extract_iota_from_goal ({x, y}).
take extension_trans _ _ _ H4 iota_prop0.
swap_eq H7.
repl H7.
extract_iota_from_goal ({u0, xy}).
take extension_trans _ _ _ H5 iota_prop1.
swap_eq H8.
repl H8.
extract_iota_from_goal ({`u}).
take extension_trans _ _ _ H2 iota_prop2.
swap_eq H9.
repl H9.
extract_iota_from_goal ({u, v}).
take extension_trans _ _ _ H1 iota_prop3.
swap_eq H10.
repl H10.
extract_iota_from_goal ({u1, uv}).
take extension_trans _ _ _ H6 iota_prop4.
swap_eq H11.
repl H11.
apply H.
Qed.


Definition ex_less_ex_unique_el (P: Set -> Prop):
∃≤1 x. ∃1 y. P x.
intros q w H1 H2.
ex_unique_el H1.
ex_unique_el H2.
take U q w.
take H H1 H1.
ass.
Qed.


Definition triple_exists(a b c: Set) : ∃1t. (triple_p a b c t).
unfold triple_p.
take pair_exists a b.
ex_unique_el H.
rename p into ab.
take pair_exists ab c.
ex_unique_el H0.
rename p into t.
split.
apply (ex_in _ t).
split.
apply (ex_in _ ab).
split; ass.
apply ex_less_conj_in.
apply U.
intros q w R1 R2.
ex_unique_el R1.
ex_unique_el R2.
clear U1 U2.
both R1.
both R2.
take extension_trans _ _ _ H1 H3.
repl H5 in H2.
take extension_trans _ _ _ H2 H4.
apply H6.
Qed.

(* Exercise 6.1 *)
Theorem triple_prop (x y z u v w: Set):
∃1t1. triple_p x y z t1 ∧
∃1t2. (triple_p u v w t2) ∧
((t1 = t2) -> ((x = u) ∧ (y = v) ∧ (z = w))).
ex_unique_in (triple_exists x y z).
ex_unique_in (triple_exists u v w).
intros H.
repl H in P.
rename H into G.
unfold triple_p in P, P0.
ex_el P.
ex_el P0.
both P.
both P0.
take pair_property_p_hard x y u v.
ex_el H3.
both H3.
ex_el H5.
both H5.
take pair_property_p_hard ab z ab0 w.
ex_el H5.
both H5.
ex_el H8.
both H8.
take extension_trans _ _ _ H0 H7.
take extension_trans _ _ _ H2 H5.
swap_eq H8.
take eq_trans _ _ _ H8 H10.
take H9 H11.
both H12.
swap_eq H13.
repl H13 in H1.
take extension_trans _ _ _ H H4.
take extension_trans _ _ _ H1 H3.
swap_eq H12.
take eq_trans _ _ _ H12 H15.
take H6 H16.
split.
apply H17.
apply H14.
Qed.


(* Exercise 6.2 
{1,2} X {2,3,4} = {(1,2), (1,3), (1,4), (2,2), (2,3), (2,4)}
{1,2} - domain
{2,3,4} - range
graph - rectangle, 6 points
*)


(* Exercise 6.3, 6.4 - Calculus, skipped, requires R*)

Definition cartesian_p (a b c: Set):= 
(∀ w. ((w ∈ c) ⇔ ((∃x. (x ∈ a) ∧ (∃y. (y ∈ b) ∧ ∃1p. pair_p x y p ∧ w = p ))))).

Definition bridge_pair_iota_to_p(w x y: Set): (w = (< x, y >)) -> ∃1 p.
(p := < x, y >) ∧ w = p.
intro.
unfold pair in H.
extract_iota ({`x}) H.
extract_iota ({x, y}) H.
extract_iota ({s, s0}) H.
split.
apply (ex_in _ s1).
split.
intro g.
split.
intro.
split.
apply (ex_in _ s).
split.
apply iota_prop.
split.
apply (ex_in _ s0).
split.
apply iota_prop0.
take iota_prop1 g.
left H1.
take H2 H0.
ass.
apply ex_less_conj_in.
apply any_biimpl_set_is_no_more_than_one.
apply ex_less_conj_in.
apply any_biimpl_set_is_no_more_than_one.
intro.
ex_el H0.
both H0.
ex_el H2.
both H2.
take iota_prop1 g.
right H2.
apply H4.
take extension_trans _ _ _ iota_prop H1.
repl H5.
take extension_trans _ _ _ iota_prop0 H0.
repl H6.
apply H3.
apply H.
apply ex_less_conj_in.
apply any_biimpl_set_is_no_more_than_one.
Qed.

Definition bridge_pair_p_to_iota(w x y: Set): (∃1 p.
(p := < x, y >) ∧ w = p) -> (w = (< x, y >)).
intro.
ex_el H.
both H.
repl H1.
clear H1.
unfold pair_p in H0.
unfold pair.
extract_iota_from_goal ({`x}).
extract_iota_from_goal ({x, y}).
extract_iota_from_goal ({s, s0}).
eq_in.
take H0 x0.
left H1.
take H2 H.
clear H1 H2.
rename s into u.
rename s0 into xy.
rename s1 into p1.
take iota_prop1 x0.
right H1.
apply H2.
clear H1 H2.
ex_el H3.
both H3.
ex_el H2.
both H2.
take extension_trans _ _ _ iota_prop H1.
take extension_trans _ _ _ iota_prop0 H3.
repl H2.
repl H5.
apply H4.
take H0 x0.
right H1.
apply H2.
clear H1 H2.
split.
apply (ex_in _ s).
split.
apply iota_prop.
split.
apply (ex_in _ s0).
split.
apply iota_prop0.
take iota_prop1 x0.
left H1.
take H2 H.
ass.
apply ex_less_conj_in.
apply any_biimpl_set_is_no_more_than_one.
apply ex_less_conj_in.
apply any_biimpl_set_is_no_more_than_one.
Qed.

Definition cartesian_exists (a b: Set): ∃1c. cartesian_p a b c.
unfold cartesian_p.
take cartesian_exists_old a b.
ex_el H.
split.
apply (ex_in _ c).
intro w.
split.
intro.
take H w.
left H1.
take H2 H0.
ex_el H3.
both H3.
ex_el H5.
both H5.
apply bridge_pair_iota_to_p in H6.
ex_el H6.
both H6.
apply (ex_in _ x).
split.
ass.
apply (ex_in _ y).
split.
ass.
split.
apply (ex_in _ p).
split.
ass.
apply H7.
apply ex_less_conj_in.
apply any_biimpl_set_is_no_more_than_one.
intro.
ex_el H0.
both H0.
ex_el H2.
both H2.
ex_el H3.
both H3.
take H w.
right H3.
apply H5.
apply (ex_in _ x).
split.
ass.
apply (ex_in _ y).
split.
ass.
repl H4.
pose proof H2.
take bridge_pair_p_to_iota p x y.
apply H7.
split.
apply (ex_in _ p).
split.
apply H6.
apply eq_refl.
apply ex_less_conj_in.
apply any_biimpl_set_is_no_more_than_one.
apply any_biimpl_set_is_no_more_than_one.
Qed.

Notation "i := a ∩ b" := (intersection2_p a b i)(at level 81, left associativity).
Notation "c := a × b" := (cartesian_p a b c)(at level 81, left associativity).
Notation "i := a ∪ b" := (union2_p a b i)(at level 81, left associativity).

(* 6.6, 6.7 - skipped but will be back SOOOOOON*)

Ltac get_left B H := 
let K := fresh "K" in
let G := fresh "G" in
match type of H with
|?x ∈ _ =>
pose proof conj_el_1 _ _ (B x) as K;
pose proof K H as G;
clear K
end.

Ltac get_right B H := 
let K := fresh "K" in
let G := fresh "G" in
match type of H with
|?x ∈ _ =>
pose proof conj_el_2 _ _ (B x) as K;
pose proof K H as G;
clear K
end.

Ltac grab B H := get_left B H || get_right B H.

Ltac apply_b H :=
let K := fresh "K" in
pose proof conj_el_2 _ _ H as K;
apply K;
clear H K.

Ltac ex_in x := apply (ex_in _ x).

(* Exercise 6.8 *)
Theorem cartesian_of_intersections (A B C D: Set): 
∃1ab. intersection2_p A B ab ∧
∃1cd. intersection2_p C D cd ∧
∃1abcd. cartesian_p ab cd abcd ∧
∃1ac. cartesian_p A C ac ∧
∃1bd. cartesian_p B D bd ∧
∃1acbd. intersection2_p ac bd acbd ∧
abcd = acbd.
ex_unique_in (intersection2_exists A B).
ex_unique_in (intersection2_exists C D).
ex_unique_in (cartesian_exists ab cd).
ex_unique_in (cartesian_exists A C).
ex_unique_in (cartesian_exists B D).
ex_unique_in (intersection2_exists ac bd).
eq_in.
grab P1 H.
take P4 x.
right H0.
apply H1.
clear H0 H1.
change (∃ el_ab :: ab. ∃ el_cd :: cd. ∃1 p. p := < el_ab, el_cd > ∧ x = p) in G.
ex_el G.
both G.
ex_el H1.
both H1.
ex_el H3.
both H3.
swap_eq H4.
repl H4 in H1.
clear H4 p.
grab P H0.
both G.
grab P0 H2.
both G.
split.
take P2 x.
apply_b H7.
apply (ex_in _ el_ab).
split.
ass.
apply (ex_in _ el_cd).
split.
ass.
split.
ex_in x.
split.
apply H1.
apply eq_refl.
apply ex_less_conj_in.
apply any_biimpl_set_is_no_more_than_one.
take P3 x.
apply_b H7.
apply (ex_in _ el_ab).
split.
ass.
apply (ex_in _ el_cd).
split.
ass.
split.
ex_in x.
split.
apply H1.
apply eq_refl.
apply ex_less_conj_in.
apply any_biimpl_set_is_no_more_than_one.
(*part 2*)
grab P4 H.
both G.
grab P2 H0.
ex_el G.
both G.
rename x0 into a_el.
ex_el H3.
both H3.
rename y into c_el.
ex_el H5.
both H5.
grab P3 H1.
ex_el G.
both G.
rename x0 into b_el.
ex_el H7.
both H7.
rename y into d_el.
ex_el H9.
both H9.
repl <- H10 in H7.
repl <- H6 in H3.
take pair_property_p_hard a_el c_el b_el d_el.
ex_el H9.
both H9.
ex_el H12.
both H12.
take extension_trans _ _ _ H7 H9.
take extension_trans _ _ _ H3 H11.
swap_eq H14.
take eq_trans _ _ _ H14 H12.
take H13 H15.
both H16.
repl <- H17 in H5.
repl <- H18 in H8.
repl <- H17 in H7.
repl <- H18 in H7.
clear H17 H18 H12 H14 H15 H13.
pose proof H3.
rename a_el into ab_el.
rename c_el into cd_el.
(* good*)
take P1 x.
apply_b H13.
ex_in ab_el.
split.
take P ab_el.
apply_b H13.
split.
ass.
ass.
ex_in cd_el.
split.
take P0 cd_el.
apply_b H13.
split.
ass.
ass.
split.
ex_in x.
split.
apply H7.
apply eq_refl.
apply ex_less_conj_in.
apply any_biimpl_set_is_no_more_than_one.
Qed.

Ltac ex_conj_chain_el H :=
let K := fresh "K" in
let L := fresh "P" in
let R := fresh "F" in
let I := fresh "I" in
match type of H with
|∃1 s. _ =>
let s' := fresh s in
pose proof conj_el_1 _ _ H as K;
apply (ex_el _ K);
intros s' I;
pose proof conj_el_1 _ _ I as L;
pose proof conj_el_2 _ _ I as R;
clear H K I;
ex_conj_chain_el R
|_ => idtac
end.

Lemma intersection_idempotent: ∀A. ∃1i. intersection2_p A A i ∧ i = A.
intro A.
ex_unique_in (intersection2_exists A A).
eq_in.
grab P H.
left G.
apply H0.
take P x.
apply_b H0.
split; ass.
Qed.

Ltac join H1 H2 := take extension_trans _ _ _ H1 H2.

Theorem cartesian_distributes_1 (A B C: Set): 
∃1ab. intersection2_p A B ab ∧
∃1abc. cartesian_p ab C abc ∧
∃1ac. cartesian_p A C ac ∧
∃1bc. cartesian_p B C bc ∧
∃1acbc. intersection2_p ac bc acbc ∧
abc = acbc.
ex_unique_in (intersection2_exists A B).
ex_unique_in (cartesian_exists ab C).
ex_unique_in (cartesian_exists A C).
ex_unique_in (cartesian_exists B C).
ex_unique_in (intersection2_exists ac bc).
take cartesian_of_intersections A B C C.
ex_conj_chain_el H.
take intersection_idempotent C.
ex_conj_chain_el H.
take extension_trans _ _ _ P10 P5.
swap_eq H.
take eq_trans _ _ _ H F.
repl H0 in P5.
repl H0 in P6.
clear F H H0 cd i P10.
(* seems ok *)
eq_in.
grab P0 H.
ex_el G.
both G.
ex_el H1.
both H1.
ex_conj_chain_el H3.
repl <- F in P10.
clear F.
take P3 x.
apply_b H1.
split.
take P1 x.
apply_b H1.
ex_in x0.
split.
grab P H0.
left G.
apply H1.
ex_in y.
split.
apply H2.
split.
ex_in x.
split.
ass.
apply eq_refl.
apply ex_less_conj_in.
apply any_biimpl_set_is_no_more_than_one.
take P2 x.
apply_b H1.
ex_in x0.
split.
grab P H0.
right G.
apply H1.
ex_in y.
split.
apply H2.
split.
ex_in x.
split.
ass.
apply eq_refl.
apply ex_less_conj_in.
apply any_biimpl_set_is_no_more_than_one.
take extension_trans _ _ _ P P4.
repl <- H0 in P6.
clear P4 H0 ab0.
take extension_trans _ _ _ P1 P7.
repl <- H0 in P9.
clear P7 H0 ac0.
(* move on *)
take P0 x.
apply_b H0.
grab P3 H.
both G.
grab P1 H0.
ex_el G.
both G.
ex_el H3.
both H3.
ex_conj_chain_el H5.
repl <- F in P4.
clear F.
rename x0 into q.
rename y into w.
grab P2 H1.
ex_el G.
both G.
ex_el H5.
both H5.
ex_conj_chain_el H7.
repl <- F in P7.
take pair_property_p_hard q w x0 y.
ex_conj_chain_el H5.
join P7 P11.
join P4 P10.
swap_eq H7.
take eq_trans _ _ _ H7 H5.
take F2 H8.
both H9.
repl <- H10 in H3.
repl <- H11 in H6.
ex_in q.
split.
take P q.
apply_b H9.
split.
apply H2.
apply H3.
ex_in w.
split.
apply H6.
split.
ex_in x.
split.
apply P4.
apply eq_refl.
apply ex_less_conj_in.
apply any_biimpl_set_is_no_more_than_one.
Qed.

Theorem cartesian_distributes_2 (A B C: Set): 
∃1bc. intersection2_p B C bc ∧
∃1abc. cartesian_p A bc abc ∧
∃1ab. cartesian_p A B ab ∧
∃1ac. cartesian_p A C ac ∧
∃1abac. intersection2_p ab ac abac ∧
abc = abac.
ex_unique_in (intersection2_exists B C).
ex_unique_in (cartesian_exists A bc).
ex_unique_in (cartesian_exists A B).
ex_unique_in (cartesian_exists A C).
ex_unique_in (intersection2_exists ab ac).
take cartesian_of_intersections A A B C.
ex_conj_chain_el H.
rename ab0 into aa.
join P P5.
repl <- H in P5.
repl <- H in P6.
clear H.
join P1 P7.
repl <- H in P9.
clear H P7.
take intersection_idempotent A.
ex_conj_chain_el H.
repl F in P7.
clear F.
join P7 P4.
repl <- H in P6.
clear i P7 H P4.
join P6 P0.
repl H in F0.
repl H in P6.
clear H abcd.
join P2 P8.
repl <- H in P8.
repl <- H in P9.
clear H bd.
join P9 P3.
repl H in P9.
repl H in F0.
clear H acbd.
apply F0.
Qed.

Theorem switch_premises(A B C: Prop): (A -> B -> C) -> (B -> A -> C).
intro.
intros.
take H H1 H0.
apply H2.
Qed.

Ltac refl := apply eq_refl.

Definition pair_property_p (x y u v p: Set): 
(pair_p x y p) ->
(pair_p u v p) ->
((x = u) ∧ (y = v)).
intros Q H.
take pair_property_p_hard x y u v.
ex_conj_chain_el H0.
join Q P.
join H P0.
swap_eq H0.
take eq_trans _ _ _ H0 H1.
take F0 H2.
apply H3.
Qed.

(* Exercise 6.5 - part 1 *)
Theorem cartesian_not_commutative: ¬(∀a. ∀b. ∃1q. 
(cartesian_p a b q) ∧ ∃1w.  (cartesian_p b a w) ∧ q = w).
intro.
take empty_set_exists.
ex_el H0.
take unit_set_exists e.
ex_el H1.
rename p into u_e.
take unit_set_exists u_e.
ex_el H2.
rename p into u_u_e.
take H u_e u_u_e.
ex_conj_chain_el H3.
apply extension_backwards in F0.
take pair_exists e u_e.
ex_el H3.
take F0 p.
left H4.
take contrapositive H5.
change (p ∉ w -> p ∈ q -> ⊥) in H6.
take (switch_premises (p ∉ w) (p ∈ q) ⊥) H6.
apply H7.
take P p.
apply_b H8.
ex_in e.
split.
take H1 e.
apply_b H8.
apply eq_refl.
ex_in u_e.
split.
take H2 u_e.
apply_b H8.
apply eq_refl.
split.
ex_in p.
split.
apply H3.
refl.
apply ex_less_conj_in.
apply any_biimpl_set_is_no_more_than_one.
clear H4 H5 H6 H7.
intro.
grab P0 H4.
ex_el G.
both G.
ex_el H6.
both H6.
ex_el H8.
both H8.
repl <- H9 in H6.
clear H9.
take pair_property_p_hard e u_e x y.
ex_conj_chain_el H8.
join H6 P2.
join P1 H3.
take eq_trans _ _ _ H9 H8.
take F1 H10.
both H11.
repl <- H13 in H7.
grab H1 H7.
apply extension_backwards in G.
take G e.
take H0 e.
left H14.
apply H15.
left H11.
apply H16.
take H1 e.
right H17.
apply H18.
refl.
Qed.


(* Exercise 6.5 - part 2 *)
Theorem cartesian_not_associative: ¬(∀a. ∀b. ∀c. 
∃1ab. (cartesian_p a b ab) ∧ 
∃1bc. (cartesian_p b c bc) ∧
∃1ab_c. (cartesian_p ab c ab_c) ∧ 
∃1a_bc. (cartesian_p a bc a_bc) ∧ 
 ab_c = a_bc).
intro.
take empty_set_exists.
ex_el H0.
take unit_set_exists e.
ex_el H1.
rename p into u_e.
take H u_e u_e u_e.
clear H.
ex_conj_chain_el H2.
take pair_exists e e.
ex_el H.
take pair_exists p e.
ex_el H2.
rename p0 into t.
apply extension_backwards in F0.
take F0 t.
clear F0.
left H3.
clear H3.
assert ((t ∈ ab_c)).
take P1 t.
apply_b H3.
ex_in p.
split.
take P p.
apply_b H3.
ex_in e.
split.
take H1 e.
apply_b H3.
refl.
ex_in e.
split.
take H1 e.
apply_b H3.
refl.
split.
ex_in p.
split.
apply H.
refl.
apply ex_less_conj_in.
apply any_biimpl_set_is_no_more_than_one.
ex_in e.
split.
take H1 e.
apply_b H3.
refl.
split.
ex_in t.
split.
ass.
refl.
apply ex_less_conj_in.
apply any_biimpl_set_is_no_more_than_one.
take H4 H3.
clear H4 H3.
grab P2 H5.
ex_el G.
both G.
ex_el H4.
both H4.
ex_conj_chain_el H7.
repl <- F in P3.
clear F.
assert (x = e).
take H1 x.
left H4.
apply H7.
apply H3.
take pair_property_p _ _ _ _ _ H2 P3.
both H7.
take eq_trans _ _ _ H8 H4.
apply extension_backwards in H7.
take H7 u_e.
left H10.
take H0 u_e.
left H12.
apply H13.
apply H11.
take H u_e.
apply_b H14.
split.
ex_in u_e.
split.
apply H1.
ex_unique_in (pair_unord_exists e e).
left.
refl.
apply ex_less_conj_in.
apply any_biimpl_set_is_no_more_than_one.
Qed.

(* Exercise 6.6
beta = X a brother of Y, (me, my_brother)

beta ∪ sigma = is a brother or a sister of
beta ∩ sigma = empty set (is a brother AND a sister of)
beta - sigma = is a brother but not a sister of, relation is equal to beta

Exercise 6.7
beta[A] - brothers of students in school
beta ∪ sigma [A] - brothers and sisters of students in school
 *)

(* Exercise 6.9 *)
Theorem exercise_4_9: 
∃A. ∃B. ∃C. ∃D. 
∃1AuB. union2_p A B AuB ∧
∃1CuD. union2_p C D CuD ∧
∃1ABCD. cartesian_p AuB CuD ABCD ∧
∃1AxC. cartesian_p A C AxC ∧
∃1BxD. cartesian_p B D BxD ∧
∃1ACBD. union2_p AxC BxD ACBD ∧
¬(ABCD = ACBD).
take empty_set_exists.
ex_el H.
take unit_set_exists e.
ex_el H0.
rename p into u_e.
(*
A = { e }
B = e 
C = e 
D = { e }
A ∪ B = { e }
C ∪ D = { e }
A ∪ B X C ∪ D = { (e,e) } 
A x C = e
B x D = e
... = e
*)
ex_in u_e.
ex_in e.
ex_in e.
ex_in u_e.
ex_unique_in (union2_exists u_e e).
ex_unique_in (union2_exists e u_e).
ex_unique_in (cartesian_exists AuB CuD).
ex_unique_in (cartesian_exists u_e e).
ex_unique_in (cartesian_exists e u_e).
ex_unique_in (union2_exists AxC BxD).
intro.
apply extension_backwards in H1.
take pair_exists e e.
ex_el H2.
take H1 p.
left H3.
clear H3.
assert ((p ∈ ABCD) ⇒ ((p ∉ ACBD) -> ⊥)).
intro.
intro.
take H4 H3.
apply (H5 H6).
apply H3.
clear H4 H3 H1.
take P1 p.
apply_b H1.
ex_in e.
split.
take P e.
apply_b H1.
left.
take H0 e.
right H1.
apply H3.
apply eq_refl.
ex_in e.
split.
take P0 e.
apply_b H1.
right.
take H0 e.
right H1.
apply H3.
apply eq_refl.  
ex_unique_in (pair_exists e e).
join H2 P5.
apply H1.
intro.
take P4 p.
left H6.
take H7 H5.
apply (disj_el _ _ _ H8).
intro.
take P2 p.
left H10.
take H11 H9.
ex_el H12.
right H12.
ex_el H13.
left H13.
take H y.
left H15.
apply H16.
apply H14.
intro.
take P3 p.
left H10.
take H11 H9.
ex_el H12.
left H12.
take H x.
left H14.
apply (H15 H13).
Qed.

Ltac left_and_take x y := 
let K := fresh "K" in
pose proof conj_el_1 _ _ x as K;
pose proof K y;
clear K.

Tactic Notation "left" uconstr(x) uconstr(y) := left_and_take x y.

(* Exercise 6.10 
 A x (B ∪ C) = (A x B) ∪ (A x C)
*)
Theorem cartesian_distributes_over_union: 
∀A. ∀B. ∀C.
∃1BuC. union2_p B C BuC ∧
∃1AxBuC. cartesian_p A BuC AxBuC ∧
∃1AxB. cartesian_p A B AxB ∧
∃1AxC. cartesian_p A C AxC ∧
∃1AxBuAxC. union2_p AxB AxC AxBuAxC ∧
(AxBuC = AxBuAxC).
intros A B C.
ex_unique_in (union2_exists B C).
ex_unique_in (cartesian_exists A BuC).
ex_unique_in (cartesian_exists A B).
ex_unique_in (cartesian_exists A C).
ex_unique_in (union2_exists AxB AxC).
eq_in.
take P3 x.
apply_b H0.
take P0 x.
left H0.
take H1 H.
clear H0 H1.
ex_el H2.
both H2.
ex_el H1.
both H1.
ex_el H3.
both H3.
repl <- H4 in H1.
clear H4 p.
take P y.
left H3 H2.
apply (disj_el _ _ _ H4).
intro.
left.
take P1 x.
apply_b H6.
ex_in x0.
split.
apply H0.
ex_in y.
split.
apply H5.
ex_unique_in (pair_exists x0 y).
join H1 P4.
ass.
intro.
right.
take P2 x.
apply_b H6.
ex_in x0.
split.
apply H0.
ex_in y.
split.
apply H5.
ex_unique_in (pair_exists x0 y).
join H1 P4.
ass.
take P0 x.
apply_b H0.
take P3 x.
left H0.
take H1 H.
apply (disj_el _ _ _ H2).
intro.
take P1 x.
left H4.
take H5 H3.
ex_el H6.
both H6.
ex_el H8.
both H8.
ex_el H9.
both H9.
ex_in x0.
split.
ass.
repl <- H10 in H8.
ex_in y.
split.
take P y.
apply_b H9.
left.
apply H6.
ex_unique_in (pair_exists x0 y).
join H8 P4.
apply H9.
intro.
take P2 x.
left H4.
take H5 H3.
ex_el H6.
both H6.
ex_el H8.
both H8.
ex_el H9.
both H9.
ex_in x0.
split.
apply H7.
ex_in y.
split.
take P y.
apply_b H9.
right.
ass.
ex_unique_in (pair_exists x0 y).
repl <- H10 in H8.
join H8 P4.
ass.
Qed.

(* Exercise 6.11 *)
Theorem union_not_distributes_over_cartesian: 
¬(∀A. ∀B. ∀C.
∃1BxC. cartesian_p B C BxC ∧
∃1AuBxC. union2_p A BxC AuBxC ∧
∃1AuB. union2_p A B AuB ∧
∃1AuC. union2_p A C AuC ∧
∃1AuBxAuC. cartesian_p AuB AuC AuBxAuC ∧
(AuBxC = AuBxAuC)).
intro.
take empty_set_exists.
ex_el H0.
take unit_set_exists e.
ex_el H1.
rename p into u_e.
specialize (H u_e e e).
cbv beta in H.
ex_conj_chain_el H.
apply extension_backwards in F.
take F e.
left H.
assert ((e ∈ AuBxC)).
take P0 e.
apply_b H3.
left.
take H1 e.
apply_b H3.
apply eq_refl.
take H2 H3.
take P3 e.
left H5 H4.
ex_el H6.
both H6.
ex_el H8.
both H8.
ex_el H9.
both H9.
repl <- H10 in H8.
clear H10.
take unit_set_exists x.
ex_el H9.
rename p0 into u_x.
take H8 u_x.
right H10.
take H0 u_x.
left H12.
apply H13.
apply H11.
ex_unique_in (unit_set_exists x).
ex_unique_in (pair_unord_exists x y).
join H9 P4.
left.
apply H14.
Qed.

Theorem intersection_not_distributes_over_cartesian: 
¬(∀A. ∀B. ∀C.
∃1BxC. cartesian_p B C BxC ∧
∃1AiBxC. intersection2_p A BxC AiBxC ∧
∃1AiB. intersection2_p A B AiB ∧
∃1AiC. intersection2_p A C AiC ∧
∃1AiBxAiC. cartesian_p AiB AiC AiBxAiC ∧
(AiBxC = AiBxAiC)).
intro.
take empty_set_exists.
ex_el H0.
take pair_exists e e.
ex_el H1.
take unit_set_exists e.
ex_el H2.
rename p0 into u_e.
take unit_set_exists p.
ex_el H3.
rename p0 into u_p.
take H u_p u_e u_e.
clear H.
ex_conj_chain_el H4.
apply extension_backwards in F.
take F p.
left H.
assert ((p ∈ AiBxC) ⇒ ((p ∉ AiBxAiC) -> ⊥)).
intro.
intro.
take H4 H5.
apply (H6 H7).
apply H5.
take P0 p.
apply_b H6.
split.
take H3 p.
apply_b H6.
apply eq_refl.
take P p.
apply_b H6.
ex_in e.
split.
take H2 e.
apply_b H6.
apply eq_refl.
ex_in e.
split.
take H2 e.
apply_b H6.
apply eq_refl.
ex_unique_in (pair_exists e e).
join P4 H1.
swap_eq H6.
apply H6.
intro.
take P3 p.
left H7 H6.
ex_el H8.
both H8.
ex_el H10.
both H10.
ex_conj_chain_el H11.
repl <- F0 in P4.
clear F0.
take P1 x.
left H10 H9.
both H11.
left (H3 x) H12.
left (H2 x) H13.
swap_eq H11.
take eq_trans _ _ _ H11 H14.
apply extension_backwards in H15.
take H15 u_e.
left H16.
take H0 u_e.
left H18.
apply H19.
apply H17.
take H1 u_e.
apply_b H20.
ex_unique_in (unit_set_exists e).
ex_unique_in (pair_unord_exists e e).
left.
join P5 H2.
swap_eq H20.
ass.
Qed.

Definition non_empty_set_has_element: ∀e. (empty_set_p e) ->
∀c. c ≠ e -> ∃a. a ∈ c.
intro.
take non_empty_set_has_element2.
ex_conj_chain_el H.
intro.
join P H.
intro.
intro.
take F x0.
repl <- H0 in H1.
take H2 H1.
apply H3.
Qed.

Theorem element_of_first_component_of_cartesian:
∀x. ∀A. ∀B. ∀e. ∀AxB. 
(empty_set_p e) ->
(cartesian_p A B AxB) ->
(B ≠ e) ->
(x ∈ A) ->
∃y. (y ∈ B) ∧ ∃1p. pair_p x y p ∧ p ∈ AxB.
intros x A B e AxB.
intros.
take non_empty_set_has_element e H B H1.
ex_el H3.
rename a into y.
ex_in y.
split.
ass.
ex_unique_in (pair_exists x y).
take H0 p.
apply_b H4.
ex_in x.
apply (conj_in _ _ H2).
ex_in y.
apply (conj_in _ _ H3).
ex_unique_in (pair_exists x y).
join P P0.
ass.
Qed.

Theorem element_of_both_components_of_cartesian:
∀C. ∀e. ∀CxC. 
(empty_set_p e) ->
(cartesian_p C C CxC) ->
(C ≠ e) ->
∃x. (x ∈ C) ∧
∃y. (y ∈ C) ∧ 
∃1p. pair_p x y p ∧ p ∈ CxC.
intros C e CxC.
intros.
take non_empty_set_has_element e H C H1.
ex_el H2.
take pair_exists a a.
ex_el H3.
take H0 p.
ex_in a.
split.
ass.
ex_in a.
split.
ass.
ex_unique_in (pair_exists a a).
join H3 P.
repl <- H5.
apply_b H4.
ex_in a.
split.
ass.
ex_in a.
split.
ass.
ex_unique_in (pair_exists a a).
join H3 P0.
ass.
Qed.

Theorem element_of_cartesian_square:
∀x. ∀C. ∀CxC. 
(cartesian_p C C CxC) ->
(x ∈ C) ->
∃1p. pair_p x x p ∧ p ∈ CxC.
intros x C CxC.
intros.
ex_unique_in (pair_exists x x).
take H p.
apply_b H1.
ex_in x.
split.
ass.
ex_in x.
split.
ass.
ex_unique_in (pair_exists x x).
join P P0.
ass.
Qed.

Theorem cartesian_of_nonempty_sets_is_not_empty:
∀A. ∀B. ∀e. ∀AxB. 
(empty_set_p e) ->
(cartesian_p A B AxB) ->
(A ≠ e) ->
(B ≠ e) ->
(AxB ≠ e).
intros A B e AxB.
intros.
take non_empty_set_has_element e H A H1.
take non_empty_set_has_element e H B H2.
ex_el H3.
ex_el H4.
take pair_exists a a0.
ex_el H5.
take H0 p.
intro.
apply extension_backwards in H7.
take H7 p.
take H p.
left H9.
apply H10.
left H8.
apply H11.
right H6.
apply H12.
ex_in a.
split.
ass.
ex_in a0.
split.
ass.
ex_unique_in (pair_exists a a0).
join H5 P.
ass.
Qed.

Theorem union_of_nonempty_sets_is_not_empty:
∀A. ∀B. ∀e. ∀AuB. 
(empty_set_p e) ->
(union2_p A B AuB) ->
(A ≠ e) ->
(B ≠ e) ->
(AuB ≠ e).
intros A B e AuB.
intros.
take non_empty_set_has_element e H A H1.
ex_el H3.
take H0 a.
intro.
apply extension_backwards in H5.
take H5 a.
take H a.
left H7.
apply H8.
left H6.
apply H9.
apply_b H4.
left.
apply H3.
Qed.


(* Exercise 6.12 *)
Theorem exercise_6_12: 
∃1e. empty_set_p e ∧
∀A. ∀B. ∀C.
∃1AxB. cartesian_p A B AxB ∧
∃1BxA. cartesian_p B A BxA ∧
∃1CxC. cartesian_p C C CxC ∧
∃1AxBuBxA. (union2_p AxB BxA AxBuBxA) ∧
((A ≠ e) -> (B ≠ e) -> AxBuBxA = CxC ->
((A = B) ∧ (B = C))).
ex_unique_in (empty_set_exists).
intros A B C.
ex_unique_in (cartesian_exists A B).
ex_unique_in (cartesian_exists B A).
ex_unique_in (cartesian_exists C C).
ex_unique_in (union2_exists AxB BxA).
intros.
assert ((A = C ∧ B = C) -> (A = B ∧ B = C)).
intro.
both H2.
swap_eq H4.
take eq_trans _ _ _ H3 H4.
split.
ass.
swap_eq H4.
ass.
apply H2.
clear H2.
split.
eq_in.
take element_of_first_component_of_cartesian x A B e AxB P P0.
take H3 H0 H2.
ex_el H4.
both H4.
ex_el H6.
both H6.
assert (p ∈ AxBuBxA).
take P3 p.
apply_b H6.
left.
ass.
apply eq_el_1 in H1.
take H1 p.
take H8 H6.
take P2 p.
left H10 H9.
ex_el H11.
both H11.
ex_el H13.
both H13.
ex_el H14.
both H14.
repl <- H15 in H13.
take pair_property_p x y x0 y0 p H4 H13.
left H14.
repl <- H16 in H12.
apply H12.
take element_of_cartesian_square x C CxC P2 H2.
ex_conj_chain_el H3.
apply eq_el_2 in H1.
take H1 p F.
take P3 p.
left H4 H3.
apply (disj_el _ _ _ H5).
intro.
take P0 p.
left H7 H6.
ex_el H8.
both H8.
ex_el H10.
both H10.
ex_el H11.
both H11.
repl <- H12 in H10.
take pair_property_p x x x0 y p P4 H10.
left H11.
repl <- H13 in H9.
ass.
intro.
take P1 p.
left H7 H6.
ex_el H8.
both H8.
ex_el H10.
both H10.
ex_el H11.
both H11.
repl <- H12 in H10.
take pair_property_p x x x0 y p P4 H10.
right H11.
repl <- H13 in H8.
apply H8.
eq_in.
take element_of_first_component_of_cartesian x B A e BxA P.
take H3 P1 H H2.
ex_el H4.
both H4.
ex_el H6.
both H6.
assert (p ∈ AxBuBxA).
take P3 p.
apply_b H6.
right.
ass.
apply eq_el_1 in H1.
take H1 p H6.
take P2 p.
left H9 H8.
ex_el H10.
both H10.
ex_el H12.
both H12.
ex_el H13.
both H13.
repl <- H14 in H12.
take pair_property_p x y x0 y0 p H4 H12.
left H13.
repl <- H15 in H11.
apply H11.
take element_of_cartesian_square x C CxC P2 H2.
ex_el H3.
both H3.
apply eq_el_2 in H1.
take H1 p H5.
take P3 p.
left H6 H3.
apply (disj_el _ _ _ H7).
intro.
take P0 p.
left H9 H8.
ex_el H10.
both H10.
ex_el H12.
both H12.
ex_el H13.
both H13.
repl <- H14 in H12.
take pair_property_p x x x0 y p H4 H12.
right H13.
repl H15.
apply H10.
intro.
take P1 p.
left H9 H8.
ex_el H10.
both H10.
ex_el H12.
both H12.
ex_el H13.
both H13.
repl <- H14 in H12.
take pair_property_p x x x0 y p H4 H12.
left H13.
repl H15.
apply H11.
Qed.

Theorem pred_exists: ∀ x :: N. (0 < x) -> ∃px::N. (S px) = x.
intro.
intro.
take PN5_induction (fun x=> 0 < x -> ∃ px::N . S px = x).
intro.
assert ((0 < 0 -> (∃ px::N . S px = 0))).
intro.
take set_in_zero_causes_contradiction H2.
apply H3.
take H0 H2.
clear H0 H2.
assert ((∀ x :: N
. (0 < x -> (∃ px::N . S px = x)) ->
0 < S x -> (∃ px::N . S px = S x))).
intro.
intros.
ex_in x0.
split.
apply H0.
apply eq_refl.
take H3 H0.
take H2 x H H1.
apply H4.
Qed.


Theorem induction_starts_at_one: forall P : Set -> Prop, P 1 ->
(∀ x :: N . P x -> P (S x)) ->
(∀ x :: N . (0 < x) -> P x).
intros.
intro.
intros.
take PN5_induction (fun x => P (S x)).
take H3 H.
clear H3.
assert ((∀ x :: N . P (S x) -> P (S (S x)))).
intros y.
intros.
take H0 (S y).
take PN2_succ y.
take H7 H3.
take H6 H8 H5.
apply H9.
take H4 H3.
take pred_exists x.
take H6 H1 H2.
ex_el H7.
both H7.
take H5 px.
take H7 H8.
repl H9 in H10.
apply H10.
Qed.

(* notion xpy *)
Definition related x p y := ∃1xpy. (pair_p x y xpy) ∧ (xpy ∈ p).

Definition relation_from_x_to_y_p (p X Y: Set):= 
∃1c. cartesian_p X Y c ∧
(relation_p p) ∧ (p ⊆ c).

Definition relation_from_z_to_z_p (p Z: Set):= ∃X. ∃Y.
∃1u. union2_p X Y u ∧
(relation_from_x_to_y_p p X Y) ∧ (u ⊆ Z).

Definition relation_in_z_p (p Z: Set) := relation_from_x_to_y_p p Z Z.

Definition p_relatives_p(A p s: Set) (p_is_rel: relation_p p) := 
(∀y. (y ∈ s) ⇔ ∃x::A. related x p y).

Definition p_relatives_ex(A p: Set) (p_is_rel: relation_p p) : 
∃1s. p_relatives_p A p s p_is_rel.
split.
assert (relation p).
unfold relation.
intro.
intro.
take p_is_rel x H.
ex_el H0.
ex_el H0.
take bridge_pair_p_to_iota x m n.
ex_in m.
ex_in n.
apply H1.
split.
ex_in x.
split.
apply H0.
apply eq_refl.
apply ex_less_conj_in.
apply any_biimpl_set_is_no_more_than_one.
take p_relatives_ex_iota A p H.
ex_el H0.
ex_in s.
intro.
split.
intro.
take H0 x.
left H2 H1.
unfold p_relatives_p.
ex_el H3.
both H3.
ex_in x0.
split.
apply H4.
unfold related.
split.
take bridge_pair_iota_to_p (< x0, x >) x0 x.
assert ((< x0, x >) = (< x0, x >)).
apply eq_refl.
take H3 H6.
ex_el H7.
both H7.
ex_in p0.
split.
apply H8.
repl H9 in H5.
apply H5.
apply ex_less_conj_in.
apply any_biimpl_set_is_no_more_than_one.
unfold p_relatives_p.
intro.
take H0 x.
right H2.
apply H3.
ex_el H1.
both H1.
ex_in x0.
split.
apply H4.
unfold related in H5.
ex_el H5.
both H5.
take bridge_pair_p_to_iota xpy x0 x.
assert ((∃1 p. p := < x0, x > ∧ xpy = p)).
split.
ex_in xpy.
split.
apply H1.
apply eq_refl.
apply ex_less_conj_in.
apply any_biimpl_set_is_no_more_than_one.
take H5 H7.
repl H8 in H6.
apply H6.
apply any_biimpl_set_is_no_more_than_one.
Qed.


Definition reflective p X := ∀x::X. related x p x.

Definition symmetric p := ∀x. ∀y. (related x p y) -> (related y p x).

Definition transitive p := ∀x. ∀y. ∀z. (related x p y) -> (related y p z) -> (related x p z).

Definition equivalence_relation p X := 
(relation_in_z_p p X) ∧ (reflective p X) ∧ (symmetric p) ∧ (transitive p).

Definition equiv_class_gen_by_x_p(p x: Set) (p_is_rel: relation_p p) (s: Set) := 
(∀y. (y ∈ s) ⇔ related x p y).

Definition equiv_class_gen_by_x_ex(p x: Set) (p_is_rel: relation_p p) :
∃1s. equiv_class_gen_by_x_p p x p_is_rel s.
take unit_set_exists x.
ex_el H.
rename p0 into u_x.
take p_relatives_ex u_x p p_is_rel.
split.
ex_el H0.
ex_in s.
intro.
take H0 x0.
split.
intro.
left H1 H2.
ex_el H3.
both H3.
take H x1.
left H3 H4.
repl H6 in H5.
apply H5.
intro.
right H1.
apply H3.
take H x0.
ex_in x.
split.
take H x.
right H5.
apply H6.
apply eq_refl.
apply H2.
apply any_biimpl_set_is_no_more_than_one.
Qed.

Definition to_rel 
(p X: Set) (H: equivalence_relation p X): relation_p p.
left H.
left H0.
left H1.
unfold relation_in_z_p in H2.
unfold relation_from_x_to_y_p in H2.
left H2.
ex_el H3.
left H3.
right H4.
apply H5.
Qed.

(* property (I) *)
Definition any_element_is_in_equivalence_class 
(p: Set) (X: Set) (H: equivalence_relation p X) : 
∀x::X. ∃1c. (equiv_class_gen_by_x_p p x 
(to_rel p X H) c) ∧ x ∈ c.
intro.
intro.
ex_unique_in (equiv_class_gen_by_x_ex p x 
(to_rel p X H)).
unfold equiv_class_gen_by_x_p in P.
take P x.
apply_b H1.
left H.
left H1.
unfold reflective in H2.
both H2.
take H4 x H0.
apply H2.
Qed.

(* property (II) *)
Theorem related_elements_are_in_the_same_class (p R: Set)
(ER: equivalence_relation p R):
∀x. ∀y. related x p y -> 
∃1class_x. equiv_class_gen_by_x_p p x (to_rel p R ER) class_x ∧
∃1class_y. equiv_class_gen_by_x_p p y (to_rel p R ER) class_y ∧
class_x = class_y.
intro x.
intro y.
intros.
ex_unique_in (equiv_class_gen_by_x_ex p x 
(to_rel p R ER)).
ex_unique_in (equiv_class_gen_by_x_ex p y 
(to_rel p R ER)).
apply eq_in.
intro z.
intro.
unfold equiv_class_gen_by_x_p in P, P0.
take P0 z.
apply_b H1.
take P z.
left H1 H0.
left ER.
right H3.
take H4 x y H.
right ER.
take H6 y x z.
take H7 H5 H2.
apply H8.
intro z.
intro.
unfold equiv_class_gen_by_x_p in P, P0.
take P z.
apply_b H1.
take P0 z.
left H1 H0.
right ER.
take H3 x y z.
take H4 H H2.
apply H5.
Qed.


Definition equivalence_class_p p X A 
(ER: equivalence_relation p X) := 
(A ⊆ X) ∧ 
∃x::A. (∀y. (y∈A) ⇔ related x p y). 

Definition equivalence_class_p_alt p X A 
(ER: equivalence_relation p X) := 
(A ⊆ X) ∧ 
∃x::A. ∃1u_x. unit_set_p x u_x ∧ p_relatives_p u_x p A (to_rel p X ER). 

Theorem simplify_empty_set(e: Set): 
(∀ x . x ∉ e) -> (∀ x . (x ∈ e ⇔ ⊥)).
intro.
intro.
split.
intro.
take H x H0.
apply H1.
intro.
apply H0.
Defined.

Theorem get_symmetric (p X: Set) (ER: equivalence_relation p X): symmetric p.
left ER.
right H.
apply H0.
Qed.

Theorem get_transitive (p X: Set) (ER: equivalence_relation p X): transitive p.
right ER.
apply H.
Qed.

Theorem get_reflective (p X: Set) (ER: equivalence_relation p X): reflective p X.
left ER.
left H.
right H0.
apply H1.
Qed.

Theorem conj_symmetric (A B: Prop): (A ∧ B) -> (B ∧ A).
intro.
both H.
split.
ass.
ass.
Qed.

(* Theorem 7.1 - part 1*)
Theorem collection_of_equiv_classes_is_a_partition:
∀p. ∀X. forall ER: equivalence_relation p X,
∀c. (∀z. z ∈ c ⇔ equivalence_class_p p X z ER) ->
partition_p c X.
intro p.
intro X.
intro.
intros c H.
unfold partition_p.
ex_unique_in (empty_set_exists).
split.
split.
split.
unfold disjoint_collection.
intros x.
intro.
intros y y_in_C NE.
unfold disjoint.
ex_unique_in (empty_set_exists).
join P P0.
repl <- H1.
clear P0 H1.
ex_unique_in (intersection2_exists x y).
assert ((∀ x . (x ∈ i ⇔ ⊥)) -> i = e).
intro.
join H1 P.
apply H2.
apply H1.
clear H1.
apply (simplify_empty_set i).
take H x.
take H y.
left H1 H0.
left H2 y_in_C.
clear H1 H2.
intro z.
intro.
take P0 z.
left H2.
take H5 H1.
both H6.
clear H1 H2 H5.
apply NE.
apply eq_in.
intro k.
intro.
left H3.
take H2 z H7.
left H4.
take H6 z H8.
take H2 k H1.
clear H2 H6 H9.
unfold equivalence_class_p in H3.
right H3.
right H4.
ex_el H2.
both H2.
rename x0 into u.
ex_el H6.
both H6.
rename x0 into v.
take H11 k.
left H6 H1.
take H12 k.
right H14.
apply H15.
clear H14 H15.
take H11 z.
take H12 z.
left H14 H7.
left H15 H8.
take get_symmetric _ _ ER.
unfold symmetric in H18.
take H18 u z H16.
take get_transitive _ _ ER.
take H20 v z u H17 H19.
take H20 v u k H21 H13.
apply H22.
intro k.
intro.
left H3.
left H4.
take H2 z H7.
take H5 k H1.
clear H2 H5.
right H3.
right H4.
ex_el H2.
ex_el H5.
rename x0 into u.
rename x1 into v.
both H2.
both H5.
take H11 k.
right H5.
apply H13.
take H12 k.
left H14 H1.
take get_symmetric _ _ ER.
apply H16 in H15.
assert ((related v p u) -> (related u p k)).
intro.
take get_transitive _ _ ER.
take H18 k v u H15 H17.
take get_symmetric _ _ ER.
apply H20.
apply H19.
apply H17.
clear H16 H17.
take H11 z.
take H12 z.
left H16 H7.
left H17 H8.
take get_symmetric _ _ ER.
apply H20 in H18.
take get_transitive _ _ ER.
take H21 v z u H19 H18.
apply H22.
unfold collection_of_nonempty_sets.
intro.
intro.
intro.
unfold empty_set_p in H1.
join H1 P.
repl H2 in H0.
clear H1 H2.
take H e.
left H1 H0.
unfold equivalence_class_p in H2.
right H2.
ex_el H3.
left H3.
take P x0.
left H5 H4.
apply H6.
intro.
intro.
take H x.
left H1 H0.
left H2.
apply H3.
intro.
intro.
take equiv_class_gen_by_x_ex p x (to_rel p X ER).
ex_el H1.
unfold equiv_class_gen_by_x_p in H1.
take H1 x.
ex_in s.
apply conj_symmetric.
split.
apply_b H2.
left ER.
left H2.
right H3.
take H4 x H0.
apply H5.
take H s.
apply_b H3.
unfold equivalence_class_p.
split.
intro g.
intro.
take H1 g.
unfold  equivalence_relation in ER.
take get_symmetric _ _ ER.
take H5 g.
left H4 H3.
unfold related in H7.
left ER.
left H8.
left H9.
unfold relation_p in H10.
unfold relation_in_z_p in H10.
unfold relation_from_x_to_y_p in H10.
ex_el H7.
both H7.
right H9.
unfold reflective in H7.
left H10.
ex_el H13.
right H13.
take H14 xpy H12.
left H13.
left H16.
take H17 xpy.
left H18 H15.
ex_el H19.
both H19.
ex_el H21.
both H21.
ex_conj_chain_el H22.
repl <- F in P0.
take pair_property_p x1 y x g xpy P0 H11.
right H21.
repl H22 in H19.
apply H19.
ex_in x.
split.
take get_reflective _ _ ER.
take H3 x H0.
apply_b H2.
apply H4.
apply H1.
Qed.

Ltac conj_chain_el H :=
let L := fresh "C" in
let R := fresh "C" in
match type of H with
|_ ∧ _ =>
pose proof conj_el_1 _ _ H as L;
pose proof conj_el_2 _ _ H as R;
clear H;
conj_chain_el L;
conj_chain_el R
|_ => idtac
end.

Theorem elements_of_pair_in_relation_in_z_belongs_to_z:
∀p. ∀X.
∀p_is_rel: relation_in_z_p p X.
∀a. ∀b. ∀k. pair_p a b k -> (k ∈ p) -> (a ∈ X) ∧ (b ∈ X). 
intros p X p_is_rel a b k H U.
left p_is_rel.
ex_el H0.
both H0.
both H1.
split.
take H0 k.
rename x into C.
take H2 k U.
left H1 H4.
ex_el H5.
both H5.
ex_el H7.
both H7.
ex_el H8.
both H8.
repl <- H9 in H7.
take pair_property_p _ _ _ _ _ H7 H.
left H8.
repl H10 in H6.
apply H6.
take H0 k.
rename x into C.
take H2 k U.
left H1 H4.
ex_el H5.
both H5.
ex_el H7.
both H7.
ex_el H8.
both H8.
repl <- H9 in H7.
take pair_property_p _ _ _ _ _ H7 H.
right H8.
repl H10 in H5.
apply H5.
Qed.


(* Theorem 7.1 - part 2*)
Theorem partition_defines_equivalence_relation:
∀p. ∀X.
∀p_is_rel: relation_in_z_p p X.
∀PAR. ((partition_p PAR X) ∧ (∀a. ∀b. (∀z. (z ∈ p) ⇔ (pair_p a b z)) ⇔ 
∃A::PAR. (a ∈ A) ∧ (b ∈ A)))
-> equivalence_relation p X .
intros p X p_is_rel PAR.
intro.
both H.
split.
split.
split.
apply p_is_rel.
unfold partition_p in H0.
ex_conj_chain_el H0.
both F.
both H.
both H2.
intro g.
intro.
unfold related.
ex_unique_in (pair_exists g g).
rename xpy into gpg.
take H1 g g.
assert ((∀ z . z ∈ p ⇔ z := < g, g >) -> gpg ∈ p).
intro.
take H6 gpg.
apply_b H7.
apply P0.
apply H6.
apply_b H5.
take H0 g H2.
ex_el H5.
both H5.
ex_in p0.
split.
ass.
split; ass.
intros u v.
intro.
unfold related.
ex_unique_in (pair_exists v u).
unfold related in H.
ex_el H.
rename xpy into v_u.
rename xpy0 into u_v.
both H.
unfold partition_p in H0.
ex_el H0.
conj_chain_el H0.
take C2 u.
take elements_of_pair_in_relation_in_z_belongs_to_z
p X p_is_rel u v u_v H2 H3.
both H0.
take H H4.
ex_el H0.
both H0.
rename p0 into u_v_class.
take H1 u v.
Admitted.

(* Skipped all exercises for chapter 7  *)

Definition any_set_is_empty_or_non_empty (s: Set) : 
(empty_set_p s) ∨ (∃e. e ∈ s).
take exc_thrd (empty_set_p s).
apply (disj_el _ _ _ H).
intro.
left.
ass.
intro.
right.
apply ex_in_alt.
intro.
unfold empty_set_p in H0.
apply H0.
intro.
split.
intro.
take H1 x.
apply (H3 H2).
intro.
apply H2.
Qed.

Lemma empty_set_is_subset_of_any: ∀A. ∃1e. empty_set_p e ∧ (e ⊆ A).
intro A.
ex_unique_in (empty_set_exists).
intro.
intro.
take P x.
left H0.
take H1 H.
apply H2.
Qed.


(* Section 8: Functions*)
Definition ordered_pair (s: Set) := ∃a. ∃b. pair_p a b s.

Definition function (s: Set) := 
(* I *) (∀x. x ∈ s -> ordered_pair x) ∧
(* II *) (∀x. ∀y. ∀z. ∃1xy. pair_p x y xy ∧ ∃1xz. pair_p x z xz ∧ 
((xy ∈ s ∧ xz ∈ s) -> y = z)).

Definition on(s X: Set) := domain_p s X.

Definition function_on(s X: Set) := (function s) 
∧ domain_p s X.

Definition range_is_subset(s Y: Set) :=
∃1r. range_p s r ∧ r ⊆ Y.

Definition into(s Y: Set) := range_is_subset s Y.

Definition onto(s Y: Set) := range_p s Y.

Definition function_into(s X Y: Set) := 
(function s) ∧ (into s Y).

Definition function_onto(s X Y: Set) := 
(function s) ∧ (onto s Y).

Definition function_on_into(s X Y: Set) := (function s) 
∧ domain_p s X 
∧ range_is_subset s Y.

Definition on_onto(s X Y: Set) := (function s) 
∧ domain_p s X 
∧ range_p s Y.

Notation "f : X -> Y" := (function_on_into f X Y)(at level 81, left associativity).

Definition appl_p(f x fx: Set) :=  ∃1p. pair_p x fx p ∧ p ∈ f.

Definition appl_exists: ∀f. ∀X. function_on f X -> ∀x::X. ∃1y. appl_p f x y.
intro f.
intro X.
intro.
intro x.
intro.
right H.
left H.
take H1 x.
left H3 H0.
ex_el H4.
ex_el H4.
both H4.
split.
unfold appl_p.
ex_in y.
ex_unique_in (pair_exists x y).
join P H5.
repl H4.
apply H6.
unfold appl_p.
intros y1 y2.
intro.
intro.
ex_el H4.
ex_el H7.
both H4.
both H7.
right H2.
take H7 x y1 y2.
ex_el H11.
both H11.
ex_el H13.
both H13.
apply H14.
split.
join H12 H8.
repl H13.
apply H9.
join H4 H11.
repl <- H13.
apply H10.
Qed.


Definition appl_p_with_Y(f x Y fx: Set):=  fx ∈ Y ∧ ∃1p. pair_p x fx p ∧ p ∈ f.

Definition function_on_into_is_total: ∀f. ∀X. ∀Y. function_on_into f X Y -> ∀x::X. ∃1y. 
appl_p_with_Y f x Y y.
intro f.
intro X.
intro Y.
intro.
intro.
intros.
split.
left H.
right H1.
take H2 x.
left H3 H0.
ex_el H4.
ex_conj_chain_el H4.
right H.
unfold range_is_subset in H4.
ex_conj_chain_el H4.
assert (y ∈ Y).
take P0 y.
take F0 y.
apply H5.
apply_b H4.
ex_in x.
ex_unique_in (pair_exists x y).
join P P1.
repl <- H4.
apply F.
left H3.
take H5 H0.
ex_in y.
split.
ass.
ex_el H6.
ex_el H6.
both H6.
left H1.
right H6.
take H9 x y y0.
ex_conj_chain_el H10.
join P P1.
repl <- H10 in F2.
join H7 P2.
repl <- H11 in F2.
take conj_in _ _ F H8.
take F2 H12.
repl H13.
unfold appl_p_with_Y.
ex_unique_in (pair_exists x y0).
join P2 P3.
repl <- H14.
repl <- H11.
apply H8.
intros a b H1 H2.
both H1.
both H2.
left H.
left H2.
right H6.
take H7 x a b.
clear H7.
ex_el H8.
both H8.
ex_el H9.
both H9.
apply H10.
split.
unfold appl_p_with_Y in H4.
ex_el H4.
both H4.
join H7 H9.
repl H4.
ass.
unfold appl_p_with_Y in H5.
ex_el H5.
both H5.
join H8 H9.
repl H5.
ass.
Qed.

Definition appl_with_Y_exists: ∀f. ∀X. ∀Y. function_on_into f X Y -> ∀x::X. ∃1y. appl_p_with_Y f x Y y.
apply function_on_into_is_total.
Qed.

Definition pair_components_are_in_domain_and_codomain: 
∀a. ∀b. ∃1p. pair_p a b p ∧ 
(∀f. ∀X. ∀Y. function_on_into f X Y -> p ∈ f -> a ∈ X ∧ b ∈ Y).
intro a.
intro b.
ex_unique_in (pair_exists a b).
intro f.
intro X.
intro Y.
intro.
intro.
split.
left H.
right H1.
unfold domain_p in H2.
take H2 a.
apply_b H3.
ex_in b.
split.
ex_in p.
split.
apply P.
ass.
apply ex_less_conj_in.
apply any_biimpl_set_is_no_more_than_one.
right H.
unfold range_is_subset in H1.
ex_el H1.
both H1.
take H3 b.
apply H1.
take H2 b.
apply_b H4.
ex_in a.
ex_unique_in (pair_exists a b).
join P P0.
repl <- H4.
ass.
Qed.


(* Y ^ X *)
Definition all_functions_p (X Y s: Set) := 
∀f. (f ∈ s) ⇔ (function_on_into f X Y).

Definition all_functions_exists: ∀X. ∀Y. ∃1s. all_functions_p X Y s.
intro X.
intro Y.
split.
take cartesian_exists X Y.
ex_el H.
rename c into XmY.
take ZF6_power_set XmY.
ex_el H0.
rename b into P_XmY.
take ZF2_subsets (fun f=> (function_on_into f X Y)) P_XmY.
ex_el H1.
rename b into subset_P_XmY.
ex_in subset_P_XmY.
intro.
split.
intro.
take H1 x.
left H3 H2.
right H4.
apply H5.
intro.
take H1 x.
apply_b H3.
split.
left H2.
left H3.
left H4.
take any_set_is_empty_or_non_empty x.
apply (disj_el _ _ _ H6).
intro.
take empty_set_is_subset_of_any XmY.
ex_conj_chain_el H8.
join H7 P.
repl <- H8 in F.
take H1 x.
take H0 x F.
apply H10.
intro.
ex_el H7.
rename e into k.
take H5 k H7.
unfold ordered_pair in H8.
ex_el H8.
ex_el H8.
take H1 x.
left H9.
take H0 x.
apply H11.
clear H11.
intro p.
intro.
take H p.
apply_b H12.
take H5 p H11.
unfold ordered_pair in H12.
ex_el H12.
ex_el H12.
take pair_components_are_in_domain_and_codomain a0 b0.
ex_conj_chain_el H13.
take F x X Y H2.
join H12 P.
repl <- H14 in H13.
take H13 H11.
both H15.
ex_in a0.
split.
ass.
ex_in b0.
split.
ass.
split.
ex_in p.
split.
apply H12.
apply eq_refl.
apply ex_less_conj_in.
apply any_biimpl_set_is_no_more_than_one.
apply H2.
apply any_biimpl_set_is_no_more_than_one.
Qed.

Definition domain_of_all_functions_is_empty_then_only_one_element:
∀X. ∀Y. ∃1s. (all_functions_p X Y s) ∧ 
((empty_set_p X) -> ∀z. z ∈ s ⇔ empty_set_p z).
intros X Y.
ex_unique_in (all_functions_exists X Y).
intro.
intro.
split.
intro.
unfold all_functions_p in P.
take P x.
left H1 H0.
left H2.
right H2.
unfold empty_set_p.
intro z.
split.
intro.
left H3.
left H6.
take H7 z H5.
unfold ordered_pair in H8.
ex_el H8.
ex_el H8.
right H3.
take H9 a.
take H a.
left H11.
apply H12.
apply_b H10.
ex_in b.
ex_unique_in (pair_exists a b).
join H8 P0.
repl <- H10.
apply H5.
intro.
apply H5.
intro.
take P x.
apply_b H1.
(* empty set is INTO function from empty set to any codomain*)
split.
split.
split.
intro.
intro.
take H0 x0.
left H2 H1.
apply H3.
intros a b c.
ex_unique_in (pair_exists a b).
ex_unique_in (pair_exists a c).
intro.
both H1.
take H0 xy.
left H1 H2.
apply H4.
intro z.
split.
intro.
ex_in z.
ex_unique_in (pair_exists z z).
take H z.
left H2 H1.
apply H3.
intro.
ex_el H1.
ex_el H1.
both H1.
take H0 xy.
left H1 H3.
apply H4.
unfold range_is_subset.
ex_unique_in (range_exists x).
intro m.
intro.
take P0 m.
left H2 H1.
ex_el H3.
ex_el H3.
both H3.
take H0 xy.
left H3 H5.
apply H6.
Qed.

Definition impl_el(A B: Prop): (A ⇒ B) -> ((¬A) ∨ B).
intro.
take exc_thrd A.
apply (disj_el _ _ _ H0).
intro.
right.
apply H.
apply H1.
intro.
left.
apply H1.
Qed.

Definition impl_in(A B: Prop): ((¬A) ∨ B) -> (A ⇒ B).
intro.
intro.
apply (disj_el _ _ _ H).
intro.
apply (H1 H0).
apply impl_in_tauto.
Qed.

Definition not_impl_el_1(A B: Prop): (¬ (A ⇒ B)) -> A.
intro.
assert (¬ ((¬A) ∨ B)).
intro.
apply H.
apply impl_in in H0.
apply H0.
apply deMorganNotOr in H0.
both H0.
apply DN_el.
apply H1.
Qed.


Definition non_empty_set_has_element_simple:
∀s.  (¬ empty_set_p s) -> ∃ a . a ∈ s.
intro.
intro.
unfold empty_set_p in H.
assert (¬ (∀ x0 . ¬ ¬ (x0 ∈ x ⇔ ⊥))).
intro.
apply H.
intro.
take H0 x0.
apply DN_el in H1.
apply H1.
apply ex_in_alt in H0.
ex_el H0.
ex_in x0.
apply deMorganNotAnd in H0.
apply (disj_el _ _ _ H0).
intro.
apply not_impl_el_1 in H1.
apply H1.
intro.
apply not_impl_el_1 in H1.
apply H1.
Qed.

Definition range_of_all_functions_is_empty_then_no_elements:
∀X. ∀Y. ∃1s. (all_functions_p X Y s) ∧ 
((empty_set_p Y) -> (¬(empty_set_p X)) -> empty_set_p s).
intros X Y.
ex_unique_in (all_functions_exists X Y).
intro.
intro.
apply non_empty_set_has_element_simple in H0.
ex_el H0.
intro k.
split.
intro.
take P k.
left H2 H1.
left H3.
right H3.
right H4.
take H6 a.
left H7 H0.
ex_el H8.
ex_el H8.
both H8.
rename y into b.
unfold range_is_subset in H5.
ex_el H5.
both H5.
take H8 b.
take H11 b.
take H b.
left H13.
apply H14.
apply H12.
apply_b H5.
ex_in a.
split.
ex_in xy.
split.
ass.
apply H10.
apply ex_less_conj_in.
apply any_biimpl_set_is_no_more_than_one.
intro.
apply H1.
Qed.


Definition element_of_cartesian_is_ordered_pair (X Y c m: Set) 
(H : cartesian_p X Y c)
(H2: m ∈ c): ordered_pair m.
unfold ordered_pair.
take H m.
left H0 H2.
ex_el H1.
both H1.
ex_el H4.
both H4.
ex_el H5.
both H5.
ex_in x.
ex_in y.
repl H6.
apply H4.
Qed.

Definition intersection_with_cartesian_p(A X Y s: Set):= 
(∀k. (k ∈ s) ⇔ ((k ∈ A) ∧ (∃ x :: X . ∃ y :: Y . pair_p x y k))).

Definition intersection_with_cartesian_exists(A X Y: Set): 
∃1s. intersection_with_cartesian_p A X Y s.
split.
take cartesian_exists X Y.
ex_el H.
take intersection2_exists A c.
ex_el H0.
ex_in i.
intro.
split.
intro.
split.
take H0 x.
left H2 H1.
both H3.
apply H4.
take H x.
take H0 x.
left H3 H1.
both H4.
left H2 H6.
ex_el H4.
both H4.
ex_el H8.
both H8.
ex_el H9.
both H9.
ex_in x0.
split.
ass.
ex_in y.
split.
ass.
repl H10.
apply H8.
intro.
both H1.
take H0 x.
apply_b H1.
split.
apply H2.
take H x.
apply_b H1.
ex_el H3.
both H3.
ex_el H4.
both H4.
ex_in x0.
split.
ass.
ex_in y.
split.
ass.
split.
ex_in x.
split.
apply H5.
apply eq_refl.
apply ex_less_conj_in.
apply any_biimpl_set_is_no_more_than_one.
apply any_biimpl_set_is_no_more_than_one.
Qed.

Definition restriction_p (f A Y: Set) (g: Set):=
intersection_with_cartesian_p f A Y g.

Definition restriction_exists (f A Y: Set) : ∃1g. restriction_p f A Y g.
apply intersection_with_cartesian_exists.
Qed.

Definition identity_map_p(X i: Set) := (∀p. ((p ∈ i) ⇔ 
(∃x:: X. pair_p x x p))).

Definition identity_map_exists (X: Set): ∃1i. identity_map_p X i.
split.
take cartesian_exists X X.
ex_el H.
take ZF2_subsets (fun p => (∃x:: X. pair_p x x p)) c.
ex_el H0.
ex_in b.
intro.
split.
intro.
take H0 x.
left H2 H1.
both H3.
apply H5.
intro.
take H0 x.
right H2.
apply H3.
split.
take H x.
apply_b H4.
ex_el H1.
both H1.
ex_in x0.
split.
apply H4.
ex_in x0.
split.
apply H4.
split.
ex_in x.
split.
apply H5.
apply eq_refl.
apply ex_less_conj_in.
apply any_biimpl_set_is_no_more_than_one.
apply H1.
apply any_biimpl_set_is_no_more_than_one.
Qed.

Ltac join_pairs_by_name P1 P2 :=
let T := fresh "T" in
match type of P1 with
|  ?xy := < ?x1, ?y1 > => 
match type of P2 with
|  xy := < ?x2, ?y2 > => 
pose proof pair_property_p x1 y1 x2 y2 xy P1 P2 as T;
both T
end
end.


Definition identity_map_is_into (X: Set): 
∃1i. identity_map_p X i ∧ function_on_into i X X.
ex_unique_in (identity_map_exists X).
split.
split.
split.
intro.
intro.
take P x.
left H0 H.
ex_el H1.
both H1.
ex_in x0.
ex_in x0.
apply H3.
intros x y z.
ex_unique_in (pair_exists x y).
ex_unique_in (pair_exists x z).
intro.
both H.
take P xy.
left H H0.
ex_el H2.
both H2.
take P xz.
left H2 H1.
ex_el H5.
both H5.
join_pairs_by_name P0 H4.
join_pairs_by_name P1 H7.
join_pairs_by_name P1 H7.
apply eq_symm in H9.
take eq_trans x1 x x0 H9 H5.
apply eq_symm in H10.
apply eq_symm in H13.
take eq_trans y x0 x1 H8 H13.
take eq_trans y x1 z H14 H10.
apply H15.
intro x.
split.
intro.
ex_in x.
ex_unique_in (pair_exists x x ).
take P xy.
apply_b H0.
ex_in x.
split.
apply H.
apply P0.
intro.
ex_el H.
ex_el H.
both H.
take P xy.
left H H1.
ex_el H2.
both H2.
join_pairs_by_name H0 H4.
repl H2.
apply H3.
unfold range_is_subset.
ex_unique_in (range_exists i).
intro g.
intro.
take P0 g.
left H0 H.
ex_el H1.
ex_el H1.
both H1.
take P xy.
left H1 H3.
ex_el H4.
both H4.
join_pairs_by_name H2 H6.
repl H7.
apply H5.
Qed.

(* Exercise 8.2 *)
Definition restriction_of_identity_relation (A X: Set) (H: A ⊆ X) :
∃1ix. identity_map_p X ix ∧
∀H1: function_on_into ix X X.
∃1iA. identity_map_p A iA ∧ 
∃1ix_A. (restriction_p ix A A ix_A) ∧ ix_A = iA.
ex_unique_in (identity_map_exists X).
intro.
ex_unique_in (identity_map_exists A).
ex_unique_in (restriction_exists ix A A).
unfold restriction_p in P1.
unfold intersection_with_cartesian_p in P1.
eq_in.
take P1 x0.
left H1 H0.
both H2.
unfold identity_map_p in P0.
unfold identity_map_p in P.
take P0 x0.
apply_b H2.
ex_el H4.
both H4.
ex_el H5.
both H5.
take P x0.
left H5 H3.
ex_el H7.
both H7.
join_pairs_by_name H6 H9.
repl H7 in H6.
repl H10 in H6.
ex_in x2.
split.
repl H7 in H2.
apply H2.
apply H9.
take P1 x0.
apply_b H1.
take P0 x0.
left H1 H0.
split.
take P x0.
apply_b H3.
ex_el H2.
both H2.
take H x1 H3.
ex_in x1.
split.
apply H2.
apply H4.
ex_el H2.
both H2.
ex_in x1.
split.
apply H3.
ex_in x1.
split.
apply H3.
apply H4.
Qed.

Ltac right_uniqueness_in x y z :=
let T := fresh "T" in
intros x y z;
ex_unique_in (pair_exists x y);
ex_unique_in (pair_exists x z);
intro T;
both T.



Definition restriction_is_function_on_A (f X Y A: Set) (H1: function_on_into f X Y) 
(SUB: A ⊆ X) (fA: Set) 
(H2: restriction_p f A Y fA) : function_on fA A.
split.
split.
intro.
intro.
take H2 x.
left H0 H.
both H3.
ex_conj_chain_el H5.
ex_el H5.
both H5.
ex_el H6.
both H6.
ex_in x0.
ex_in y.
apply H7.
right_uniqueness_in x y z.
take H2 xy.
left H3 H.
both H4.
take H2 xz.
left H4 H0.
both H7.
left H1.
left H7.
right H10.
take H11 x y z.
ex_el H12.
both H12.
ex_el H14.
both H14.
join H13 P.
repl H14 in H15.
join H12 P0.
repl H16 in H15.
apply H15.
split;ass.
intro.
split.
intro.
take function_on_into_is_total f X Y H1 x.
take SUB x H.
take H0 H3.
ex_el H4.
unfold appl_p_with_Y in H4.
both H4.
ex_el H6.
both H6.
ex_in y.
ex_unique_in (pair_exists x y).
join H4 P.
repl <- H6.
take H2 p.
apply_b H8.
split.
apply H7.
ex_in x.
split.
apply H.
ex_in y.
split.
apply H5.
apply H4.
intro.
ex_el H.
ex_el H.
both H.
take H2 xy.
left H H3.
right H4.
ex_el H5.
both H5.
ex_el H7.
both H7.
join_pairs_by_name H0 H8.
repl H7.
apply H6.
Qed.

Definition function_on_into_function_on (f X Y: Set) (H1: function_on_into f X Y): function_on f X.
unfold function_on.
left H1.
apply H.
Qed.

Definition restriction_property (f X Y A: Set) (H1: function_on_into f X Y) (SUB: A ⊆ X) 
(fA: Set) (H2: restriction_p f A Y fA) : ∀a::A. 
(∃1y1. appl_p fA a y1 ∧
∃1y2. appl_p f a y2 ∧ y1 = y2).
intros a.
intro.
take restriction_is_function_on_A f X Y A H1 SUB fA H2.
take appl_exists fA A H0 a H.
ex_unique_in H3.
take H1.
apply function_on_into_function_on in H4.
take SUB a H.
take appl_exists f X H4 a H5.
ex_unique_in H6.
clear H3 H6.
unfold appl_p in P0.
ex_el P0.
both H0.
unfold appl_p in P.
ex_el P.
both P.
both P0.
left H4.
right H10.
assert (p0 ∈ f -> y1 = y2).
intro.
take H11 a y1 y2.
ex_el H13.
both H13.
ex_el H15.
both H15.
apply H16.
split.
join H0 H14.
repl H15 in H12.
ass.
join H8 H13.
repl H15 in H9.
ass.
apply H12.
clear H11.
take H2 p0.
left H11 H7.
left H13.
apply H14.
Qed.

Definition injection_mapping_on_into_p(A X s: Set) :=
∃1ix. identity_map_p X ix ∧
restriction_p ix A X s ∧ function_on_into s A X.

Definition one_to_one (f: Set) := ∀x1. ∀x2. 
∃1y1. appl_p f x1 y1 ∧
∃1y2. appl_p f x2 y2 ∧
(y1 = y2) -> (x1 = x2).

Definition one_to_one_correspondence(f X Y: Set) :=
(function f) ∧ (on f X) ∧ (one_to_one f) ∧ (onto f Y).

Definition in_one_to_one_correspondence(X Y: Set) :=
∃f. one_to_one_correspondence f X Y.

Definition all_functions_in_one_to_one (A B X: Set)
(H: in_one_to_one_correspondence A B):
∃1AX. all_functions_p A X AX ∧
∃1BX. all_functions_p B X BX ∧
in_one_to_one_correspondence AX BX.
ex_unique_in (all_functions_exists A X).
ex_unique_in (all_functions_exists B X).
unfold in_one_to_one_correspondence.
Admitted.

Definition zero_p s := empty_set_p s.

Definition zero_exists : ∃1s. zero_p s.
apply empty_set_exists.
Qed.


Definition one_p s := ∀x. (x ∈ s) ⇔ empty_set_p x.

Definition one_exists: ∃1s. one_p s.
split.
take zero_exists.
ex_el H.
take unit_set_exists s.
ex_el H0.
unfold one_p.
ex_in p.
intro.
split.
intro.
take H0 x.
left H2 H1.
repl <- H3 in H.
apply H.
intro.
join H H1.
take eq_symm _ _ H2.
take H0 x.
right H4.
take H5 H3.
apply H6.
apply any_biimpl_set_is_no_more_than_one.
Qed.

Definition set_of_two_elements_p(s: Set) := 
∀x. (x ∈ s) ⇔ (zero_p x ∨ one_p x).

Definition set_of_two_elements_exists: 
∃1s. set_of_two_elements_p s.
split.
take one_exists.
ex_el H.
take zero_exists.
ex_el H0.
take ZF3_pairing_equiv s s0.
ex_el H1.
ex_in c.
unfold set_of_two_elements_p.
intro.
split.
intro.
take H1 x.
left H3 H2.
apply (disj_el _ _ _ H4).
intro.
right.
repl H5.
ass.
intro.
left.
repl H5.
ass.
intro.
take H1 x.
apply_b H3.
apply (disj_el _ _ _ H2).
intro.
right.
join H0 H3.
apply eq_symm.
ass.
intro.
left.
join H H3.
apply eq_symm.
apply H4.
apply any_biimpl_set_is_no_more_than_one.
Qed.

Definition characteristic_function_p (A X: Set) (H: A ⊆ X) (f: Set):
∀p. (p ∈ f) ⇔ (∃x. ∃y. pair_p x y p ∧ 
(x ∈ A -> one_p y) ∧ ((x ∈ X ∧ x ∉ A) -> zero_p y)).



