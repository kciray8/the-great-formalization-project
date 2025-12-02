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

Definition disjoint (A B: Set) := ((A ∩ B) = ∅).
Definition intersect (A B: Set) := ((A ∩ B) ≠ ∅).
Definition disjoint_collection (A: Set) := 
∀x::A. ∀y::A. (x ≠ y) -> disjoint x y.

Definition partition (X P: Set) := (disjoint_collection P) ∧ 
(∀s. (s ⊆ X) -> (s ≠ ∅) -> s ∈ P) ∧ (∀x::X. ∃p::P. x ∈ p).

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

Lemma relative_complement_el_alt: ∀A. ∀B. ∀x. 
x ∉ (A - B) ->  (x ∉ A) ∨ (x ∈ B).
intros A B x.
intro.
extract_iota (A - B) H.
take iota_prop x.
right H0.
take contrapositive H1.
take H2 H.
apply deMorganNotAnd in H3.
apply (disj_el _ _ _ H3).
intro.
left.
apply H4.
intro.
right.
apply DN_el.
apply H4.
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

Lemma eq_in_backward: ∀A. ∀B. B ⊆ A -> A ⊆ B -> A = B.
intros A B H H2.
apply extensionality_for_subsets.
ass.
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

Lemma impl_in (H: Prop): H ⇒ H.
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
apply impl_in.
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

Lemma empty_set_is_subset_of_any: ∀A. (∅ ⊆ A).
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
apply empty_set_is_subset_of_any.
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
Lemma intersection_idempotent: ∀A. ((A ∩ A) = A).
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

(* Exercise 5.3 - d 
Too complex and boring -- skipped for later
Should do on paper first?
Maybe this exercise is with a typo -
unable to solve it with membership relation
*)
Goal ∀A. ∀B. ∀C. ∀X. ∀Y. ∀U. (A ⊆ U) -> (B ⊆ U)-> (C ⊆ U) -> (X ⊆ U) -> (Y ⊆ U) ->
 (((A ∩ B) ∪ (A ∩ C) ∪ ((U - A) ∩ (U - X) ∩ Y))
    ∩ (U - ((A ∩ (U - B) ∩ C) ∪ ((U - A) ∩ (U - X) ∩ (U - Y)) ∪ ((U - A) ∩ B ∩ Y))))
  = ((A ∩ B) ∪ ((U - A) ∩ (U - B) ∩ (U - X) ∩ Y)).
intros A B C X Y U aU bU cU xU yU.
get (U - B) as uB.
get (U - A) as uA.
get (U - C) as uC.
get (U - X) as uX.
get (U - Y) as uY.
repl <- P.
repl <- P0.
repl <- P1.
repl <- P2.
repl <- P3.
take intersection_union_distr A B C.
repl <- H.
take deMorganNotIntersection ((A ∩ uB) ∩ C)
((uA ∩ uX) ∩ uY) U.
clear H.
take rc_in_subset B U bU.
repl <- P in H.
take intersection_in_subset _ _ _ aU H.
take intersection_in_subset _ _ _ H1 cU.
take H0 H2.
clear H0.
Admitted.


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

(* Exercise 5.8 - a b c - TYPOS TYPOS SKIPPED*)

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
take cartesian_product_exists X X.
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

Definition p_relatives_ex(A r: Set): 
∃1s. (∀y. (y ∈ s) ⇔ ∃x::A. <x, y> ∈ r).
split.
take range_exists r.
ex_el H.
take ZF2_subsets (fun y => (∃ x :: A . < x, y > ∈ r)) d.
ex_el H0.
apply (ex_in _ b).
intro.
split.
intro.
take H0 x.
left H2.
take H3 H1.
right H4.
apply H5.
intro.
ex_el H1.
both H1.
take H0 x.
apply_b H1.
split.
take H x.
apply_b H1.
ex_in x0.
ass.
ex_in x0.
split.
apply H2.
apply H3.
apply any_biimpl_set_is_no_more_than_one.
Qed.

Definition p_relatives(A p: Set)
:= ι _ (p_relatives_ex A p).

Notation "p [ A ]" := 
(p_relatives A p)
(at level 60, left associativity).

Definition ordered_pair (s: Set) := ∃a. ∃b. s = <a, b>.

Definition function (s: Set) := 
(* I *) (∀x. x ∈ s -> ordered_pair x) ∧
(* II *) (∀x. ∀y. ∀z. ((<x, y> ∈ s ∧ <x, z> ∈ s) -> y = z)).

Definition on(s X: Set) := (domain s) = X.

Definition function_on(s X: Set) := (function s) ∧ (on s X).

Definition range (r: Set):= ι _ (range_exists r).

Definition range_is_subset(s Y: Set) := range s ⊆ Y.

Definition into(s Y: Set) := range s ⊆ Y.

Definition onto(s Y: Set) := (range s) = Y.

Definition function_into(s Y: Set) := 
(function s) ∧ (into s Y).

Definition function_onto(s Y: Set) := 
(function s) ∧ (onto s Y).

Definition function_on_into(s X Y: Set) := (function s) 
∧ on s X
∧ into s Y.

Definition on_onto(s X Y: Set) := (function s) 
∧ on s X
∧ onto s X.

Notation "f : X -> Y" := (function_on_into f X Y)(at level 81, left associativity).

Definition one_to_one (s: Set) := (∀a. ∀b. ∀y. ((<a, y> ∈ s ∧ <b, y> ∈ s) -> a = b)).

Definition one_to_one_correspondence (f A B: Set) :=
(function f) ∧ (on f A) ∧ (onto f B) ∧ (one_to_one f).

Ltac left_and_take x y := 
let K := fresh "K" in
pose proof conj_el_1 _ _ x as K;
pose proof K y;
clear K.

Tactic Notation "left" uconstr(x) uconstr(y) := left_and_take x y.

Theorem exercsise_8_9 (A B f: Set): f[A ∩ B] ⊆ (f[A] ∩ f[B]).
intro.
intro.
extract_iota (f [A ∩ B]) H.
extract_iota_from_goal ((f [A] ∩ f [B])).
take iota_prop0 x.
apply_b H0.
split.
take iota_prop x.
left H0 H.
ex_el H1.
both H1.
apply (intersection_el) in H2.
both H2.
extract_iota_from_goal (f [A]).
take iota_prop1 x.
apply_b H2.
ex_in x0.
split.
ass.
ass.
extract_iota_from_goal (f [B]).
take iota_prop1 x.
apply_b H0.
take iota_prop x.
left H0 H.
ex_el H1.
both H1.
apply (intersection_el) in H2.
both H2.
ex_in x0.
split.
ass.
ass.
Qed.

Definition similar (A B: Set) := ∃f. one_to_one_correspondence f A B.

Notation "A ~ B" := 
(similar A B) (at level 60, left associativity).

Definition dominated (A B: Set) := ∃b. (b ⊆ B) ∧ (A ~ b).

Notation "A ≾ B" := 
(dominated A B) (at level 60, left associativity).

Definition dominates (A B: Set) := dominated B A.

Notation "A ≿ B" := 
(dominates A B) (at level 60, left associativity).

Theorem dominated_means_ex_of_function (A B: Set) (H: A ≾ B): 
∃f. function_on_into f A B ∧ one_to_one f.
unfold dominated in H.
ex_el H.
both H.
unfold similar in H1.
ex_el H1.
ex_in f.
split.
left H1.
split.
left H.
apply H2.
unfold into.
right H.
unfold onto in H2.
repl H2.
apply H0.
right H1.
apply H.
Qed.

Definition appl_ex (f: Set) (X Y: Set) (H: function_on_into f X Y) (x: Set) 
(x_in_X: x ∈ X):
 ∃1y. (y ∈ Y) ∧ (<x,y> ∈ f).
apply (conj_in _ _).
left H.
right H0.
unfold on in H1.
extract_iota (domain f) H1.
apply eq_symm in  H1.
repl H1 in x_in_X.
take iota_prop x.
left H2 x_in_X.
ex_el H3.
ex_in y.
split.
right H.
unfold into in H4.
take H4 y.
apply H5.
extract_iota_from_goal (range f).
take iota_prop0 y.
apply_b H6.
ex_in x.
ass.
ass.
left H.
left H0.
right H1.
intros a b K L.
both K.
both L.
take H2 x a b.
apply H7.
split.
ass.
ass.
Defined.

Definition appl (f: Set) (X Y: Set) 
(H: function_on_into f X Y) (x: Set) (x_in_X: x ∈ X) := 
ι _ (appl_ex f X Y H x x_in_X).

Theorem composition_ex(g f: Set): ∃1c. ∀p. (p ∈ c) ⇔ 
∃x. ∃z. (p = <x, z>) ∧ ∃y. <x,y> ∈ f ∧ <y,z> ∈ g.
take domain_exists f.
ex_el H.
rename d into dom_f.
take range_exists g.
ex_el H0.
rename d into ran_g.
take cartesian_product_exists dom_f ran_g.
ex_el H1.
take ZF2_subsets (fun p => ∃x. ∃z. (p = <x, z>) ∧ ∃y. <x,y> ∈ f ∧ <y,z> ∈ g) c.
ex_el H2.
split.
ex_in b.
intro.
split.
intro.
take H2 x.
left H4 H3.
both H5.
apply H7.
intro.
take H3.
ex_el H3.
ex_el H3.
both H3.
take H2 x.
apply_b H3.
split.
take H1 x.
apply_b H3.
rename x into p.
rename x0 into x.
ex_in x.
split.
take H x.
apply_b H3.
ex_el H6.
both H6.
ex_in y.
ass.
ex_el H6.
both H6.
ex_in z.
split.
take H0 z.
apply_b H6.
ex_in y.
ass.
ass.
apply H4.
apply any_biimpl_set_is_no_more_than_one.
Qed.

Definition composition(g f: Set)
:= ι _ (composition_ex g f).

Notation "g ∘ f" := 
(composition g f) (at level 60, left associativity).

Ltac pick H:=
let L := fresh "L" in
let R := fresh "R" in
let function := fresh "function" in
let on := fresh "on" in
let into := fresh "into" in
match type of H with
| function_on_into ?f ?A ?B => pose proof conj_el_1 _ _ H as L;
pose proof conj_el_1 _ _ L as function;
pose proof conj_el_2 _ _ L as on;
pose proof conj_el_2 _ _ H as into;
clear L
end.

Theorem subset_of_p_relatives (f A B: Set) (H: A ⊆ B): 
f [A] ⊆ f [B].
intro.
intro.
extract_iota (f [A]) H0.
extract_iota_from_goal (f [B]).
take iota_prop x.
left H1 H0.
take iota_prop0 x.
apply_b H3.
ex_el H2.
both H2.
take H x0 H3.
ex_in x0.
split.
ass.
ass.
Qed.

Theorem conj_symm (A B: Prop): (A ∧ B) -> (B ∧ A).
intro.
both H.
split.
ass.
ass.
Qed.

Ltac grab_function_domain f :=
  lazymatch goal with
  | H : (function_on_into f ?A ?B) |- _ => exact A
  | _ => fail "Unable to grab function domain"
  end.

Ltac grab_function_range f :=
  lazymatch goal with
  | H : (function_on_into f ?A ?B) |- _ => exact B
  | _ => fail "Unable to grab function domain"
  end.

(* Don't use it !!! Why:
1) it is weaker than inverse_property because ∃x. ∃y
2) Impossible to prove uniqueness because these sets can contain some extra
 trash
*)
Definition inverse_property_weak(f f_inv: Set) := 
∀x. ∀y. (<x, y> ∈ f) ⇔ (<y, x> ∈ f_inv).

Definition inverse_property (f f_inv: Set) :=
∀p. (p ∈ f_inv) ⇔ (∃x. ∃y. (p = <x,y>) ∧ (<y,x> ∈ f)).

Theorem inverse_property_strong_to_weak(f f_inv: Set):
(inverse_property f f_inv) -> (inverse_property_weak f f_inv).
intro.
unfold inverse_property in H.
unfold inverse_property_weak.
intros x y.
split.
intro.
take H (< y, x >).
apply_b H1.
ex_in y.
ex_in x.
split.
apply eq_refl.
ass.
intro.
take H (< y, x >).
left H1 H0.
ex_el H2.
ex_el H2.
both H2.
apply pair_property in H3.
both H3.
repl H2.
repl H5.
ass.
Qed.


Theorem inverse_exists (f A B: Set) 
(H: function_on_into f A B): ∃1f_inv. 
(inverse_property f f_inv).
split.
take cartesian_product_exists B A.
ex_el H0.
take ZF2_subsets (fun p=> (∃ x . ∃ y . p = (< x, y >) ∧ < y, x >
∈ f)) c.
ex_el H1.
rename b into inv.
ex_in inv.
unfold inverse_property.
intro.
split.
intro.
take H1 x.
left H3 H2.
both H4.
apply H6.
intro.
take H1 x.
apply_b H3.
split.
take H0 x.
apply_b H3.
ex_el H2.
ex_el H2.
both H2.
pick H.
ex_in x0.
split.
take into0 x0.
apply H2.
extract_iota_from_goal (range f).
take iota_prop x0.
apply_b H5.
ex_in y.
ass.
ex_in y.
split.
apply eq_el_1 in on0.
take on0 y.
apply H2.
extract_iota_from_goal (domain f).
take iota_prop y.
apply_b H5.
ex_in x0.
ass.
ass.
apply H2.
apply any_biimpl_set_is_no_more_than_one.
Qed.

Definition inverse(f A B: Set) (H: function_on_into f A B)
:= ι _ (inverse_exists f A B H).

Theorem function_application (f A B: Set) (H : function_on_into f A B):
∀a::A. ∃b. <a, b> ∈ f.
intro a.
intro.
pick H.
unfold on in on0.
apply eq_el_2 in on0.
take on0 a H0.
extract_iota ( domain f) H1.
take iota_prop a.
left H2 H1.
apply H3.
Qed.

Theorem element_of_function_in_domain (f A B x y: Set) 
(H : function_on_into f A B) (H2: < x, y > ∈ f): x ∈ A.
left H.
left H0.
left H1.
right H0.
apply eq_el_1 in H4.
take H4 x.
apply H5.
extract_iota_from_goal (domain f).
take iota_prop x.
apply_b H6.
ex_in y.
apply H2.
Qed.

Theorem element_of_function_in_range (f A B x y: Set) 
(H : function_on_into f A B) (H2: < x, y > ∈ f): y ∈ B.
right H.
take H0 y.
apply H1.
extract_iota_from_goal (range f).
take iota_prop y.
apply_b H3.
ex_in x.
ass.
Qed.

Ltac clear_dup :=
  repeat match goal with
  | H1 : ?P, H2 : ?P |- _ =>
      (* clear the second one; you could pick H1 instead *)
      clear H2
  end.


Theorem SchroderBernstein (A B: Set) (H1: A ≾ B) (H2: B ≾ A): (A ~ B).
take dominated_means_ex_of_function A B H1.
take dominated_means_ex_of_function B A H2.
ex_el H.
ex_el H0.
rename f0 into g.
both H.
both H0.
assert (∃A1. A1 ⊆ A ∧ (g [B - f [A1]]) = (A - A1)).
take power_set_exists A.
ex_el H0.
rename b into subsets_of_A.
take ZF2_subsets (fun A0 => (A - g[B] ⊆ A0) ∧ ((g ∘ f)[A0] ⊆ A0 )) subsets_of_A.
ex_el H6.
rename b into alpha.
change (∀ A0. A0 ∈ alpha ⇔ (A0 ∈ subsets_of_A
∧ (A - g [B] ⊆ A0 ∧ ((g ∘ f) [A0]) ⊆ A0))) in H6.
assert (A ∈ alpha).
take H6 A.
apply_b H7.
split.
take H0 A.
apply_b H7.
apply subset_refl.
split.
intro.
intro.
apply relative_complement_el in H7.
both H7.
apply H8.
(* g ∘ f [A] ⊆ A *)
intro p.
intro.
extract_iota (g ∘ f [A]) H7.
take iota_prop p.
left H8 H7.
ex_el H9.
both H9.
extract_iota (g ∘ f) H11.
take iota_prop0 (< x, p >).
left H9 H11.
ex_el H12.
ex_el H12.
both H12.
apply pair_property in H13.
both H13.
ex_el H14.
both H14.
repl <- H15 in H16.
pick H.
unfold into in into0.
take into0 p.
apply H14.
extract_iota_from_goal ( range g).
take iota_prop1 p.
apply_b H17.
ex_in y.
ass.
assert (alpha ≠ ∅).
intro.
apply eq_el_1 in H8.
take H8 A H7.
apply any_set_in_empty_set_causes_contradiction in H9.
apply H9.
take intersection_exists alpha H8.
ex_el H9.
rename a into A1.
assert (A1 ∈ alpha).
take H6 A1.
apply_b H10.
split.
take H0 A1.
apply_b H10.
intro k.
intro.
take H9 k.
left H11 H10.
take H12 A.
apply H13.
apply H7.
split.
(* A - g [B] ⊆ A1 *)
intro k.
intro.
apply relative_complement_el in H10.
both H10.
take H9 k.
apply_b H10.
intro.
intro.
take H6 x.
left H13 H10.
right H14.
left H15.
take H16 k.
apply H17.
apply relative_complement_in.
split.
ass.
ass.
(* g ∘ f [A1] ⊆ A1 *)
assert (∀A0::alpha. (((g ∘ f)[A1] ⊆ (g ∘ f) [A0])) ∧ ((g ∘ f) [A0] ⊆ A0)).
intro A0.
intro.
split.
(* g ∘ f [A1] ⊆ g ∘ f [A0] *)
apply subset_of_p_relatives.
intro a.
intro.
take H9 a.
left H12 H11.
take H13 A0 H10.
apply H14.
take H6 A0.
left H11 H10.
right H12.
right H13.
apply H14.
assert (∀ A0 :: alpha . g ∘ f [A1] ⊆ A0).
intro A0.
intro.
take H10 A0 H11.
both H12.
take subset_trans _ _ _ H13 H14.
ass.
(* g ∘ f [A1] ⊆ A1 *)
intro el.
intro.
take H9 el.
apply_b H13.
intro.
intro.
take H11 x H13.
take H14 el H12.
apply H15.
(* first page finished, A1 ∈ alpha proven*)
ex_in A1.
split.
take H6 A1.
left H11 H10.
left H12.
take H0 A1.
left H14 H13.
apply H15.
(* (g [B - f [A1]]) = (A - A1) *)
apply eq_in_backward.
take H6 A1.
left H11 H10.
both H12.
both H14.
assert (A - A1 ⊆ g [B]).
intro.
intro.
apply relative_complement_el in H14.
both H14.
take H12 x.
take contrapositive H14.
take H18 H17.
apply relative_complement_el_alt in H19.
apply (disj_el _ _ _ H19).
intro.
apply (H20 H16).
intro.
ass.
take H6 A1.
left H16 H10.
both H17.
both H19.
clear H16 H18 H17.
rename H14 into first.
rename H20 into second.
intro.
intro.
apply relative_complement_el in H14.
both H14.
extract_iota_from_goal (f [A1]).
rename s into f_A1.
extract_iota_from_goal (g [B - f_A1]).
take iota_prop0 x.
apply_b H14.
take first x.
assert (x ∈ (A - A1)).
apply relative_complement_in.
split; ass.
take H14 H18.
extract_iota (g [B]) H19.
take iota_prop1 x.
left H20 H19.
ex_el H21.
both H21.
rename x0 into y.
ex_in y.
split.
apply relative_complement_in.
split.
ass.
intro.
take iota_prop y.
left H24 H21.
ex_el H25.
both H25.
rename x0 into y0.
take second x.
apply contrapositive in H25.
assert (<y0, x> ∈ g ∘ f).
extract_iota_from_goal (g ∘ f).
take iota_prop2 (< y0, x >).
apply_b H28.
ex_in y0.
ex_in x.
split.
apply eq_refl.
ex_in y.
split; ass.
apply H25.
extract_iota_from_goal (g ∘ f [A1]).
take iota_prop2 x.
apply_b H29.
ex_in y0.
split.
ass.
ass.
ass.
apply H23.
assert (((A - g[B]) ∪ ((g ∘ f) [A1])) = A1).
take H6 A1.
left H11 H10.
right H12.
both H13.
assert(A - g [B] ∪ g ∘ f [A1] ⊆ A1).
intro.
intro.
apply union_el in H13.
apply (disj_el _ _ _ H13).
intro.
apply (H14 x).
ass.
intro.
take H15 x.
apply H17.
ass.
apply eq_in.
apply H13.
take subset_of_p_relatives (g ∘ f) ( A - g [B] ∪ g ∘ f [A1]) A1 H13.
assert (A - g [B] ∪ g ∘ f [A1] ∈ alpha).
rename H16 into condition.
take H6 (A - g [B] ∪ g ∘ f [A1]).
apply_b H16.
(* 3 cases *)
apply conj_symm.
split.
split.
intros x HH.
apply union_in.
left.
apply HH.
intros x HH.
apply union_in.
right.
take  condition x.
apply H16.
apply HH.
(* last case *)
take H0 (A - g [B] ∪ g ∘ f [A1]).
apply_b H16.
intro z.
intro.
apply union_el in H16.
apply (disj_el _ _ _ H16).
intro.
apply relative_complement_el in H17.
both H17.
ass.
intro.
take H15 z H17.
take H9 z.
left H19 H18.
take H20 A.
apply H21.
apply H7.
intro z.
intro.
take H9 z.
left H19 H18.
take H20 (A - g [B] ∪ g ∘ f [A1]) H17.
apply H21.
rename H11 into main_condition.
(* g [B - f [A1]] ⊆ (A - A1)  *)
intro z.
intro.
apply relative_complement_in.
apply conj_symm.
split.
(* disjoint proof is here *)
intro.
apply eq_el_2 in main_condition.
take main_condition z H12.
clear H12.
extract_iota (f [A1]) H11.
rename s into f_A1.
extract_iota (g [B - f_A1]) H11.
take iota_prop0 z.
left H12 H11.
clear iota_prop0 H12.
ex_el H14.
rename x into b.
both H14.
apply relative_complement_el in H12.
both H12.
assert (z ∈ g [B]).
extract_iota_from_goal (g [B]).
take iota_prop0 z. 
apply_b H12.
ex_in b.
split;ass.
apply union_el in H13.
apply (disj_el _ _ _ H13).
intro.
apply relative_complement_el in H17.
both H17.
apply H19.
apply H12.
intro.
(* first condition done *)
clear H13.
take iota_prop b.
right H13.
apply contrapositive in H18.
clear H13.
clear H16.
apply ex_el_alt_simple in H18.
extract_iota (g ∘ f [A1]) H17.
take iota_prop0 z.
left H13 H17.
ex_el H16.
clear H13.
both H16.
extract_iota (g ∘ f) H19.
take iota_prop1 (< x, z >).
left H16 H19.
clear H16.
ex_el H20.
ex_el H20.
both H20.
apply pair_property in H16.
both H16.
repl <- H20 in H21.
repl <- H22 in H21.
ex_el H21.
both H21.
clear H20 H22.
clear iota_prop1.
take H5 b y z.
take conj_in _ _ H15 H23.
take H20 H21.
repl <- H22 in H16.
take H18 x.
apply H24.
split.
ass.
ass.
apply H16.
(* disjoint proof successfully done*)
pick H.
extract_iota (f [A1]) H11.
rename s into f_A1.
extract_iota (g [B - f_A1]) H11.
take iota_prop0 z.
left H12 H11.
ex_el H13.
both H13.
unfold into in into0.
take into0 z.
apply H13.
extract_iota_from_goal (range g).
take iota_prop1 z.
apply_b H16.
ex_in x.
apply H15.
(* A ~ B *)
take cartesian_product_exists A B.
ex_el H6.
ex_el H0.
both H0.
rename c into AxB.
take inverse_exists g B A H.
ex_el H0.
rename f_inv into g_inv.
unfold inverse_property in H0.
take ZF2_subsets (fun p => ∀x. ∀y. (p = <x,y>) -> 
((x ∈ A1) -> <x, y> ∈ f)
∧ ((x ∈ (A - A1)) -> <x, y> ∈ g_inv)) AxB.
ex_el H9.
rename b into h.
change (∀ p. p ∈ h⇔ (p ∈ AxB
∧ (∀ x. ∀ y. (p = (< x, y >)) -> ((x ∈ A1 -> < x, y > ∈ f)
∧ (x ∈ (A - A1) -> < x, y > ∈ g_inv))))) in H9.
assert (one_to_one g_inv) as g_inv_is_one_to_one.
intros x y z.
apply inverse_property_strong_to_weak in H0.
unfold inverse_property_weak in H0.
intro.
both H10.
take H0 z x.
right H10.
take H13 H11.
take H0 z y.
right H15.
take H16 H12.
pick H.
right function0.
take H18 z x y.
apply H19.
split.
ass.
ass.
assert (function g_inv) as g_inv_is_function.
split.
intro.
intro.
take H0 x.
left H11 H10.
ex_el H12.
ex_el H12.
both H12.
ex_in x0.
ex_in y.
ass.
intros x y z.
intro.
both H10.
take H0.
apply inverse_property_strong_to_weak in H10.
take H10 y x.
right H13.
take H14 H11.
take H10 z x.
right H16.
take H17 H12.
apply (H5 y z x).
split; ass.
apply inverse_property_strong_to_weak in H0.
unfold inverse_property_weak in H0.
ex_in h.
split.
split.
split.
split.
intro p.
intro.
take H9 p.
left H11 H10.
both H12.
take H6 p.
left H12 H13.
ex_el H15.
both H15.
ex_el H17.
both H17.
ex_in x.
ex_in y.
apply H18.
intros x y z.
intro.
both H10.
take H9 ( < x, y >).
left H10 H11.
right H13.
take H14 x y.
assert ((< x, y >) = (< x, y >)).
apply eq_refl.
take H15 H16.
both H17.
take H9 ( < x, z >).
left H17 H12.
right H20.
take H21 x z.
assert ((< x, z >) = (< x, z >)).
apply eq_refl.
take H22 H23.
both H24.
clear H17 H20 H21 H22 H23.
assert (x ∈ A).
take H6 (< x, y >).
left H17.
left H13.
take H20 H21.
ex_el H22.
both H22.
ex_el H24.
both H24.
apply pair_property in H27.
both H27.
repl H24.
apply H23.
take exc_thrd (x ∈ A1).
apply (disj_el _ _ _ H20).
intro.
take H18 H21.
take H25 H21.
pick H3.
right function0.
take H24 x y z.
apply H27.
split; ass.
intro.
assert (x ∈ A ∧ x ∉ A1).
split; ass.
take relative_complement_in _ _ x H22.
take H19 H23.
take H26 H23.
right g_inv_is_function.
take H28 x y z.
apply H29.
split.
ass.
ass.
(* on h A *)
apply eq_in.
intro.
intro.
extract_iota (domain h) H10.
take iota_prop x.
left H11 H10.
ex_el H12.
take H9 (< x, y >).
left H13 H12.
left H14.
take H6 (< x, y >).
left H16 H15.
ex_el H17.
both H17.
ex_el H19.
both H19.
apply pair_property in H20.
both H20.
repl H19.
ass.
intros x HH.
extract_iota_from_goal (domain h).
take iota_prop x.
apply_b H10.
clear iota_prop s.
take exc_thrd (x ∈ A1).
apply (disj_el _ _ _ H10).
intro.
take function_application  _ _ _ H3 x HH.
ex_el H12.
rename b into y.
ex_in y.
take H9 (< x, y >).
apply_b H13.
split.
take H6 (< x, y >).
apply_b H13.
ex_in x.
split.
take element_of_function_in_domain f A B x y H3 H12.
ass.
ex_in y.
split.
take element_of_function_in_range f A B x y H3 H12.
ass.
apply eq_refl.
intros x0 y0.
intro.
apply pair_property in H13.
both H13.
repl <- H14.
repl <- H15.
split.
intro.
ass.
intro.
apply relative_complement_el in H13.
both H13.
apply (H17 H11).
intro.
assert (x ∈ A ∧ x ∉ A1).
split; ass.
take relative_complement_in A A1 x H12.
clear H12 H10.
(* try *)
apply eq_el_2 in H8.
take H8 x H13.
extract_iota (f [A1]) H10.
rename s into f_A1.
extract_iota (g [B - f_A1]) H10.
take iota_prop0 x.
left H12 H10.
ex_el H14.
rename x0 into y.
both H14.
take H0 y x.
left H14 H16.
ex_in y.
take H9 (< x, y >).
apply_b H18.
split.
take H6 (< x, y >).
apply_b H18.
ex_in x.
split.
take element_of_function_in_range g B A y x H H16.
ass.
ex_in y.
split.
take element_of_function_in_domain g B A y x H H16.
ass.
apply eq_refl.
intros x0 y0.
intro.
apply pair_property in H18.
both H18.
repl <- H19.
repl <- H20.
split.
intro.
apply (H11 H18).
intro.
apply H17.
(* onto h B *)
2:{
  intros a b y.
  intro.
  both H10.
  take H9 (< a, y >).
  left H10 H11.
  both H13.
  take H15 a y.
  assert ((< a, y >) = (< a, y >)).
  apply eq_refl.
  take H13 H16.
  both H17.
  take H9 (< b, y >).
  left H17 H12.
  both H20.
  take H22 b y.
  assert ((< b, y >) = (< b, y >)).
  apply eq_refl.
  take H20 H23.
  both H24.
  clear H17 H21 H22 H20 H23.
  move H25 before H18.
  clear H16 H13 H15.
  take exc_thrd (a ∈ A1).
  apply (disj_el _ _ _ H13).
  intro.
  take exc_thrd (b ∈ A1).
  apply (disj_el _ _ _ H16).
  intro.
  clear H13 H16.
  take H18 H15.
  take H25 H17.
  take H4 a b y.
  apply H20.
  split; ass.
  intro.
  assert (b ∈ A).
  take H9 (< b, y >).
  left H20 H12.
  left H21.
  take H6 (< b, y >).
  left H23 H22.
  ex_el H24.
  both H24.
  ex_el H28.
  both H28.
  apply pair_property in H29.
  both H29.
  repl H28.
  ass.
  assert ((b ∈ A ∧ b ∉ A1)).
  split; ass.
  take relative_complement_in A A1 b H21.
  take H18 H15.
  take H26 H22.
  (* try to derive a contradiction *)
  take H0 y b.
  right H27.
  take H28 H24.
  clear H28 H27.
  take H8.
  apply eq_el_2 in H27.
  take H27 b.
  take H28 H22.
  clear H27 H28.
  extract_iota (f [A1]) H30.
  extract_iota (g [B - s]) H30.
  take iota_prop0 b.
  left H27 H30.
  ex_el H28.
  both H28.
  apply relative_complement_el in H31.
  both H31.
  assert ( (< x, b > ∈ g ∧ < y, b > ∈ g)).
  split; ass.
  take H5 x y b H31.
  repl H34 in H32.
  repl H34 in H28.
  repl H34 in H33.
  clear H31 H34.
  clear H32.
  take iota_prop y.
  right H31.
  apply contrapositive in H32.
  apply ex_el_alt_simple in H32.
  take H32 a.
  apply abs_el.
  apply H34.
  split.
  ass.
  apply H23.
  ass.
  intro.
  (* branch 2 -- a ∉ A1*)
  take exc_thrd (b ∈ A1).
  apply (disj_el _ _ _ H16).
  intro.
  clear H13 H16.
  assert (a ∈ (A - A1)).
  apply relative_complement_in.
  split.
  take H6 (< a, y >).
  left H13 H14.
  ex_el H16.
  both H16.
  ex_el H21.
  both H21.
  apply pair_property in H22.
  both H22.
  repl H21.
  ass.
  ass.
  take H8.
  apply eq_el_2 in H16.
  take H16 a H13.
  extract_iota (f [A1]) H20.
  extract_iota (g [B - s]) H20.
  take iota_prop0 a.
  left H21 H20.
  ex_el H22.
  both H22.
  apply relative_complement_el in H23.
  both H23.
  take iota_prop x.
  right H23.
  take @contrapositive (∃ x0 :: A1 . < x0, x > ∈ f) (x ∈ s) H28.
  apply contrapositive in H28.
  take H29 H27.
  apply ex_el_alt_simple in H30.
  take H30 b.
  apply abs_el.
  apply H31.
  split.
  ass.
  take H19 H13.
  take H25 H17.
  take H0 x a.
  left H34 H24.
  right g_inv_is_function.
  take H36 a y x.
  assert ((< a, y > ∈ g_inv ∧ < a, x > ∈ g_inv)).
  split; ass.
  take H37 H38.
  repl <- H39.
  ass.
  ass.
  intro.
  assert (a ∈ (A - A1)).
  apply relative_complement_in.
  split.
  take H6 (< a, y >).
  left H20 H14.
  ex_el H21.
  both H21.
  ex_el H23.
  both H23.
  apply pair_property in H24.
  both H24.
  repl H23.
  ass.
  ass.
  assert (b ∈ (A - A1)).
  apply relative_complement_in.
  split.
  take H6 (< b, y >).
  take H9 (< b, y >).
  left H22 H12.
  left H23.
  take H6 (< b, y >).
  left H27 H24.
  ex_el H28.
  both H28.
  ex_el H30.
  both H30.
  apply pair_property in H31.
  both H31.
  repl H30.
  ass.
  ass.
  take H19 H20.
  take H26 H21.
  take g_inv_is_one_to_one a b y.
  apply H24.
  split; ass.
}
(* onto h B *)
apply eq_in.
intro b.
intro.
extract_iota (range h) H10.
take iota_prop b.
left H11 H10.
ex_el H12.
take H9 (< x, b >).
left H13 H12.
left H14.
take H6 (< x, b >).
left H16 H15.
ex_el H17.
both H17.
ex_el H19.
both H19.
apply pair_property in H20.
both H20.
repl H21.
ass.
intro b.
intro.
extract_iota_from_goal (range h).
rename s into range_h.
take iota_prop b.
apply_b H11.
take exc_thrd (b ∈ f [A1]).
(* b ∈ f [A1] ∨ b ∉ f [A1] *)
apply (disj_el _ _ _ H11).
intro.
extract_iota (f [A1]) H12.
take iota_prop0 b.
left H13 H12.
ex_el H14.
both H14.
take H9 (< x, b >).
ex_in x.
apply_b H14.
split.
take H6 (< x, b >).
apply_b H14.
ex_in x.
split.
take element_of_function_in_domain f A B x b H3 H16.
ass.
ex_in b.
split.
take element_of_function_in_range f A B x b H3 H16.
ass.
apply eq_refl.
intro.
intro.
intro.
apply pair_property in H14.
both H14.
repl <- H17.
repl <- H18.
split.
intro.
apply H16.
intro.
apply relative_complement_el in H14.
both H14.
apply (H20 H15).
intro.
assert (b ∈ (B - f [A1])).
apply relative_complement_in.
split;ass.
take H8.
clear H11.
take function_application g B A H b H10.
ex_el H11.
rename b0 into a.
assert (a ∈ g [B - f [A1]]).
extract_iota_from_goal (f [A1]).
extract_iota_from_goal (g [B - s]).
take iota_prop1 a.
apply_b H15.
ex_in b.
split.
apply relative_complement_in.
split.
ass.
take iota_prop0 b.
left H15.
take @contrapositive (b ∈ s) (∃ x :: A1 . < x, b > ∈ f) H16.
apply H17.
intro.
ex_el H18.
both H18.
apply H12.
extract_iota_from_goal (f [A1]).
take iota_prop2 b.
apply_b H18.
ex_in x.
split;ass.
ass.
apply eq_el_1 in H14.
take H14 a H15.
ex_in a.
take H9 (< a, b >).
apply_b H17.
split.
take H6 (< a, b >).
apply_b H17.
ex_in a.
split.
take element_of_function_in_range g B A b a H H11.
ass.
ex_in b.
split.
take element_of_function_in_domain g B A b a H H11.
ass.
apply eq_refl.
intros x y HH.
apply pair_property in HH.
both HH.
repl <- H17.
repl <- H18.
split.
apply relative_complement_el in H16.
right H16.
intro.
apply (H19 H20).
intro.
take H0 b a.
left H20.
apply H21.
apply H11.
Qed.





