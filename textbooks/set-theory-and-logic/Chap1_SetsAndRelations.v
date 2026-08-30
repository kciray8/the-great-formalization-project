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

Tactic Notation "take" uconstr(a) uconstr(b) uconstr(c) uconstr(d) uconstr(e) uconstr(f) uconstr(g) uconstr(h) uconstr(i) uconstr(j) :=
  take_core (a b c d e f g h i j).

Tactic Notation "take" uconstr(a) uconstr(b) uconstr(c) uconstr(d) uconstr(e) uconstr(f) uconstr(g) uconstr(h) uconstr(i) uconstr(j) uconstr(p) :=
  take_core (a b c d e f g h i j p).

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

Theorem intersection_in_alt: ∀A. ∀B. ∀x. (x ∈ A) ∧ (x ∈ B) -> x ∈ (A ∩ B).
intros A B x.
intro.
extract_iota_from_goal ((A ∩ B)).
take iota_prop x.
right H0.
apply H1.
ass.
Qed.

Theorem intersection_in (A B x: Set) (H1: x ∈ A) (H2: x ∈ B): x ∈ (A ∩ B).
extract_iota_from_goal ((A ∩ B)).
take iota_prop x.
right H.
apply H0.
split; ass.
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
apply intersection_in_alt.
split.
ass.
ass.
intro.
right.
apply intersection_in_alt.
split.
ass.
ass.
intro.
apply union_el in H.
apply intersection_in_alt.
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
apply intersection_in_alt.
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

Definition relative_complement_annihilation: ∀A. ((A - A) = ∅).
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
apply intersection_in_alt.
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
apply intersection_in_alt.
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
apply intersection_in_alt.
split.
ass.
ass.
intro.
take H x H2.
take union_in_2 B C x H2.
apply intersection_in_alt.
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
apply intersection_in_alt.
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
take intersection_in_alt A B x H9.
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
apply intersection_in_alt.
apply intersection_el in H.
both_old H.
apply intersection_el in H1.
both_old H1.
split.
apply intersection_in_alt.
split; ass.
ass.
apply intersection_in_alt.
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
apply intersection_in_alt.
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
apply intersection_in_alt.
apply intersection_el in H.
both_old H.
split.
ass.
ass.
apply intersection_in_alt.
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
apply intersection_in_alt.
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
apply intersection_in_alt.
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
apply intersection_in_alt.
split; ass.
apply union_in.
right.
apply intersection_in_alt.
split; ass.
apply union_el in H.
disj H.
apply intersection_el in H0.
both H0.
apply intersection_in_alt.
split.
ass.
apply union_in.
left.
ass.
apply intersection_el in H0.
both H0.
apply intersection_in_alt.
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
apply intersection_in_alt.
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
take intersection_in_alt A B x H3.
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
apply intersection_in_alt.
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
apply intersection_in_alt.
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

Lemma intersection_in_alt_neg: ∀A. ∀B. ∀x. ((x ∉ A) ∨ (x ∉ B)) 
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
apply intersection_in_alt.
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
apply intersection_in_alt.
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

Lemma intersection_in_alt_subset: ∀A. ∀B. ∀U.
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
take intersection_in_alt_subset _ _ _ aU H.
take intersection_in_alt_subset _ _ _ H1 cU.
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

Definition universal_relation_in_x (X: Set) := (X × X).
Definition void_relation := ∅.

Definition identity_relation_prop(X i: Set) := 
(∀p. ((p ∈ i) ⇔ (∃x:: X. p = ⟨x, x⟩))).

Definition identity_relation_exists (X: Set): ∃1i.
identity_relation_prop X i.
split.
take cartesian_product_exists X X.
left H.
clear H.
cbv beta in H0.
change (∃ s1. (∀ w . ((w ∈ s1) ⇔ 
(∃ x :: X . (∃ y :: X . (w = (⟨ x, y ⟩))))))) in H0.
apply (ex_el _ H0).
intros s1 P.
clear H0.
take ZF2_subsets (fun g => (∃ z :: X . (g = (⟨ z, z ⟩)))) s1.
apply (ex_el _ H).
intros s2.
intros P0.
2:{
  apply any_biimpl_set_is_no_more_than_one.
}
change (∃ s. (∀ p . ((p ∈ s) ⇔ 
(∃ x :: X . (p = (⟨ x, x ⟩)))))).
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

Ltac ex_el_named H Name :=
match type of H with
|∃ x. _ =>
let H2 := fresh "H2" in
apply (ex_el _ H);
intros Name H2;
move Name before H;
move H2 before Name;
clear H;
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
∃1s. (∀y. (y ∈ s) ⇔ ∃x::A. ⟨x, y⟩ ∈ r).
split.
take range_exists r.
ex_el H.
take ZF2_subsets (fun y => (∃ x :: A . ⟨ x, y ⟩ ∈ r)) d.
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

Definition ordered_pair (s: Set) := ∃a. ∃b. s = ⟨a, b⟩.

Definition function (s: Set) := 
(* I *) (∀x. x ∈ s -> ordered_pair x) ∧
(* II *) (∀x. ∀y. ∀z. ((⟨x, y⟩ ∈ s ∧ ⟨x, z⟩ ∈ s) -> y = z)).

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

Definition one_to_one (s: Set) := (∀a. ∀b. ∀y. ((⟨a, y⟩ ∈ s ∧ ⟨b, y⟩ ∈ s) -> a = b)).

Definition bijection (f A B: Set) :=
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

Definition similar (A B: Set) := ∃f. bijection f A B.

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

Definition appl_ex_deprecated (f: Set) (X Y: Set) (H: function_on_into f X Y) (x: Set) 
(x_in_X: x ∈ X):
 ∃1y. (y ∈ Y) ∧ (⟨x,y⟩ ∈ f).
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

Definition appl_deprecated (f: Set) (X Y: Set) 
(H: function_on_into f X Y) (x: Set) (x_in_X: x ∈ X) := 
ι _ (appl_ex_deprecated f X Y H x x_in_X).

Theorem composition_ex(g f: Set): ∃1c. ∀p. (p ∈ c) ⇔ 
∃x. ∃z. (p = ⟨x, z⟩) ∧ ∃y. ⟨x,y⟩ ∈ f ∧ ⟨y,z⟩ ∈ g.
take domain_exists f.
ex_el H.
rename d into dom_f.
take range_exists g.
ex_el H0.
rename d into ran_g.
take cartesian_product_exists dom_f ran_g.
ex_el H1.
take ZF2_subsets (fun p => ∃x. ∃z. (p = ⟨x, z⟩) ∧ ∃y. ⟨x,y⟩ ∈ f ∧ ⟨y,z⟩ ∈ g) c.
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
  | _ => fail "Unable to grab function range"
  end.

(* Don't use it !!! Why:
1) it is weaker than inverse_property because ∃x. ∃y
2) Impossible to prove uniqueness because these sets can contain some extra
 trash
*)
Definition inverse_property_weak(f f_inv: Set) := 
∀x. ∀y. (⟨x, y⟩ ∈ f) ⇔ (⟨y, x⟩ ∈ f_inv).

Definition inverse_property (f f_inv: Set) :=
∀p. (p ∈ f_inv) ⇔ (∃x. ∃y. (p = ⟨x,y⟩) ∧ (⟨y,x⟩ ∈ f)).

Theorem inverse_property_strong_to_weak(f f_inv: Set):
(inverse_property f f_inv) -> (inverse_property_weak f f_inv).
intro.
unfold inverse_property in H.
unfold inverse_property_weak.
intros x y.
split.
intro.
take H (⟨ y, x ⟩).
apply_b H1.
ex_in y.
ex_in x.
split.
apply eq_refl.
ass.
intro.
take H (⟨ y, x ⟩).
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
take ZF2_subsets (fun p=> (∃ x . ∃ y . p = (⟨ x, y ⟩) ∧ ⟨ y, x ⟩
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
∀a::A. ∃b. ⟨a, b⟩ ∈ f.
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
(H : function_on_into f A B) (H2: ⟨ x, y ⟩ ∈ f): x ∈ A.
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
(H : function_on_into f A B) (H2: ⟨ x, y ⟩ ∈ f): y ∈ B.
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
take iota_prop0 (⟨ x, p ⟩).
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
assert (⟨y0, x⟩ ∈ g ∘ f).
extract_iota_from_goal (g ∘ f).
take iota_prop2 (⟨ y0, x ⟩).
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
take iota_prop1 (⟨ x, z ⟩).
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
take ZF2_subsets (fun p => ∀x. ∀y. (p = ⟨x,y⟩) -> 
((x ∈ A1) -> ⟨x, y⟩ ∈ f)
∧ ((x ∈ (A - A1)) -> ⟨x, y⟩ ∈ g_inv)) AxB.
ex_el H9.
rename b into h.
change (∀ p. p ∈ h⇔ (p ∈ AxB
∧ (∀ x. ∀ y. (p = (⟨ x, y ⟩)) -> ((x ∈ A1 -> ⟨ x, y ⟩ ∈ f)
∧ (x ∈ (A - A1) -> ⟨ x, y ⟩ ∈ g_inv))))) in H9.
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
take H9 ( ⟨ x, y ⟩).
left H10 H11.
right H13.
take H14 x y.
assert ((⟨ x, y ⟩) = (⟨ x, y ⟩)).
apply eq_refl.
take H15 H16.
both H17.
take H9 ( ⟨ x, z ⟩).
left H17 H12.
right H20.
take H21 x z.
assert ((⟨ x, z ⟩) = (⟨ x, z ⟩)).
apply eq_refl.
take H22 H23.
both H24.
clear H17 H20 H21 H22 H23.
assert (x ∈ A).
take H6 (⟨ x, y ⟩).
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
take H9 (⟨ x, y ⟩).
left H13 H12.
left H14.
take H6 (⟨ x, y ⟩).
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
take H9 (⟨ x, y ⟩).
apply_b H13.
split.
take H6 (⟨ x, y ⟩).
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
take H9 (⟨ x, y ⟩).
apply_b H18.
split.
take H6 (⟨ x, y ⟩).
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
  take H9 (⟨ a, y ⟩).
  left H10 H11.
  both H13.
  take H15 a y.
  assert ((⟨ a, y ⟩) = (⟨ a, y ⟩)).
  apply eq_refl.
  take H13 H16.
  both H17.
  take H9 (⟨ b, y ⟩).
  left H17 H12.
  both H20.
  take H22 b y.
  assert ((⟨ b, y ⟩) = (⟨ b, y ⟩)).
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
  take H9 (⟨ b, y ⟩).
  left H20 H12.
  left H21.
  take H6 (⟨ b, y ⟩).
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
  assert ( (⟨ x, b ⟩ ∈ g ∧ ⟨ y, b ⟩ ∈ g)).
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
  take H6 (⟨ a, y ⟩).
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
  take @contrapositive (∃ x0 :: A1 . ⟨ x0, x ⟩ ∈ f) (x ∈ s) H28.
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
  assert ((⟨ a, y ⟩ ∈ g_inv ∧ ⟨ a, x ⟩ ∈ g_inv)).
  split; ass.
  take H37 H38.
  repl <- H39.
  ass.
  ass.
  intro.
  assert (a ∈ (A - A1)).
  apply relative_complement_in.
  split.
  take H6 (⟨ a, y ⟩).
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
  take H6 (⟨ b, y ⟩).
  take H9 (⟨ b, y ⟩).
  left H22 H12.
  left H23.
  take H6 (⟨ b, y ⟩).
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
take H9 (⟨ x, b ⟩).
left H13 H12.
left H14.
take H6 (⟨ x, b ⟩).
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
take H9 (⟨ x, b ⟩).
ex_in x.
apply_b H14.
split.
take H6 (⟨ x, b ⟩).
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
take @contrapositive (b ∈ s) (∃ x :: A1 . ⟨ x, b ⟩ ∈ f) H16.
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
take H9 (⟨ a, b ⟩).
apply_b H17.
split.
take H6 (⟨ a, b ⟩).
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


Definition similarity_relation_exists (U: Set): ∃1r.
(∀p. ((p ∈ r) ⇔ (∃x. x ∈ (𝒫 U) ∧ ∃y. y ∈ (𝒫 U) ∧ ((p = ⟨x, y⟩) ∧ (x ~ y))))).
split.
take cartesian_product_exists (𝒫 U) (𝒫 U).
ex_el H.
take ZF2_subsets (fun p => ∃x. ∃y. (p = ⟨x, y⟩) ∧ (x ~ y)) c.
ex_el H0.
ex_in b.
intro.
split.
intro.
take H0 x.
left H2 H1.
both H3.
take H x.
left H3 H4.
ex_el H6.
both H6.
ex_el H8.
both H8.
ex_in x0.
split.
ass.
ex_in y.
split.
ass.
split.
ass.
ex_el H5.
ex_el H5.
both H5.
repl H9 in H8.
apply pair_property in H8.
both H8.
repl H5.
repl H11.
ass.
intro.
ex_el H1.
both H1.
ex_el H3.
both H3.
both H4.
take H0 x.
apply_b H4.
split.
take H x.
apply_b H4.
ex_in x0.
split. ass.
ex_in y.
split. ass.
ass.
ex_in x0.
ex_in y.
split; ass.
apply any_biimpl_set_is_no_more_than_one.
Qed.

Definition similarity_relation (U: Set): Set := 
ι _ (similarity_relation_exists U).

Definition equivalence_class_gen_by (x r: Set): Set := p_relatives (unit_set x) r.

(* deprecated *)
Definition card_eq_class (U x: Set):= equivalence_class_gen_by x (similarity_relation U).

Definition element_in_power_set (A B: Set) (H: A ⊆ B): A ∈ power_set B.
extract_iota_from_goal ( 𝒫 B).
take iota_prop A.
apply_b H0.
ass.
Qed.

Definition identity_relation_is_bijection (X i: Set)
(H: identity_relation_prop X i): bijection i X X.
unfold bijection.
unfold identity_relation_prop in H.
split.
split.
split.
unfold function.
split.
intro.
intro.
take H x.
left H1 H0.
ex_el H2.
both H2.
ex_in x0.
ex_in x0.
ass.
intros x y z.
intro.
both H0.
take H (⟨ x, y ⟩).
left H0 H1.
take H (⟨ x, z ⟩).
left H4 H2.
ex_el H3.
both H3.
ex_el H5.
both H5.
apply pair_property in H7.
both H7.
apply pair_property in H8.
both H8.
apply eq_symm in H9.
take eq_trans _ _ _ H5 H9.
apply eq_symm in H10.
take eq_trans _ _ _ H7 H10.
apply eq_symm in H11.
take eq_trans _ _ _ H11 H8.
apply eq_symm.
ass.
unfold on.
apply eq_in.
intro.
intro.
extract_iota (domain i) H0.
take iota_prop x.
left H1 H0.
ex_el H2.
take H ( ⟨ x, y ⟩ ).
left H3 H2.
ex_el H4.
both H4.
apply pair_property in H6.
both H6.
repl H4.
ass.
intro.
intro.
extract_iota_from_goal (domain i).
take iota_prop x.
apply_b H1.
ex_in x.
take H (⟨ x, x ⟩).
apply_b H1.
ex_in x.
split.
ass.
apply eq_refl.
apply eq_in.
intro.
intro.
extract_iota (range i) H0.
take iota_prop x.
left H1 H0.
ex_el H2.
take H (⟨ x0, x ⟩).
left H3 H2.
ex_el H4.
both H4.
apply pair_property in H6.
both H6.
repl H7.
ass.
intro.
intro.
extract_iota_from_goal (range i).
take iota_prop x.
apply_b H1.
ex_in x.
take H (⟨ x, x ⟩).
apply_b H1.
ex_in x.
split.
ass.
apply eq_refl.
intros a b c.
intro.
both H0.
take H (⟨ a, c ⟩).
take H (⟨ b, c ⟩).
left H0 H1.
left H3 H2.
ex_el H4.
both H4.
ex_el H5.
both H5.
apply pair_property in H7.
both H7.
apply pair_property in H8.
both H8.
apply eq_symm in H10.
take eq_trans _ _ _ H10 H9.
apply eq_symm in H8.
take eq_trans _ _ _ H5 H8.
take eq_trans _ _ _ H9 H8.
apply eq_symm in H7.
take eq_trans _ _ _ H11 H7.
ass.
Qed.


Definition similar_reflective (A: Set): A ~ A.
unfold similar.
take identity_relation_exists A.
ex_el H.
take identity_relation_is_bijection A i H.
ex_in i.
ass.
Qed.

Definition bijection_to_into (f A B: Set)
(H: (bijection f A B)):  function_on_into f A B.
unfold bijection in H.
both H.
both H0.
both H.
split.
split.
ass.
ass.
unfold into.
unfold onto in H2.
repl H2.
apply subset_refl.
Qed.

Definition domain_range_of_inverse (f f_inv: Set) 
(H: inverse_property f f_inv): domain f = range f_inv.
unfold inverse_property in H.
apply eq_in.
intro.
intro.
extract_iota (domain f) H0.
take iota_prop x.
left H1 H0.
ex_el H2.
extract_iota_from_goal ( range f_inv).
take iota_prop0 x.
apply_b H3.
ex_in y.
take H (⟨ y, x ⟩).
apply_b H3.
ex_in y.
ex_in x.
split.
apply eq_refl.
ass.
intro.
intro.
extract_iota (range f_inv) H0.
take iota_prop x.
left H1 H0.
ex_el H2.
extract_iota_from_goal ( domain f).
take iota_prop0 x.
apply_b H3.
take H (⟨ x0, x ⟩).
left H3 H2.
ex_el H4.
ex_el H4.
both H4.
apply pair_property in H5.
both H5.
repl <- H4 in H6.
repl <- H7 in H6.
ex_in x0.
ass.
Qed.

Definition inverse_the_inverse_property (f f_inv: Set) 
(f_is_function: function f)
(H: inverse_property f f_inv): inverse_property f_inv f.
unfold inverse_property.
unfold inverse_property in H.
intro p.
split.
intro.
left f_is_function.
take H1 p H0.
unfold ordered_pair in H2.
ex_el H2.
ex_el H2.
ex_in a.
ex_in b.
split.
ass.
take H (⟨ b, a ⟩).
apply_b H3.
ex_in b.
ex_in a.
split.
apply eq_refl.
repl H2 in H0.
ass.
intro.
ex_el H0.
ex_el H0.
both H0.
take H (⟨ y, x ⟩).
left H0 H2.
ex_el H3.
ex_el H3.
both H3.
apply pair_property in H4.
both H4.
repl <- H3 in H5.
repl <- H6 in H5.
repl H1.
ass.
Qed.



Definition similar_symmetric (A B: Set) (H: A ~ B): B ~ A.
unfold similar in H.
ex_el H.
pose proof H as HH.
both H.
both H0.
both H.
take bijection_to_into f A B HH.
take inverse_exists f A B H.
ex_el H4.
ex_in f_inv.
unfold inverse_property in H4.
split.
split.
split.
split.
intro x.
intro.
take H4 x.
left H6 H5.
ex_el H7.
ex_el H7.
both H7.
unfold ordered_pair.
ex_in x0.
ex_in y.
ass.
intros x y z.
intro.
both H5.
take H4 (⟨ x, y ⟩).
take H4 (⟨ x,z ⟩).
left H5 H6.
left H8 H7.
ex_el H9.
ex_el H9.
both H9.
apply pair_property in H11.
both H11.
repl <- H9 in H12.
repl <- H13 in H12.
ex_el H10.
ex_el H10.
both H10.
apply pair_property in H11.
both H11.
repl <- H10 in H14.
repl <- H15 in H14.
take H1 y z x.
apply H11.
split; ass.
unfold on.
unfold onto in H2.
take inverse_the_inverse_property f f_inv H0 H4.
take domain_range_of_inverse f_inv f H5.
take eq_trans _ _ _ H6 H2.
ass.
unfold onto.
take domain_range_of_inverse f f_inv H4.
unfold on in H3.
apply eq_symm in H3.
take eq_trans _ _ _ H3 H5.
apply eq_symm.
ass.
intros a b c.
intro.
both H5.
take H4 (⟨ a, c ⟩).
left H5 H6.
ex_el H8.
ex_el H8.
both H8.
apply pair_property in H9.
both H9.
repl <- H8 in H10.
repl <- H11 in H10.
take H4 (⟨ b, c ⟩).
left H9 H7.
ex_el H12.
ex_el H12.
both H12.
apply pair_property in H13.
both H13.
repl <- H12 in H14.
repl <- H15 in H14.
right H0.
take H13 c a b.
apply H16.
split.
ass.
ass.
Qed.

Definition composition_of_bijections
(A B C f g: Set)
(H : bijection f A B)
(H1 : bijection g B C):
bijection (g ∘ f) A C .
extract_iota_from_goal (g ∘ f).
rename s into comp.
split.
split.
split.
split.
intro.
intro.
unfold ordered_pair.
take iota_prop x.
left H2 H0.
ex_el H3.
ex_el H3.
both H3.
ex_in x0.
ex_in z.
ass.
intros x y z HH.
both HH.
take iota_prop ( ⟨ x, y ⟩).
left H3 H0.
ex_el H4.
ex_el H4.
both H4.
apply pair_property in H5.
both H5.
repl <- H4 in H6.
repl <- H7 in H6.
ex_el H6.
both H6.
take iota_prop ( ⟨ x, z ⟩). 
left H6 H2.
ex_el H9.
ex_el H9.
both H9.
apply pair_property in H10.
both H10.
repl <- H9 in H11.
repl <- H12 in H11.
ex_el H11.
both H11.
left H.
left H11.
left H14.
right H15.
take H16 x y0 y1.
assert ( (⟨ x, y0 ⟩ ∈ f ∧ ⟨ x, y1 ⟩ ∈ f)).
split. 
ass.
ass.
take H17 H18.
repl H19 in H5.
repl H19 in H8.
left H1.
left H20.
left H21.
right H22.
take H23 y1 y z.
apply H24.
split.
ass.
ass.
apply eq_in.
intro.
intro.
extract_iota ( domain comp) H0.
take iota_prop0 x.
left H2 H0.
ex_el H3.
take iota_prop (⟨ x, y⟩).
left H4 H3.
ex_el H5.
ex_el H5.
both H5.
apply pair_property in H6.
both H6.
ex_el H7.
both H7.
repl H5.
left H.
left H7.
right H10.
apply eq_el_1 in H11.
take H11 x0.
apply H12.
extract_iota_from_goal (domain f).
take iota_prop1 x0.
apply_b H13.
ex_in y0.
ass.
intro.
intro.
extract_iota_from_goal (domain comp).
take iota_prop0 x.
apply_b H2.
left H.
left H2.
right H3.
apply eq_el_2 in H4.
take H4 x H0.
extract_iota (domain f) H5.
take iota_prop1 x.
left H6 H5.
ex_el H7.
left H1.
left H8.
right H9.
apply eq_el_2 in H10.
take H10 y.
right H2.
unfold onto in H12.
assert (y ∈ B).
apply eq_el_1 in H12.
take H12 y.
apply H13.
extract_iota_from_goal ( range f).
take iota_prop2 y.
apply_b H14.
ex_in x.
ass.
take H11 H13.
extract_iota (domain g) H14.
take iota_prop2 y.
left H15 H14.
ex_el H16.
ex_in y0.
take iota_prop (⟨ x, y0 ⟩).
apply_b H17.
ex_in x.
ex_in y0.
split.
apply eq_refl.
ex_in y.
split.
ass.
ass.
apply eq_in.
intro.
intro.
extract_iota (range comp) H0.
take iota_prop0 x.
left H2 H0.
ex_el H3.
take iota_prop (⟨ x0, x ⟩).
left H4 H3.
ex_el H5.
ex_el H5.
both H5.
ex_el H7.
both H7.
apply pair_property in H6.
both H6.
repl H9.
left H1.
right H6.
apply eq_el_1 in H10.
take H10 z.
apply H11.
extract_iota_from_goal (range g).
take iota_prop1 z.
apply_b H12.
ex_in y.
ass.
intro.
intro.
extract_iota_from_goal (range comp).
take iota_prop0 x.
apply_b H2.
left H1.
right H2.
apply eq_el_2 in H3. 
take H3 x H0.
extract_iota (range g) H4.
take iota_prop1 x.
left H5 H4.
ex_el H6.
left H.
right H7.
apply eq_el_2 in H8. 
assert (x0 ∈ B).
left H2.
right H9.
apply eq_el_1 in H10.  
take H10 x0.
apply H11.
extract_iota_from_goal ( domain g).
take iota_prop2 x0.
apply_b H12.
ex_in x.
ass.
take H8 x0 H9.
extract_iota (range f) H10.
take iota_prop2 x0.
left H11 H10.
ex_el H12.
ex_in x1.
take iota_prop (⟨ x1, x ⟩).
apply_b H13.
ex_in x1.
ex_in x.
split.
apply eq_refl.
ex_in x0.
split.
ass.
ass.
intros a b c.
intro.
both H0.
take iota_prop (⟨ a, c ⟩).
left H0 H2.
ex_el H4.
ex_el H4.
both H4.
apply pair_property in H5.
ex_el H6.
both H6.
take iota_prop (⟨ b, c ⟩).
left H6 H3.
ex_el H8.
ex_el H8.
both H8.
apply pair_property in H9.
ex_el H10.
both H10.
both H5.
repl <- H10 in H4.
repl <- H12 in H7.
both H9.
repl <- H5 in H8.
repl <- H13 in H11. 
clear H6 H10 H12 H5 H13.
right H1.
take H5 y y0 c.
assert (⟨ y, c ⟩ ∈ g ∧ ⟨ y0, c ⟩ ∈ g).
split; ass.
take H6 H9.
repl <- H10 in H8.
right H.
take H12 a b y.
apply H13.
split.
ass.
ass.
Qed.


Definition similar_transitive (A B C: Set)
(H: A ~ B) (H1: B ~ C): A ~ C.
unfold similar in H.
unfold similar in H1.
unfold similar.
ex_el H.
ex_el H1.
rename f0 into g.
ex_in (g ∘ f).
apply (composition_of_bijections A B).
ass.
ass.
Qed.


Definition card_eq_classinality_property (U A B: Set)(UP: ∀s. s ⊆ U): 
(card_eq_class U A = card_eq_class U B) ⇔ (A ~ B). 
split.
intro.
unfold card_eq_class in H.
unfold equivalence_class_gen_by in H.
extract_iota (similarity_relation U [{`A}]) H.
extract_iota (similarity_relation U [{`B}]) H.
repl H in iota_prop.
clear H.
extract_iota (similarity_relation U) iota_prop.
extract_iota (similarity_relation U) iota_prop0.
take iota_prop1 (⟨A,B⟩).
assert ( ⟨ A, B ⟩ ∈ s1 -> A ~ B).
intro.
left H H0.
ex_el H1.
both H1.
ex_el H3.
both H3.
both H4.
apply pair_property in H3.
both H3.
repl H4.
repl H6.
ass.
apply H0.
clear H H0.
take iota_prop B.
assert (B ∈ s0 -> ⟨ A, B ⟩ ∈ s1).
intro.
left H H0.
ex_el H1.
both H1.
apply element_of_unit_set in H2.
repl H2 in H3.
ass.
apply H0.
take iota_prop0 B.
apply_b H1.
ex_in B.
split.
apply every_set_is_in_unit_set.
take iota_prop2 (⟨ B, B ⟩).
apply_b H1.
ex_in B.
split.
apply element_in_power_set.
apply (UP B).
ex_in B.
split.
apply element_in_power_set.
apply (UP B).
split.
apply eq_refl.
apply similar_reflective.
intro.
unfold card_eq_class.
unfold equivalence_class_gen_by.
extract_iota_from_goal ((similarity_relation U [{`A}]) ).
extract_iota_from_goal ((similarity_relation U [{`B}]) ).
extract_iota (similarity_relation U) iota_prop.
extract_iota (similarity_relation U) iota_prop0.
apply eq_in.
intro.
intro.
take iota_prop x.
left H1 H0.
ex_el H2.
both H2.
apply element_of_unit_set in H3.
repl H3 in H4.
take iota_prop1  (⟨ A, x ⟩).
left H2 H4.
ex_el H5.
both H5.
ex_el H7.
both H7.
both H8.
apply pair_property in H7.
both H7.
repl <- H8 in H9.
repl <- H10 in H9.
clear H8 H10.
take iota_prop0 x.
apply_b H7.
ex_in B.
split.
apply every_set_is_in_unit_set.
take iota_prop2 (⟨ B, x ⟩).
apply_b H7.
ex_in B.
split.
apply element_in_power_set.
apply (UP B).
ex_in x.
split.
take UP x.
apply element_in_power_set.
ass.
split.
apply eq_refl.
apply similar_symmetric in H.
take similar_transitive _ _ _ H H9.
ass.
intro.
intro.
take iota_prop0 x.
left H1 H0.
ex_el H2.
both H2.
apply element_of_unit_set in H3.
repl H3 in H4.
take iota_prop x.
apply_b H2.
ex_in A.
split.
apply every_set_is_in_unit_set.
take iota_prop2 (⟨ B, x ⟩).
left H2 H4.
ex_el H5.
both H5.
ex_el H7.
both H7.
both H8.
apply pair_property in H7.
both H7.
repl <- H8 in H9.
repl <- H10 in H9.
take iota_prop1 (⟨ A, x ⟩).
apply_b H7.
ex_in A.
split.
apply element_in_power_set.
apply (UP A).
ex_in x.
split.
apply element_in_power_set.
apply (UP x).
split.
apply eq_refl.
take similar_transitive _ _ _ H H9.
apply H7.
Qed.

(* ==== Graph Theory ====*)
(* 
started July 26, 2026 
finished _
*)

Definition gt (a b: Set) := b ∈ a.

Notation "a > b" := (gt a b)(at level 70):direct_relations.

Definition ge (a b: Set) := (a > b) ∨ (a = b).

Notation "a ≥ b" := (ge a b)(at level 70):direct_relations.

Theorem nn_is_ge_zero: forall k : Set, k ∈ N -> k ≥ 0.
intro.
intro.
take zero_is_le_nn.
take H0 k.
take H1 H.
unfold ge.
unfold le in H2.
disj H2.
left.
unfold gt.
unfold lt in H3.
apply H3.
right.
apply eq_symm in H3.
apply H3.
Qed.


(* {0,1,…, m−1} *)
Theorem set_from_0_to_n_minus_1_exists (n: Set) : 
∃1s. (∀e. e∈s ⇔ (e ∈ N ∧ e ≥ 0 ∧ e < n)).
split.
take ZF2_subsets (fun e => e ≥ 0 ∧ e < n) N.
ex_el H.
ex_in b.
intro.
split.
intro.
take H x.
left H1 H0.
conj_el H2.
conj_el H4.
split.
split.
assumption.
assumption.
assumption.
intro.
conj_el H0.
conj_el H1.
take H x.
apply_b H5.
split.
assumption.
split.
assumption.
assumption.
apply any_biimpl_set_is_no_more_than_one.
Qed.

Definition set_from_0_to_n_minus_1(n: Set)
:= ι _ (set_from_0_to_n_minus_1_exists n).

(* finite sequence *)
Definition sequence_len_in(s n A: Set) := 
(function_on_into s (set_from_0_to_n_minus_1 n) A).

Definition sequence_el_ex (s: Set) (n A: Set) (H: sequence_len_in s n A) 
(x: Set) (x_in_X: x ∈ (set_from_0_to_n_minus_1 n)):
 ∃1y. (y ∈ A) ∧ (pair x y ∈ s).
unfold sequence_len_in in H.
take appl_ex_deprecated s (set_from_0_to_n_minus_1 n) A H x x_in_X.
apply H0.
Qed.

Definition sequence_el (s: Set) (n A: Set) (H: sequence_len_in s n A) 
(x: Set) (x_in_X: x ∈ (set_from_0_to_n_minus_1 n)) := 
ι _ (sequence_el_ex s n A H x x_in_X).

Definition path(p k V E u v: Set) :=
∃ p_is_seq: (sequence_len_in p (S k) V). (pair 0 u ∈ p) ∧ (pair k u ∈ p) ∧ ∀i. 
∀ i_in_domain: (i ∈ (set_from_0_to_n_minus_1 (S k))).
∀ si_in_domain: (S i ∈ (set_from_0_to_n_minus_1 (S k))).
pair (sequence_el p (S k) V p_is_seq i i_in_domain) (sequence_el p (S k) V p_is_seq (S i) si_in_domain) ∈ E.


Definition finite(s: Set) := ∃n::N. similar n s. 

Definition zero_is_in_one:  0 ∈ 1.
unfold one .
unfold zero.
unfold S.
extract_iota_from_goal ({`∅}).
apply union_in.
right.
take iota_prop ∅.
right H.
apply H0.
apply eq_refl.
Qed.

Definition every_number_inside_nn_is_nn:
∀n::N. ∀k. k ∈ n -> k ∈ N.
apply PN5_induction.
intro.
intro.
apply any_set_in_empty_set_causes_contradiction in H.
apply H.
intro.
intro.
intro.
intro.
intro.
rename x0 into k.
take H0 k.
unfold S in H1.
apply union_el in H1.
disj H1.
take H2 H3.
assumption.
apply element_of_unit_set in H3.
repl H3.
assumption.
Qed.

Definition domain_of_rc_left (x A B: Set) (HH: one_to_one B):
x ∈ domain (A - B) -> x ∈ (domain A).
intro.
extract_iota_from_goal (domain A).
take iota_prop x.
apply_b H0.
extract_iota (domain (A - B)) H.
take iota_prop0 x.
left H0 H.
ex_el H1.
apply relative_complement_el in H1.
both H1.
ex_in y.
apply H2.
Qed.


Definition set_with_one_pair_is_one_to_one(x y: Set):
one_to_one {`⟨ x, y ⟩ }.
intros a b c.
intro.
both H.
apply element_of_unit_set in H0.
apply element_of_unit_set in H1.
apply pair_property in H0, H1.
both H0.
both H1.
apply eq_symm in H0.
take eq_trans a x b.
apply H1.
assumption.
assumption.
Qed.

Definition derive_middle_disjunct_when_others_fail (A B C: Prop) 
(H: A ∨ B ∨ C) (H2: ¬A) (H3: ¬C): B.
take disj_el_alt_2 (A ∨ B) C.
take H0 H H3.
take disj_el_alt_1 A B.
apply H4.
apply H1.
apply H2.
Qed.

(* bad definition !!!! *)
Definition restriction_deprecated(f X Y A: Set) (H: function_on_into f X Y) (H2: A ⊆ X) :=
f ∩ (A × Y).

Definition restriction(f A: Set) := f ∩ (A × (range f)).

Notation "f ↾ A" := (restriction f A)(at level 71, left associativity).

Definition ex_bridge (S: Set): ∃x. x = S.
ex_in S.
apply eq_refl.
Qed.

Definition bijection_is_into(f A B: Set) :
(bijection f A B) -> into f B.
intro.
both H.
both H0.
both H.
unfold into.
unfold onto in H2.
repl H2.
apply subset_refl.
Qed.

Definition every_element_of_cartesian_is_ordered_pair (x A B: Set):
x ∈ A × B -> ordered_pair x.
intro.
extract_iota (A × B) H.
take iota_prop x.
left H0 H.
ex_el H1.
both H1.
ex_el H3.
both H3.
ex_in x0.
ex_in y.
apply H4.
Qed.

Definition domain_el (f x: Set): x ∈ domain f -> ∃ y . ⟨ x, y ⟩ ∈ f.
intro.
extract_iota (domain f) H.
take iota_prop x.
left H0 H.
apply H1.
Qed.

Definition domain_in_old (f x: Set): (∃ y . ⟨ x, y ⟩ ∈ f) -> x ∈ domain f.
intro.
ex_el H.
extract_iota_from_goal (domain f).
take iota_prop x.
apply_b H0.
ex_in y.
apply H.
Qed.

Definition domain_in (f x y: Set): ⟨ x, y ⟩ ∈ f -> x ∈ domain f.
intro.
extract_iota_from_goal (domain f).
take iota_prop x.
apply_b H0.
ex_in y.
apply H.
Qed.

Definition range_in_old (f y: Set): (∃ x . ⟨ x, y ⟩ ∈ f) -> y ∈ range f.
intro.
ex_el H.
extract_iota_from_goal (range f).
take iota_prop y.
apply_b H0.
ex_in x.
apply H.
Qed.

Definition range_in (f y x: Set): ⟨ x, y ⟩ ∈ f -> y ∈ range f.
intro.
extract_iota_from_goal (range f).
take iota_prop y.
apply_b H0.
ex_in x.
apply H.
Qed.

Definition range_el (f y: Set): y ∈ range f -> (∃ x . ⟨ x, y ⟩ ∈ f).
intro.
extract_iota (range f) H.
take iota_prop y.
left H0 H.
apply H1.
Qed.

Definition cartesian_product_in (a b A B: Set): a ∈ A -> b ∈ B -> 
⟨a,b⟩ ∈ A × B.
intros.
extract_iota_from_goal (A × B).
take iota_prop (⟨ a, b ⟩).
apply_b H1.
ex_in a.
split.
apply H.
ex_in b.
split.
apply H0.
apply eq_refl.
Qed.

Definition cartesian_product_in_2 (p A B: Set):  
(∃a. ∃b. p = ⟨a, b⟩ ∧ a ∈ A ∧ b ∈ B) -> (p ∈ A × B).
intros.
extract_iota_from_goal (A × B).
take iota_prop p.
apply_b H0.
ex_el H.
ex_el H.
both H.
both H0.
ex_in a.
split. ass.
ex_in b.
split. ass.
ass.
Qed.


Definition cartesian_product_el (a b A B: Set):  
(⟨a,b⟩ ∈ A × B) -> a ∈ A ∧ b ∈ B.
intro.
extract_iota (A × B) H.
take iota_prop ⟨ a, b ⟩.
left H0 H.
ex_el H1.
both H1.
ex_el H3.
both H3.
apply pair_property in H4.
both H4.
repl H3.
repl H5.
split; assumption.
Qed.

Definition cartesian_product_el_2 (p A B: Set):  
(p ∈ A × B) -> ∃a. ∃b. p = ⟨a, b⟩ ∧ a ∈ A ∧ b ∈ B.
intro.
extract_iota (A × B) H.
take iota_prop p.
left H0 H.
ex_el H1.
both H1.
ex_el H3.
both H3.
ex_in x.
ex_in y.
split.
split; ass.
ass.
Qed.

Ltac a := assumption.

Ltac one_to_one_in :=
let x := fresh "x" in
let y := fresh "y" in
let z := fresh "z" in
let temp := fresh "temp" in
intro x;
intro y;
intro z;
intro temp;
both temp.

Definition pair_unord_el(x A B: Set): x ∈ {A, B} -> x = A ∨ x = B.
intro.
extract_iota ({A, B}) H.
take iota_prop x.
left H0 H.
apply H1.
Qed.

Definition f_on_into_appl_ex (f: Set) (X Y: Set) (x: Set) (x_in_X: x ∈ X) (H: function_on_into f X Y) 
:
∃1y. (y ∈ Y) ∧ (⟨x,y⟩ ∈ f).
both H.
both H0.
both H.
split.
unfold on in H2.
extract_iota (domain f) H2.
repl H2 in iota_prop.
take iota_prop x.
left H x_in_X.
ex_el H4.
ex_in y.
split.
unfold into in H1.
take H1 y.
apply H5.
apply range_in_old.
ex_in x.
a.
a.
intros a b.
intros HH HHH.
both HH.
both HHH.
take H3 x a b.
apply H7.
split; ass.
Qed.

Ltac grab_x_in_domain_proof f x :=
  lazymatch goal with
  | H : (function_on_into f ?A ?B) |- _ => 
      lazymatch goal with
      | H2 : (x ∈ A) |- _ => exact H2

      | _ => fail "Unable to grab inner"
      end
  | _ => fail "Unable to grab outer"
  end.

Ltac subset x P :=
let H := fresh "H" in
pose proof ZF2_subsets P x as H;
cbv beta in H;
ex_el H.

Definition pair_unord_in1(y x: Set): x ∈ {x, y}.
extract_iota_from_goal ({x, y}).
take iota_prop x.
apply_b H.
left.
apply eq_refl.
Qed.

Definition pair_unord_in2(x y: Set): y ∈ {x, y}.
extract_iota_from_goal ({x, y}).
take iota_prop y.
apply_b H.
right.
apply eq_refl.
Qed.

Definition relational_image_ex(f x: Set) : 
∃1s. ∀y. y ∈ s ⇔ ⟨x,y⟩ ∈ f.
take union_exists f.
ex_el H.
take union_exists u.
ex_el H0.
subset u0 (fun y => ⟨x,y⟩ ∈ f).
split.
ex_in b.
intro.
split.
intro.
take H1 x0.
left H3 H2.
both H4.
ass.
intro.
take H1 x0.
apply_b H3.
split.
take H0 x0.
apply_b H3.
ex_in {x, x0}.
split.
apply pair_unord_in2.
take H ({x, x0}).
apply_b H3.
ex_in ⟨ x, x0 ⟩.
split.
apply pair_unord_in2.
ass.
ass.
apply any_biimpl_set_is_no_more_than_one.
Qed.


Definition relational_image(f x: Set):= ι _ (relational_image_ex f x).

Definition relational_image_el(f x y: Set): y ∈ relational_image f x -> ⟨x,y⟩ ∈ f.
intro.
extract_iota (relational_image f x) H.
take iota_prop y.
left H0 H.
ass.
Qed.

Definition relational_image_in(f x y: Set): ⟨x,y⟩ ∈ f -> y ∈ relational_image f x.
intro.
extract_iota_from_goal (relational_image f x).
take iota_prop y.
apply_b H0.
ass.
Qed.



(* Metamath trick to avoid dependency on proof objects which is a source of troubles *)
Definition appl(f x: Set) := ⋃(relational_image f x).

Notation "f ⦅ x ⦆" := (appl f x)
(at level 20, x at level 200, left associativity, format "f ⦅ x ⦆"). 

Notation "f ⦅ x , y ⦆" := (appl f ⟨x,y⟩)
(at level 20, x at level 200, y at level 200, left associativity, format "f ⦅ x , y ⦆"). 

Definition identity_relation_el(p X: Set) (H: p ∈ identity_relation X): ∃x:: X. p = ⟨x, x⟩.
extract_iota (identity_relation X) H.
unfold identity_relation_prop in iota_prop.
take iota_prop p.
left H0 H.
apply H1.
Qed.

Definition id_el(p X: Set):= identity_relation_el p X.

Definition identity_relation_in(p X: Set): (∃x:: X. p = ⟨x, x⟩) -> (p ∈ identity_relation X).
intro.
extract_iota_from_goal (identity_relation X).
unfold identity_relation_prop in iota_prop.
take iota_prop p.
apply_b H0.
ass.
Qed.

Definition id_in(p X: Set):= identity_relation_in p X.


Definition composition_el(g f x z: Set): ⟨x, z⟩ ∈ g ∘ f ->
∃y. ⟨x,y⟩ ∈ f ∧ ⟨y,z⟩ ∈ g. 
intro.
extract_iota (g ∘ f) H.
take iota_prop (⟨ x, z ⟩ ).
left H0 H.
ex_el H1.
ex_el H1.
both H1.
apply pair_property in H2.
both H2.
ex_el H3.
both H3.
repl H1.
repl H4.
ex_in y.
split.
a.
a.
Qed.

Definition composition_in(g f x z: Set):
(∃y. ⟨x,y⟩ ∈ f ∧ ⟨y,z⟩ ∈ g) -> ⟨x, z⟩ ∈ g ∘ f.
intro.
extract_iota_from_goal (g ∘ f).
take iota_prop (⟨ x, z ⟩).
apply_b H0.
ex_in x.
ex_in z.
split.
apply eq_refl.
apply H.
Qed.

Definition if_function_is_own_inverse_then_bijection (A f: Set) (H: function_on_into f A A):
(composition f f = identity_relation A) -> bijection f A A.
intro.
split.
split.
pick H.
split.
a.
a.
unfold onto.
apply eq_in.
intro.
intro.
apply range_el in H1.
ex_el H1.
pick H.
unfold into in into0.
take into0 x.
apply H2.
apply range_in_old.
ex_in x0.
a.
intro y.
intro.
apply range_in_old.
pick H.
unfold on in on0.
take H1.
repl <- on0 in H2.
apply domain_el in H2.
ex_el H2.
rename y0 into x.
ex_in x.
assert (⟨y,y⟩ ∈ identity_relation A).
apply identity_relation_in.
ex_in y.
split.
ass.
apply eq_refl.
repl <- H0 in H3.
apply composition_el in H3.
ex_el H3.
both H3.
right function0.
take H3 y x y0.
assert ((⟨ y, x ⟩ ∈ f ∧ ⟨ y, y0 ⟩ ∈ f)).
split.
ass.
ass.
take H6 H7.
repl H8.
ass.
intro.
intro.
intro.
intro.
both H1.
rename x into a.
rename x0 into b.
rename x1 into f_a.
assert (⟨a,a⟩ ∈ identity_relation A).
apply identity_relation_in.
ex_in a.
split.
pick H.
unfold on in on0.
repl <- on0.
apply domain_in_old.
ex_in f_a.
a.
apply eq_refl.
repl <- H0 in H1.
apply composition_el in H1.
ex_el H1.
both H1.
pick H.
right function0.
take H1 a f_a y.
assert (⟨ a, f_a ⟩ ∈ f ∧ ⟨ a, y ⟩ ∈ f).
split.
ass.
ass.
take H6 H7.
repl <- H8 in H5.
repl <- H8 in H4.
assert (⟨ b, a ⟩ ∈ (f ∘ f)).
apply composition_in.
ex_in f_a.
split; ass.
repl H0 in H9.
apply identity_relation_el in H9.
ex_el H9.
both H9.
apply pair_property in H11.
both H11.
repl H9.
repl H12.
apply eq_refl.
Qed.

Ltac split_rev := apply conj_symm;split.


Definition restricting_bijection_gives_injection (f A B A': Set):
(bijection f A B) -> (A' ⊆ A) 
-> ∃g. function_on_into g A' B ∧ one_to_one g.
intro.
intro.
assert (function_on_into f A B).
pose proof H as HH.
both H.
both H1.
both H.
split.
split.
assumption.
assumption.
take bijection_is_into f A B HH.
apply H.
take ex_bridge (restriction_deprecated f A B A' H1 H0).
ex_el H2.
unfold restriction_deprecated in H2.
ex_in x.
rename x into g.
split.
split.
split.
split.
intro.
intro.
unfold ordered_pair.
repl H2 in H3.
apply intersection_el in H3.
both H3.
take every_element_of_cartesian_is_ordered_pair x A' B H5.
apply H3.
intros x y z.
intro.
both H3.
repl H2 in H4.
repl H2 in H5.
apply intersection_el in H4, H5.
both H4.
both H5.
left H.
left H5.
left H8.
right H9.
take H10 x y z.
apply H11.
split; assumption.
unfold on.
apply eq_in.
intro.
intro.
apply domain_el in H3.
ex_el H3.
repl H2 in H3.
apply intersection_el in H3.
both H3.
extract_iota (A' × B) H5.
take iota_prop (⟨ x, y ⟩).
left H3 H5.
ex_el H6.
both H6.
ex_el H8.
both H8.
apply pair_property in H9.
both H9.
repl H8.
apply H7.
intro.
intro.
apply domain_in_old.
take H0 x H3.
take function_application f A B H1 x H4.
ex_el H5.
ex_in b.
repl H2.
apply intersection_in_alt.
split.
apply H5.
right H1.
unfold into in H6.
assert (b ∈ B).
take H6 b.
apply H7.
apply range_in_old.
ex_in x.
assumption.
apply cartesian_product_in.
apply H3.
a.
intro.
intro.
apply range_el in H3.
ex_el H3.
repl H2 in H3.
apply intersection_el in H3.
both H3.
apply cartesian_product_el in H5.
both H5.
a.
one_to_one_in.
repl H2 in H3.
repl H2 in H4.
apply intersection_el in H3, H4.
both H3.
both H4.
right H.
take H4 x y z.
apply H8.
split.
a.
a.
Qed.

Definition subset_of_cartesian_short_exists (A B: Set)(P: Set -> Set -> Prop): 
∃1 c. c ⊆ A × B ∧ ∀x::A. ∀y::B. ⟨x, y⟩ ∈ c ⇔ P x y.
split_rev.
intros a b.
intros H HH.
both H.
both HH.
apply eq_in.
intro x.
intro.
take (H0 x) H3.
apply cartesian_product_el_2 in H4.
ex_el H4.
ex_el H4.
both H4.
both H5.
take H1 a0 H7 b0 H6.
take H2 a0 H7 b0 H6.
apply biimpl_symm in H8.
take biimpl_trans _ _ _ H5 H8.
repl H4.
left H9.
apply H10.
repl H4 in H3.
ass.
intro x.
intro.
take H x H3.
apply cartesian_product_el_2 in H4.
ex_el H4.
ex_el H4.
both H4.
both H5.
take H1 a0 H7 b0 H6.
take H2 a0 H7 b0 H6.
apply biimpl_symm in H8.
take biimpl_trans _ _ _ H5 H8.
repl H4.
right H9.
apply H10.
repl H4 in H3.
ass.
take ZF2_subsets (fun p => ∃a::A. ∃b::B. p = ⟨a,b⟩ 
∧ P a b) (A × B).
ex_el H.
ex_in b.
split.
intro k.
take H k.
intro.
left H0 H1.
both H2.
ass.
intro.
intro.
intro.
intro.
take H ⟨ x, x0 ⟩.
split.
intro.
left H2 H3.
both H4.
ex_el H6.
both H6.
ex_el H7.
both H7.
both H8.
apply pair_property in H7.
both H7.
repl H8.
repl H10.
ass.
intro.
apply_b H2.
split.
apply cartesian_product_in.
ass.
ass.
ex_in x.
split.
ass.
ex_in x0.
split.
ass.
split.
apply eq_refl.
ass.
Qed.

Definition bijection_with_exchanged_elements_exists(A a k: Set): ∃f. 
∃(f_is_func: function_on_into f A A). 
(∀x. ∀x_in_A: (x ∈ A). ((x = a) ∧ 
(f⦅x⦆ = k) ∨ ((x = k) ∧ (f⦅x⦆ = a)) ∨ ((x ≠ a ∧ x ≠ k) ∧ (f⦅x⦆ = x)))).
Abort.

Definition there_is_no_one_to_one_function_from_n_back: 
∀k::N. ¬∃f. function_on_into f (S k) k ∧  (one_to_one f).
apply PN5_induction.
intro.
ex_el H.
left H.
left H0.
right H0.
both H1.
unfold on in H4.
take function_application f (S 0) 0 H0.
take H1 0.
take zero_is_in_one.
take H5 H6.
ex_el H7.
unfold into in H2.
take element_of_function_in_range f (S 0) 0 0 b H0 H7.
take empty_set_el b.
apply H9.
assumption.
intro.
intros.
intro.
ex_el H1.
rename f into h.
both H1.
rename x into k.
take function_application _ _ _ H2 (S k).
assert (∀ x. x ∈ (S x)).
intro.
unfold S.
apply union_in_2.
apply every_set_is_in_unit_set.
take H4 (S k).
take H1 H5.
ex_el H6.
rename b into a.
right H2.
unfold into in H7.
take element_of_function_in_range _ _ _ (S k) a H2.
take H8 H6.
take PN2_succ k.
change (a ∈ S k) with (a < S k) in H9.
take elimitane_S_and_lt a.
take PN2_succ k H.
take every_number_inside_nn_is_nn (S k) H12 a H9.
take H11 H13.
take H14 k H H9.
unfold le in H15.
(* a < k ∨ a = k 
  Shall be clean and correst up until now
*)
disj H15.

take subset_of_cartesian_short_exists (S k) (S k) 
(fun x => fun y => 
((x = a) ∧ (y = k)) ∨ ((x = k) ∧ (y = a)) ∨
((x ≠ a ∧ x ≠ k) ∧ y = x)).
ex_el H15.
rename c into sigma.
both H15.
assert (bijection sigma (S k) (S k)).

(* 
ex_in a b c. !!!

super long but possible 
shall be OKAY
https://chatgpt.com/c/6a69cbaa-2ffc-83ea-8ed9-2dcd0c5dce63

 construction is too long, can resume later...
proceed with building step by step the requred set
https://chatgpt.com/c/6a65a87d-9454-83ea-86e1-14961d7df121
alternative: https://chatgpt.com/c/6a674c05-b640-83ea-9726-f8edaf797339
*)
Admitted.



Definition two_similar_nn_are_equal(a b: Set) 
(a_in_N: a ∈ N) (b_in_N: b ∈ N) (H: a ~ b): a = b.
take trichotomy_for_set_inclusion_only_disj a a_in_N b b_in_N.
take derive_middle_disjunct_when_others_fail (a ∈ b) (a = b) (b ∈ a).
rename a into m.
rename b into n.
take H1 H0.
assert (n ∉ m -> m ∉ n -> m = n).
intros.
take H2 H4 H3.
apply H5.
apply H3.
clear H0 H1 H2.
intro.
assert (((S n) ⊆ m)).
unfold S.
intro.
intro.
apply union_el in H1.
disj H1.
take every_natual_number_is_transitive m a_in_N.
unfold transitive_set in H1.
take H1 x n.
apply H4.
split.
assumption.
assumption.
take element_of_unit_set x n H2.
repl H1.
assumption.
unfold similar in H.
ex_el H.
take restricting_bijection_gives_injection f m n (S n) H H1.
take there_is_no_one_to_one_function_from_n_back n b_in_N.
apply H4.
a.
intro.
assert (((S m) ⊆ n)).
unfold S.
intro.
intro.
apply union_el in H5.
disj H5.
take every_natual_number_is_transitive n b_in_N.
unfold transitive_set in H5.
take H5 x m.
apply H7.
split.
a. a.
take element_of_unit_set x m H6.
repl H5.
a.
apply similar_symmetric in H.
unfold similar in H.
ex_el H.
take restricting_bijection_gives_injection f n m (S m) H H5.
take there_is_no_one_to_one_function_from_n_back m a_in_N.
apply H7.
a.
Qed.

Definition card_ex(s: Set)(H: finite s) : ∃1n. n∈N ∧ similar n s.
split.
unfold finite in H.
ex_el H.
right H.
ex_in n.
assumption.
intros a b.
intros H1 H2.
both H1.
both H2.
apply similar_symmetric in H4.
take similar_transitive a s b.
unfold finite in H.
take H2 H3.
take H5 H4.
ex_el H.
both H.
apply two_similar_nn_are_equal.
assumption.
assumption.
assumption.
Qed.



Definition card(s: Set)(H: finite s):= ι _ (card_ex s H).

Notation "| A |" := (card A (ltac:(assumption)))(at level 0, A at level 9, only parsing).
Notation "| A |" := (card A _)(at level 0, A at level 9, only printing).

Definition S_el(A B: Set): A ∈ S B -> A ∈ B ∨ A = B.
intro.
unfold S in H.
apply union_el in H.
disj H.
left.
ass.
apply unit_set_el in H0.
right.
ass.
Qed.

Definition S_in(A B: Set): (A ∈ B ∨ A = B) -> A ∈ S B.
intro.
unfold S.
apply union_in.
disj H.
left.
ass.
right.
apply unit_set_in.
ass.
Qed.

Definition n_properties: is_successor_set N
∧ (∀ z . is_successor_set z -> N ⊆ z).
split.
extract_iota_from_goal N.
both iota_prop.
ass.
extract_iota_from_goal N.
both iota_prop.
ass.
Qed.

(* Active development: August 14, 2026 - August 28, 2026 (15 days) *)
Definition compatible_deprecated(f g: Set) := ∀x::((domain f) ∩ (domain g)). ∃y. ⟨x,y⟩ ∈ f ∧ ⟨x,y⟩ ∈ g.

Definition set_of_functions(s: Set) := ∀f::s. function f.

Definition big_union_el (a b: Set): (a ∈ (⋃ b)) -> ∃s. a ∈ s ∧ s ∈ b.
intro.
extract_iota ((⋃ b)) H.
take iota_prop a.
left H0 H.
apply H1.
Qed.

Definition big_union_in (a b: Set): (∃s. a ∈ s ∧ s ∈ b) -> (a ∈ (⋃ b)).
intro.
extract_iota_from_goal ((⋃ b)).
take iota_prop a.
apply_b H0.
ass.
Qed.


Ltac introsx :=
lazymatch goal with
| |- ∀ xxx . _ => 
(intro xxx; introsx)
| |- _ -> _ => 
(intro; introsx)
| _ => idtac
end.

Ltac intros_agressive := intro; introsx.

Tactic Notation "intros" := intros_agressive. 

Ltac big_union_el H :=
match type of H with
| ?e ∈ (⋃ ?s) => 
  apply big_union_el in H; 
  ex_el H;
  both H
end.

Definition union_of_compatible_functions_is_a_function_deprecated (s: Set) 
(s_set_of_functions: set_of_functions s) (pairwise_compatible: (∀f::s. ∀g::s. compatible_deprecated f g)): 
((function (⋃ s))).
split.
intro.
intro.
apply big_union_el in H.
unfold ordered_pair.
ex_el H.
both H.
take s_set_of_functions s0.
take H H1.
left H2.
take H3 x H0.
ass.
intros.
both H.
big_union_el H0.
big_union_el H1.
take s_set_of_functions s0 H2.
take s_set_of_functions s1 H3.
take pairwise_compatible s0 H2 s1 H3.
unfold compatible_deprecated in H5.
take H.
take element_of_function_in_domain s0 .
apply domain_in in H6.
take H0.
apply domain_in in H8.
take intersection_in _ _ x H6 H8.
take H5 x H9.
ex_el H10.
both H10.
right H1.
take H10 x y y0.
assert (y = y0).
apply H13.
split; ass.
repl <- H14 in H12.
take H0.
take H12.
right H4.
take H17 x y z.
apply H18.
split; ass.
Qed.



Close Scope direct_relations.


(* 
MATH 320 - Set Theory - Lecture 3.3 - 100 %
https://www.youtube.com/watch?v=PbYMvjI9oMA&list=PLuiPz6iU5SQ_3Gubdqa1JHBvM0GBFcIV0&index=9
*)

Definition relation_on (p X: Set) := relation_from_x_to_y p X X.

Definition reflexive(E X: Set) := ∀x::X. ⟨x,x⟩ ∈ E.
Definition anti_symmetric(E X: Set) := ∀x::X. ∀y::X. ⟨x,y⟩ ∈ E -> ⟨y,x⟩ ∈ E -> x = y.
Definition asymmetric(E X: Set) := ∀x::X. ∀y::X. ⟨x,y⟩ ∈ E -> ⟨y,x⟩ ∉ E.
Definition transitive(E X: Set) := ∀x::X. ∀y::X. ∀z::X. ⟨x,y⟩ ∈ E -> ⟨y,z⟩ ∈ E -> ⟨x,z⟩ ∈ E.

Definition partial_order_relation (E X: Set) := 
(relation_on E X) ∧ (reflexive E X) ∧ (anti_symmetric E X) ∧ (transitive E X).

Definition strict_partial_order_relation (E X: Set) := 
(relation_on E X) ∧ (asymmetric E X) ∧ (transitive E X).

Notation "⦅ X , E ⦆ 'is' 'a' 'partially' 'ordered' 'set'" := (partial_order_relation E X)(at level 70).

Notation "⦅ X , E ⦆ 'is' 'a' 'strictly' 'partially' 'ordered' 'set'" := (strict_partial_order_relation E X)(at level 70).

Definition induced_order_prop(E F X: Set) := ∀x::X. ∀y::X. ⟨x,y⟩ ∈ E ⇔ (⟨x,y⟩ ∈ F ∨ x = y).

Definition strict_partial_order_to_ordinary (X F E: Set) (H: strict_partial_order_relation F X)
(H2: relation_on E X) (H3: induced_order_prop E F X): partial_order_relation E X.
unfold partial_order_relation.
split.
split.
split.
ass.
both H.
both H0.
intro.
intro.
take H3 x H0 x H0.
apply_b H5.
right.
apply eq_refl.
intro.
intros.
both H.
both H6.
unfold asymmetric in H8.
take H3 x H0 y H1.
take H3 y H1 x H0.
left H6 H4.
left H9 H5.
clear H6 H9.
disj H10.
disj H11.
take H8 x H0 y H1 H6.
take H10 H9.
apply H11.
apply eq_symm.
apply H9.
disj H11.
apply H6.
apply H6.
both H.
unfold transitive.
intros.
take H3 x H y H4.
left H8 H6.
disj H9.
take H3 y H4 z H5.
left H9 H7.
disj H11.
take H1 x H y H4 z H5 H10 H12.
take H3 x H z H5.
apply_b H13.
left.
apply H11.
repl <- H12.
apply H6.
repl H10.
apply H7.
Qed.

Definition induced_strict_order_prop(E F X: Set) := ∀x::X. ∀y::X. ⟨x,y⟩ ∈ E ⇔ (⟨x,y⟩ ∈ F ∧ x ≠ y).

Definition partial_order_to_strict (X F E: Set) (H: partial_order_relation F X)
(H2: relation_on E X) (H3: induced_strict_order_prop E F X): strict_partial_order_relation E X.
unfold strict_partial_order_relation.
split.
split.
apply H2.
unfold asymmetric.
intros.
take H3 x H0 y H1.
left H5 H4.
both H6.
intro.
take H3 y H1 x H0.
left H9 H6.
both H10.
both H.
both H10.
unfold anti_symmetric in H14.
take H14 x H0 y H1 H7 H11.
apply H8.
ass.
unfold transitive.
intros.
both H.
take H3 x H0 y H1.
left H H5.
both H9.
take H3 y H1 z H4.
left H9 H6.
both H12.
take H8 x H0 y H1 z H4 H10 H13.
take H3 x H0 z H4.
apply_b H15.
split.
ass.
intro.
repl <- H15 in H13.
take H10.
take H13.
right H7.
take H18 x H0 y H1 H16 H17.
left H H5.
right H20.
apply H21.
ass.
Qed.

Ltac cartesian_product_el_2 H := 
let P1 := fresh "H" in
let P2 := fresh "H" in
apply cartesian_product_el_2 in H;
ex_el H; ex_el H;
pose proof H as P1;
pose proof H as P2;
apply conj_el_1 in H;
apply conj_el_1 in H;
apply conj_el_1 in P1;
apply conj_el_2 in P1;
apply conj_el_2 in P2.

Definition induced_partial_order_exists (X F: Set) (H: strict_partial_order_relation F X): 
∃1E. relation_on E X ∧ induced_order_prop E F X ∧ partial_order_relation E X.
unfold strict_partial_order_relation in H.
split.
take union2_exists F (id X).
ex_el H0.
rename u into E.
assert (relation_on E X).
unfold relation_on.
unfold relation_from_x_to_y.
split.
intros.
take H0 x.
left H2 H1.
disj H3.
left H.
left H3.
right H5.
left H5.
unfold relation in H7.
take H7 x H4.
apply H8.
apply id_el in H4.
ex_el H4.
both H4.
ex_in x0.
ex_in x0.
ass.
intro.
intro.
take H0 x.
left H2 H1.
disj H3.
left H.
left H3.
right H5.
take H6 x H4.
ass.
apply id_el in H4.
ex_el H4.
both H4.
repl H5.
apply cartesian_product_in.
ass.
ass.
assert (induced_order_prop E F X).
unfold induced_order_prop.
intro.
intro.
rename H2 into HH2.
intro.
intro.
rename H2 into HHH2.
split.
rename x0 into y.
take H0 ⟨ x, y ⟩.
intro.
left H2 H3.
disj H4.
left.
ass.
right.
apply id_el in H5.
ex_el H5.
both H5.
apply pair_property in H6.
both H6.
repl H5.
repl H7.
apply eq_refl.
intro.
disj H2.
rename x0 into y.
take H0 ⟨ x, y ⟩.
apply_b H2.
left.
ass.
repl H3.
rename x0 into y.
take H0 ⟨ y, y ⟩.
apply_b H2.
right.
apply id_in.
ex_in x.
split. ass.
repl H3.
apply eq_refl.
ex_in E.
take strict_partial_order_to_ordinary X F E H H1 H2.
split.
split.
ass.
ass.
ass.
intros a b c d.
both c.
both d.
both H0.
both H2.
both H.
both H2.
unfold relation_on in H4, H0.
unfold relation_from_x_to_y  in H4, H0.
right H4.
right H0.
unfold induced_order_prop in H5, H6.
apply eq_in.
intro p.
intro.
take H2 p H10.
cartesian_product_el_2 H11.
repl H11.
take H6 a0 H12 b0 H13.
apply_b H14.
take H5 a0 H12 b0 H13.
left H14.
apply H15.
repl <- H11.
ass.
intro p.
intro.
take H9 p H10.
cartesian_product_el_2 H11.
repl H11.
take H5 a0 H12 b0 H13.
apply_b H14.
take H6 a0 H12 b0 H13.
left H14.
apply H15.
repl <- H11.
ass.
Qed.

Definition induced_partial_order (X F: Set) (H: strict_partial_order_relation F X):=
ι _ (induced_partial_order_exists X F H).

Definition comparable(a b E: Set) := ⟨a,b⟩ ∈ E ∨ ⟨b,a⟩ ∈ E.
Definition incomporable(a b E: Set) := ¬ (comparable a b E).

Definition strictly_comparable(a b E: Set) := ⟨a,b⟩ ∈ E ∨ ⟨b,a⟩ ∈ E ∨ a = b.

Definition linear_order_relation(E X: Set) :=
(partial_order_relation E X) ∧ ∀a::X. ∀b::X. comparable a b E.

Definition strict_linear_order_relation(E X: Set) :=
(strict_partial_order_relation E X) ∧ ∀a::X. ∀b::X. strictly_comparable a b E.

Definition membership_exists (X Y: Set): ∃1s. ∀p. p ∈ s ⇔ ∃x::X. ∃y::Y. p = ⟨x,y⟩ ∧ x ∈ y.
split.
take cartesian_product_exists X Y.
ex_el H.
take ZF2_subsets (fun p => ∃x::X. ∃y::Y. p = ⟨x,y⟩ ∧ x ∈ y) c.
ex_el H0.
ex_in b.
intro.
split.
intro.
take H0 x.
left H2 H1.
right H3.
apply H4.
intro.
take H0 x.
apply_b H2.
split.
ex_el H1.
both H1.
ex_el H3.
both H3.
both H4.
take H x.
apply_b H4.
ex_in x0.
split.
ass.
ex_in y.
split;ass.
ass.
apply any_biimpl_set_is_no_more_than_one.
Qed.

Definition membership(X Y: Set) := ι _ (membership_exists X Y).

(* to get Set->Set->Prop representation *)
Definition membership_appl (X Y x y: Set) := ⟨x,y⟩ ∈ (membership X Y).

Definition lt_n_set := membership N N.

Notation "<" := (lt_n_set)(at level 70).

Definition lt_n(x y: Set) := ⟨x,y⟩ ∈ <.

Declare Scope natural_numbers.
Open Scope natural_numbers.

Notation "a < b" := (lt_n a b)(at level 70):natural_numbers.

Definition le_n (a b: Set) := (a < b) ∨ (a = b).

Notation "a ≤ b" := (le_n a b)(at level 70):natural_numbers.

Definition lt_n_in (x y: Set) (H1: x ∈ N) (H2: y ∈ N): x ∈ y -> x < y.
intro.
unfold lt_n.
unfold lt_n_set.
extract_iota_from_goal (membership N N).
take (iota_prop (⟨ x, y ⟩)).
apply_b H0.
ex_in x.
split.
ass.
ex_in y.
split.
ass.
split.
apply eq_refl.
ass.
Qed.

Definition lt_n_el (x y: Set) (H1: x ∈ N) (H2: y ∈ N): x < y -> x ∈ y. 
intro.
unfold lt_n in H.
unfold lt_n_set in H.
extract_iota (membership N N) H.
take iota_prop ⟨ x, y ⟩.
left H0 H.
ex_el H3.
both H3.
ex_el H5.
both H5.
both H6.
apply pair_property in H5.
both H5.
repl H6.
repl H8.
ass.
Qed.

Definition lt_n_el_alt (x: Set) : x ∈ < -> ∃ m::N . ∃ n :: N. x = ⟨ m, n ⟩. 
intro.
unfold lt_n_set in H.
extract_iota (membership N N) H.
take iota_prop x.
left H0 H.
ex_el H1.
both H1.
ex_el H3.
both H3.
both H4.
ex_in x0.
split.
ass.
ex_in y.
split.
ass.
ass.
Qed.

Definition le_n_refl(n: Set) (H: n ∈ N): n ≤ n.
unfold le_n.
right.
apply eq_refl.
Qed.


Definition zero_le_nn(n: Set): n ∈ N -> 0 ≤ n.
intro.
take nn_is_ge_zero n H.
unfold ge in H0.
unfold gt in H0.
disj H0.
unfold le_n.
left.
apply lt_n_in.
apply PN1_empty_set.
ass.
ass.
repl H1.
apply le_n_refl.
apply PN1_empty_set.
Qed.

Definition power_set_in (X k: Set) (H: k ⊆ X): k ∈ power_set X.
extract_iota_from_goal (power_set X).
take iota_prop k.
apply_b H0.
ass.
Qed.

Definition power_set_el (X k: Set): k ∈ power_set X -> k ⊆ X.
intro.
extract_iota (power_set X) H.
take iota_prop k.
left H0.
apply H1.
ass.
Qed.


Definition exercise18 (X E: Set) (H: ∃a::X. ∃b::X. a ≠ b) 
(H2: relation_on E (power_set X)) (H3: ∀x::(power_set X). ∀y::(power_set X). (⟨x,y⟩ ∈ E ⇔ x ⊆ y)):
(partial_order_relation E (power_set X)) ∧ (¬ (linear_order_relation E (power_set X))).
split.
unfold partial_order_relation.
split.
split.
split.
ass.
unfold reflexive.
intros.
take H3 x H0 x H0.
apply_b H1.
apply subset_refl.
unfold anti_symmetric.
intros.
take H3 x H0 y H1.
left H6 H4.
take H3 y H1 x H0 .
left H8 H5.
apply eq_in.
ass.
ass.
intros.
take H3 x H0 y H1.
left H7 H5.
take H3 y H1 z H4.
left H9 H6.
take H3 x H0 z H4.
apply_b H11.
take subset_trans x y z.
apply H11.
ass.
ass.
intro.
unfold linear_order_relation in H0.
right H0.
ex_el H.
both H.
ex_el H5.
both H5.
unfold comparable in H1.
take unit_set_exists a.
take unit_set_exists b.
ex_el H5.
ex_el H7.
assert (p ∈ power_set X).
apply power_set_in.
intro.
intro.
take H5 x.
left H9 H8.
repl H10.
ass.
assert (p0 ∈ power_set X).
apply power_set_in.
intro.
intro.
take H7 x.
left H10 H9.
repl H11.
ass.
take H1 p H8 p0 H9.
disj H10.
take H3 p H8 p0 H9.
left H10 H11.
take H5 a.
assert (a ∈ p).
apply_b H13.
apply eq_refl.
take H12 a H14.
take H7 a.
left H16 H15.
apply H6.
ass.
take H3 p0 H9 p H8 .
left H10 H11.
take H12 b.
apply H6.
take H7 b.
take H5 b.
left H15.
apply eq_symm.
apply H16.
apply H13.
right H14.
apply H17.
apply eq_refl.
Qed.


(* 
MATH 320 - Set Theory - Lecture 4.1 - 100 %
https://www.youtube.com/watch?v=9PK8BFQy6Lc&list=PLuiPz6iU5SQ_3Gubdqa1JHBvM0GBFcIV0&index=10

exercise19 - did on paper
*)

Definition least(y Y X E: Set) := (partial_order_relation E X) ∧ y ∈ Y ∧
Y ⊆ X ∧ ∀x:: Y. ⟨y, x⟩ ∈ E.
Definition minimal(y Y X E: Set) := (partial_order_relation E X) ∧ y ∈ Y ∧
Y ⊆ X ∧ ∀x:: Y. ⟨x, y⟩ ∈ E -> x = y.

Definition greatest(y Y X E: Set) := (partial_order_relation E X) ∧ y ∈ Y ∧
Y ⊆ X ∧ ∀x:: Y. ⟨x, y⟩ ∈ E.
Definition maximal(y Y X E: Set) := (partial_order_relation E X) ∧ y ∈ Y ∧
Y ⊆ X ∧ ∀x:: Y. ⟨y, x⟩ ∈ E -> x = y.

Definition least_strict(y Y X LT: Set) := (strict_partial_order_relation LT X) ∧ y ∈ Y ∧
Y ⊆ X ∧ ∀x::Y. x = y ∨ ⟨y, x⟩ ∈ LT.


Definition exercise20 (X E Y y: Set) (H: Y ⊆ X) (H2: ∀x::Y. ∀y::Y. comparable x y E) 
(y_in_Y: y ∈ Y): (least y Y X E) -> (minimal y Y X E).
intro.
both H0.
both H1.
both H0.
split.
split.
split;ass.
ass.
intros.
take H3 x H0.
both H1.
right H8.
take H4 x H0.
take H4 y H5.
take H1 x H10 y H11.
apply H12.
ass.
ass.
Qed.


Definition nonempty(X: Set) := ∃x. x ∈ X.

Definition well_order_relation (E X: Set) := 
(linear_order_relation E X) ∧ (∀Y. Y ⊆ X -> nonempty Y -> ∃y. least y Y X E).

Definition strict_well_order_relation (E X: Set) := 
(strict_linear_order_relation E X) ∧ (∀Y. Y ⊆ X -> nonempty Y -> ∃y. least_strict y Y X E).

Notation "⦅ X , E ⦆ 'is' 'a' 'well-ordered' 'set'" := (well_order_relation E X)(at level 70).
Notation "⦅ X , E ⦆ 'is' 'a' 'strictly' 'well-ordered' 'set'" := (strict_well_order_relation E X)(at level 70).

Notation "⦅ X , E ⦆ 'is' 'a' 'linearly' 'ordered' 'set'" := (linear_order_relation E X)(at level 70).
Notation "⦅ X , E ⦆ 'is' 'a' 'strictly' 'linearly' 'ordered' 'set'" := (strict_linear_order_relation E X)(at level 70).

Definition pred_ex(X LE s: Set)
: ∃1preds. ∀i. (i ∈ preds) ⇔ ((i ∈ X) ∧ (⟨i, s⟩ ∈ LE ∧ i ≠ s)).
take ZF2_subsets (fun i=> (⟨ i, s ⟩ ∈ LE ∧ i ≠ s)) X.
split.
apply H.
apply any_biimpl_set_is_no_more_than_one.
Qed.

Definition pred(X LE s: Set) := ι _ (pred_ex X LE s).

Definition succ_ex(X LE s: Set)
: ∃1preds. ∀i. (i ∈ preds) ⇔ ((i ∈ X) ∧ (⟨s, i⟩ ∈ LE ∧ i ≠ s)).
take ZF2_subsets (fun i=> (⟨ s, i ⟩ ∈ LE ∧ i ≠ s)) X.
split.
apply H.
apply any_biimpl_set_is_no_more_than_one.
Qed.

Definition succ(X LE s: Set) := ι _ (succ_ex X LE s).

Definition pred_in(X LE s x: Set) (H: ((x ∈ X) ∧ (⟨x, s⟩ ∈ LE ∧ x ≠ s))): x ∈ pred X LE s.
extract_iota_from_goal (pred X LE s).
take iota_prop x.
apply_b H0.
ass.
Qed.

Definition pred_el(X LE s x: Set) (H: x ∈ pred X LE s): ((x ∈ X) ∧ (⟨x, s⟩ ∈ LE ∧ x ≠ s)).
extract_iota (pred X LE s) H.
take iota_prop x.
left H0 H.
ass.
Qed.

Definition non_maximal_strict(x X LT: Set) := ∃y::X. ⟨x,y⟩ ∈ LT.

Definition successor(X LE s s_succ: Set) := least s_succ (succ X LE s) X LE.

Definition initial_segment (X LE I: Set) :=
I ⊆ X ∧  ∀i::I. (pred X LE i) ⊆ I.

Definition proper_initial_segment (X LE I: Set) := (initial_segment X LE I) ∧ I ≠ X.

(* every proper initial segment of a strictly well-ordered set 
is indeed the predecessors of some element *)

Definition not_eq_el (A B: Set) (H: A ≠ B): ∃x. x ∈ A ∨ x ∈ B. 
apply ex_in_alt.
intro.
apply H.
apply eq_in.
intros.
take H0 x.
take H2.
apply deMorganNotOr in H2.
left H2.
take H4 H1.
apply H5.
intro.
intro.
take H0 x.
apply deMorganNotOr in H2.
both H2.
apply (H4 H1).
Qed.

(* closed downwards *)
Definition every_proper_initial_segment_is_pred(X LE I: Set)(H: well_order_relation LE X) 
(H2: proper_initial_segment X LE I): ∃s::X. I = (pred X LE s).
take proper_subset_exists_element I X.
assert (I ⊂ X).
split.
left H2.
unfold initial_segment in H1.
left H1.
ass.
right H2.
ass.
take H0 H1.
ex_el H3.
both H3.
rename x into x_temp.
assert (x_temp ∈ (X - I)).
apply relative_complement_in.
split; ass.
assert ((X - I) ⊆ X).
intros.
apply relative_complement_el in H6.
left H6.
ass.
right H.
take H7 (X - I) H6.
assert (nonempty (X - I)).
ex_in x_temp.
apply H3.
take H8 H9.
ex_el H10.
unfold least in H10.
both H10.
both H11.
both H10.
clear H4 H5 H3 x_temp.
rename y into s.
ex_in s.
split.
apply relative_complement_el in H14.
both H14.
ass.
apply eq_in.
intro x.
intro.
apply pred_in.
split.
left H1.
take H4 x H3.
ass.
left H.
right H4.
assert (x ∈ X).
left H1.
take H10 x H3.
ass.
take H14.
apply relative_complement_el in H15.
both H15.
take H5 x H10 s H16.
unfold comparable in H15.
split.
disj H15.
ass.
assert (⊥).
left H2.
unfold initial_segment in H15.
right H15.
take H19 x H3.
take H20 s.
apply H17.
apply H21.
apply pred_in.
split.
ass.
split.
ass.
intro.
take H17.
repl H22 in H17.
apply H17.
ass.
apply H15.
intro.
repl <- H18 in H17.
apply H17.
ass.
intro.
intro.
apply pred_el in H3.
both H3.
both H5.
take H12 x.
assert (x ∉ (X - I)).
intro.
take H5 H15.
left H11.
right H17.
assert (s ∈ X).
apply relative_complement_el in H14.
both H14.
ass.
take H18 x H4 s H19 H3 H16.
apply H10.
ass.
apply relative_complement_el_alt in H15.
disj H15.
apply (H16 H4).
ass.
Qed.


(* 
MATH 320 - Set Theory - Lecture 4.2
https://www.youtube.com/watch?v=6Cs9F_pqQno&list=PLuiPz6iU5SQ_3Gubdqa1JHBvM0GBFcIV0&index=11
*)

Definition linear_order_is_reflective (X E: Set) (H: linear_order_relation E X):
reflexive E X.
left H.
left H0.
left H1.
right H2.
ass.
Qed.

Definition partial_order_is_reflective (X E: Set) (H: partial_order_relation E X):
reflexive E X.
left H.
left H0.
right H1.
ass.
Qed.

Ltac refl H :=
let HH := fresh "P" in 
match type of H with
| linear_order_relation ?E ?X => (pose proof (linear_order_is_reflective X E H) as HH); unfold reflexive in HH
| partial_order_relation ?E ?X => (pose proof (partial_order_is_reflective X E H) as HH); unfold reflexive in HH
end.

Definition get_fun_prop (f P Q: Set) (H: function_on_into f P Q):
∀ x . (∀ y . (∀ z . (⟨ x, y ⟩ ∈ f ∧ ⟨ x, z ⟩ ∈ f) ->
y = z)).
left H.
left H0.
right H1.
ass.
Qed.

Definition get_domain (f P Q: Set) (H: function_on_into f P Q):
domain f = P.
left H.
right H0.
unfold on in H1.
ass.
Qed.

Definition get_range (f P Q: Set) (H: function_on_into f P Q):
range f ⊆ Q.
right H.
apply H0.
Qed.

Definition get_set_of_pairs(f P Q: Set) (H: function_on_into f P Q):
∀x::f. (∃a. ∃b. x = ⟨ a, b ⟩).
intros.
left H.
left H1.
left H2.
take H3 x H0.
apply H4.
Qed.

Ltac set_of_pairs H :=
let HH := fresh "P" in 
match type of H with
| function_on_into ?f ?P ?Q=> (pose proof (get_set_of_pairs f P Q H) as HH)
end.

Ltac dom H :=
let HH := fresh "P" in 
match type of H with
| function_on_into ?f ?P ?Q=> (pose proof (get_domain f P Q H) as HH)
end.

Ltac fun_prop H :=
let HH := fresh "P" in 
match type of H with
| function_on_into ?f ?P ?Q=> (pose proof (get_fun_prop f P Q H) as HH)
end.

Ltac ran H :=
let HH := fresh "P" in 
match type of H with
| function_on_into ?f ?P ?Q=> (pose proof (get_range f P Q H) as HH)
end.

Definition partial_order_is_antisymmetric(X E: Set) (H: partial_order_relation E X):
anti_symmetric E X.
left H.
right H0.
ass.
Qed.

Ltac antisymm H :=
let HH := fresh "P" in 
match type of H with
| partial_order_relation ?E ?X => (pose proof (partial_order_is_antisymmetric X E H) as HH); unfold anti_symmetric in HH
end.

Definition in_linear_order_least_same_as_min (X E Y: Set) (H: linear_order_relation E X)
(H2: Y ⊆ X): ∀y. (least y Y X E) ⇔ (minimal y Y X E).
intro.
unfold least.
unfold minimal.
split.
intro.
both H0.
both H1.
both H0.
split.
split.
split.
ass.
ass.
ass.
intros.
take H3 x0 H0.
left H1.
right H8.
apply H9.
take H4 x H5.
take H4 x0 H0.
ass.
take H4 x H5.
ass.
ass.
ass.
intro.
both H0.
both H1.
both H0.
split.
split.
split.
ass.
ass.
ass.
intro y.
intro.
take H3 y H0.
right H.
unfold comparable in H7.
take H4 x H5.
take H4 y H0.
take H7 x H8 y H9.
disj H10.
ass.
take H6 H11.
repl H10.
left H1.
left H12.
refl H1.
take P x H8.
ass.
Qed.

Definition order_preserving (P Q E1 E2 f: Set)
(H3: function_on_into f P Q) := 
∀x. ∀x_in_p:x∈P. ∀y. ∀y_in_p:y∈P. ⟨x,y⟩ ∈ E1 ⇔ ⟨f⦅x⦆, f⦅y⦆⟩ ∈ E2.

Definition big_union_of_unit_set (y: Set): (⋃ {`y}) = y.
apply eq_in.
intros.
apply big_union_el in H.
ex_el H.
both H.
apply unit_set_el in H1.
repl H1 in H0.
ass.
intros.
apply big_union_in.
ex_in y.
split.
ass.
apply every_set_is_in_unit_set.
Qed.

Definition appl_prop_on (f X x: Set) (f_is_func_on: function_on f X) 
(x_in_X: x ∈ X): ∃y. f⦅x⦆ = y ∧ ⟨x,y⟩ ∈ f.
right f_is_func_on.
take H.
unfold on in H0.
apply eq_el_2 in H0.
take H0 x x_in_X.
apply domain_el in H1.
ex_el H1.
ex_in y.
split.
unfold appl.
take H1.
apply relational_image_in in H2.
assert (relational_image f x = {`y}).
apply eq_in.
intros.
apply unit_set_in.
apply relational_image_el in H3.
left f_is_func_on.
right H4.
rename H5 into P.
take P x y x0.
apply eq_symm.
apply H5.
split.
ass.
ass.
intro.
intro.
apply unit_set_el in H3.
repl H3.
ass.
repl H3.
apply big_union_of_unit_set.
ass.
Qed.


Definition appl_prop (f X Y x: Set) (f_is_func: function_on_into f X Y) 
(x_in_X: x ∈ X): ∃y. f⦅x⦆ = y ∧ ⟨x,y⟩ ∈ f.
assert (function_on f X).
split.
left f_is_func.
both H.
ass.
left f_is_func.
right H.
ass.
take appl_prop_on f X x H x_in_X.
ass.
Qed.



Definition appl_in_range(f P Q: Set) (H: function_on_into f P Q):
∀x. ∀xp:x∈P. f⦅x⦆ ∈ Q.
intro.
intros.
ran H.
take P0 (f⦅x⦆).
apply H0.
apply (range_in f (f ⦅ x ⦆) x).
take appl_prop f P Q x H x0.
ex_el H1.
both H1.
repl H2.
ass.
Qed.

Definition strong_induction: (forall (P: Set->Prop), 
(P 0) -> 
(∀x :: N. (∀k :: N. (k ≤ x) -> P k) -> (P (S x))) -> 
(∀x :: N. P x)).
take PN5_induction.
take ordinary_induction_is_equivalent_to_strong_induction.
left H0 H.
unfold strong_induction_prop in H1.
intros.
take H1 P H2.
assert ((∀ x :: N . (∀ k :: N . le k x -> P k) -> P (S x))).
intros.
take H3 x0 H6.
apply H8.
intros.
take H7 x1 H9.
apply H11.
unfold le.
unfold le_n in H10.
disj H10.
apply lt_n_el in H12.
left.
ass.
ass.
ass.
right.
ass.
take H5 H6.
take H7 x H4.
ass.
Qed.

Definition strong_induction_alt (A: Set) (H: A ⊆ N): 
(0 ∈ A) -> (∀x :: N. (∀k :: N. (k ≤ x) -> k ∈ A) -> ((S x) ∈ A)) -> A = N.
intros.
apply eq_in.
ass.
intro n.
intro.
take strong_induction (fun x => x ∈ A) H0 H1.
take H3 n H2.
ass.
Qed.

Ltac el H :=
match type of H with
| ∃ a . _ => ((ex_el H); el H)
| ?A ∧ ?B => 
(let L := fresh "L" in
let R := fresh "R" in
pose proof conj_el_1 _ _ H as L;
pose proof conj_el_2 _ _ H as R;
clear H;
el L; 
el R)
| _ => idtac 
end.


Definition n_lt_is_strict_partial_order: strict_partial_order_relation (<) N.
unfold partial_order_relation.
repeat split.
unfold relation.
intros.
apply lt_n_el_alt in H.
ex_el H.
both H.
ex_el H1.
both H1.
ex_in m.
ex_in n.
ass.
intros.
apply cartesian_product_in_2.
apply lt_n_el_alt in H.
el H.
ex_in m.
ex_in n.
repeat split; ass.
intros.
intro.
apply lt_n_el in H1.
apply lt_n_el in H2.
take every_natural_number_is_complete.
unfold complete in H3.
take H3 x H y H2.
take H3 y H0 x H1.
assert (x = y).
apply eq_in.
ass.
ass.
repl H6 in H2.
take no_natural_number_is_member_of_itself y H0.
apply H7.
ass.
ass.
ass.
ass.
ass.
unfold transitive.
intros x xn y yn.
take PN5_induction (fun z => ⟨ x, y ⟩ ∈ < -> ⟨ y, z ⟩ ∈ < -> ⟨ x, z ⟩ ∈ <).
apply H.
clear H.
intros.
apply lt_n_in.
ass.
apply PN1_empty_set.
apply lt_n_el in H0.
take any_set_in_empty_set_causes_contradiction H0.
apply H1.
ass.
apply lt_n_el in H0.
take any_set_in_empty_set_causes_contradiction H0.
apply H1.
apply lt_n_el in H0.
take any_set_in_empty_set_causes_contradiction H0.
apply H1.
ass.
apply PN1_empty_set.
apply PN1_empty_set.
clear H.
intros.
apply lt_n_in.
ass.
apply PN2_succ.
ass.
apply S_in.
take H0 H1.
apply lt_n_el in H2.
apply S_el in H2.
disj H2.
apply lt_n_in in H4.
unfold lt_n in H4.
take H3 H4.
left.
apply lt_n_el.
ass.
ass.
apply H2.
ass.
ass.
left.
repl H4 in H1.
apply lt_n_el.
ass.
ass.
apply H1.
ass.
apply PN2_succ.
ass.
Qed.

Definition spawn(s: Set): ∃spawned. spawned = s.
ex_in s.
apply eq_refl.
Qed.

Ltac spawn Name s :=
let H := fresh "H" in 
pose proof spawn s as H;
ex_el H;
rename spawned into Name.

Definition disj_assoc(A B C: Prop):
((A ∨ B) ∨ C) -> (A ∨ (B ∨ C)).
intro.
disj H.
disj H0.
left.
ass.
right.
left.
ass.
right.
right.
ass.
Qed.


Definition n_lt_m_implies_n_le_Sm:
∀n::N. ∀m::N. (n < m) -> (n ≤ S m).
intros.
assert (m < S m).
apply lt_n_in.
ass.
apply PN2_succ.
ass.
unfold S.
apply union_in.
right.
apply unit_set_in.
apply eq_refl.
take n_lt_is_strict_partial_order.
right H3.
assert (S m ∈ N).
apply PN2_succ.
ass.
take H4 x H m H0 (S m) H5 H1 H2.
left.
apply H6.
Qed.

Definition le_Sn (n: Set) (H: n ∈ N): n ≤ S n.
left.
apply lt_n_in.
ass.
apply PN2_succ.
ass.
unfold S.
apply union_in.
right.
apply unit_set_in.
apply eq_refl.
Qed.

Definition le_transitive(a b c: Set) (H1: a ∈ N) (H2: b ∈ N) (H3: c ∈ N): 
(a ≤ b) -> (b ≤ c) -> (a ≤ c).
intros.
take n_lt_is_strict_partial_order.
right H4.
unfold transitive in H5.
take H5 a H1 b H2 c H3.
disj H.
disj H0.
left.
apply H6.
ass.
ass.
repl H in H7.
left.
ass.
repl <- H7 in H0.
ass.
Qed.


Definition n_lt_m_implies_Sn_le_m:
∀n::N. ∀m::N. (n < m) -> (S n ≤ m).
intro.
intro.
take (PN5_induction (fun m => x < m -> S x ≤ m)).
apply H0.
intro.
apply lt_n_el in H1.
take (any_set_in_empty_set_causes_contradiction H1).
apply H2.
ass.
apply PN1_empty_set.
intros.
rename x0 into y.
apply lt_n_el in H3.
unfold S in H3.
apply union_el in H3.
disj H3.
apply lt_n_in in H4.
take H2 H4.
take le_Sn y H1.
take PN2_succ x H.
take PN2_succ y H1.
take le_transitive (S x) y (S y) H6 H1 H7 H3 H5.
ass.
ass.
ass.
apply unit_set_el in H4.
repl H4.
right.
apply eq_refl.
ass.
unfold S in H3.
apply lt_n_el in H3.
apply union_el in H3.
disj H3.
apply lt_n_in in H4.
apply PN2_succ.
ass.
ass.
ass.
apply PN2_succ.
ass.
ass.
apply PN2_succ.
ass.
Qed.

(* Used https://math.stackexchange.com/questions/1836028/proving-the-well-ordering-principle-for-natural-numbers *)
Definition every_nonempty_subset_of_N_has_least_element 
(A: Set) (A_nonempty: nonempty A) (subset_N: A ⊆ N)
(linear: strict_linear_order_relation (<) N):
∃k::A. (least_strict k A N (<)).
unfold least_strict.
assert ((∃ k :: A
. (∀ x :: A . x = k ∨ ⟨ k, x ⟩ ∈ <)) -> (∃ k :: A
. ((⦅ N, < ⦆ is a strictly partially ordered set ∧ k ∈ A) ∧ A ⊆ N)
∧ (∀ x :: A . x = k ∨ ⟨ k, x ⟩ ∈ <))).
intro.
el H.
ex_in k.
split.
ass.
split.
split.
split.
apply n_lt_is_strict_partial_order.
ass.
ass.
ass.
apply H.
clear H.
take exc_thrd (0 ∈ A).
disj H.
ex_in 0.
split.
ass.
intros.
take subset_N x H.
take zero_le_nn x H1.
disj H2.
right.
apply H3.
left.
repl H3.
apply eq_refl.
spawn B (N - A).
assert (B ⊆ N).
intros.
repl H in H1.
apply relative_complement_el in H1.
both H1.
ass.
assert (0 ∈ B).
apply eq_el_2 in H.
take H 0.
apply H2.
apply relative_complement_in.
split.
apply PN1_empty_set.
ass.
apply ex_in_alt.
intro.
take strong_induction_alt B H1 H2.
assert (B = N -> ⊥).
intro.
repl <- H5 in H.
assert (A = 0).
repl <- H5 in subset_N.
apply eq_in.
intro.
intro.
take subset_N x H6.
apply eq_el_1 in H.
take H x H7.
apply relative_complement_el in H8.
both H8.
apply (H10 H6).
apply empty_set_is_subset_of_any.
unfold nonempty in A_nonempty.
ex_el A_nonempty.
apply eq_el_1 in H6.
take H6 x A_nonempty.
apply any_set_in_empty_set_causes_contradiction in H7.
ass.
apply H5.
apply H4.
clear H4 H5.
intros.
take H5 (S x).
rename x into n.
assert (∀ k :: N . k ≤ n -> k ∉ A).
intros.
intro.
take H5 x H7 H8.
apply eq_el_1 in H.
take H x H10.
apply relative_complement_el in H11.
both H11.
apply H13.
ass.
assert (∀x::A. n < x).
intros.
right linear.
take subset_N x H8.
take H9 n H4 x H10.
unfold strictly_comparable in H11.
apply disj_assoc in H11.
disj H11.
apply H12.
take H7 x H10.
assert (x ≤ n).
unfold le_n.
disj H12.
left.
ass.
right.
repl_in_goal H13.
apply eq_refl.
take H11 H13.
apply (H14 H8).
assert ((¬(S n ∈ A)) -> S n ∈ B).
intro.
apply eq_el_2 in H.
take H (S n).
apply H10.
apply relative_complement_in.
split.
apply PN2_succ.
ass.
ass.
apply H9.
intro.
take H3 (S n).
apply H11.
split.
ass.
intros.
take H8 x H12.
apply n_lt_m_implies_Sn_le_m in H13.
disj H13.
right.
apply H14.
left.
repl H14.
apply eq_refl.
ass.
take subset_N x H12.
ass.
Qed.

Definition n_lt_is_strictly_lineary_ordered: strict_linear_order_relation (<) N.
split.
apply n_lt_is_strict_partial_order.
intros.
unfold strictly_comparable.
take trichotomy_for_set_inclusion_only_disj x H b H0.
disj H1.
disj H2.
left.
left.
apply lt_n_in.
ass.
ass.
ass.
right.
ass.
left.
right.
apply lt_n_in.
ass.
ass.
ass.
Qed.


(** MILESTONE PROOF **)
Definition n_lt_is_strictly_well_ordered: strict_well_order_relation (<) N.
split.
apply n_lt_is_strictly_lineary_ordered.
intros.
take every_nonempty_subset_of_N_has_least_element x H0 H n_lt_is_strictly_lineary_ordered.
ex_el H1.
both H1.
ex_in k.
ass.
Qed.

Definition N_in (x: Set): (x = 0) ∨ (∃p::N. S p = x) -> 
x ∈ N.
intros.
disj H.
repl H0.
apply PN1_empty_set.
ex_el H0.
both H0.
apply eq_symm in H1.
repl_in_goal H1.
apply PN2_succ.
ass.
Qed.

Definition N_el (x: Set): x ∈ N -> (x = 0) ∨ (∃p::N. S p = x).
generalize dependent x.
take PN5_induction (fun x => x = 0 ∨ (∃ p :: N . S p = x)).
apply H.
left.
apply eq_refl.
intros.
disj H1.
right.
ex_in (0).
split.
apply PN1_empty_set.
repl H2.
apply eq_refl.
right.
ex_el H2.
both H2.
ex_in (S p).
split.
apply PN2_succ.
ass.
repl_in_goal_backward H3.
apply eq_refl.
Qed.

(* stopped at https://youtu.be/6Cs9F_pqQno?list=PLuiPz6iU5SQ_3Gubdqa1JHBvM0GBFcIV0&t=856 *)

Definition induction_on_subset_of_natural_number(n N': Set) (H: n ∈ N') (H2: N' ⊆ N):
forall (P: Set->Prop), 
(P 0) -> 
(∀x :: N. (x ∈ N' -> P x) -> (((S x) ∈ N' -> P (S x)))) ->  
(∀x :: N. x ∈ N' -> P x).
intro.
take PN5_induction (fun x => (x ∈ N' -> P x)).
intros.
assert ((0 ∈ N' -> P 0)).
intro.
ass.
take H0 H6.
assert ((∀ x :: N . (x ∈ N' -> P x) -> S x ∈ N' -> P (S x))).
intros.
take H3 x0 H8 H9 H10.
ass.
take H7 H8.
take H9 x H4 H5.
ass.
Qed.

Definition intersection_symm(A B: Set): (A ∩ B) = (B ∩ A).
apply eq_in.
intros.
apply intersection_el in H.
both H.
apply intersection_in.
ass.
ass.
intros.
apply intersection_el in H.
both H.
apply intersection_in.
ass.
ass.
Qed.

Definition induction_applied(x: Set) (x_in_N: x ∈ N): forall (P: Set->Prop), 
(P 0) -> (∀x :: N. P x -> (P (S x))) -> P x.
intros.
take PN5_induction P H H0.
take H1 x x_in_N.
ass.
Qed.

Definition not_all_implies_ex (P: Set->Prop) (u : (¬(∀x . P x))): (∃x. (¬(P x))).
apply all_el_alt.
ass.
Qed.

Definition m_eq_Sm_implies_contradiction(m: Set) (m_in_N: m ∈ N): ¬(m = S m).
intro.
unfold S in H.
apply eq_el_2 in H.
take H m.
assert (m ∈ (m ∪ {`m})).
apply union_in.
right.
apply unit_set_in.
apply eq_refl.
take H0 H1.
take no_natural_number_is_member_of_itself m m_in_N.
apply H3.
ass.
Qed.


Definition Sm_in_Sn_implies_m_in_Sn 
(m: Set) (m_in_N: m ∈ N) (n: Set) (n_in_N: n ∈ N): (S m ∈ S n) -> (m ∈ S n).
intro.
apply union_el in H.
disj H.
take every_natural_number_is_complete n n_in_N (S m) H0.
assert (m ∈ S m).
unfold S.
apply union_in.
right.
apply unit_set_in.
apply eq_refl.
take H m H1.
apply union_in.
left.
ass.
apply unit_set_el in H0.
apply union_in.
left.
repl_in_goal_backward H0.
apply union_in.
right.
apply unit_set_in.
apply eq_refl.
Qed.

Notation "'asm'" := (ltac:(assumption)).


Definition pair_unord_of_two_pairs_is_function(a b: Set): function {⟨ 0, a ⟩, ⟨ 1, b ⟩}.
split.
intros.
unfold ordered_pair.
apply pair_unord_el in H.
disj H.
ex_in 0.
ex_in a.
ass.
ex_in 1.
ex_in b.
ass.
intros.
el H.
apply pair_unord_el in L.
apply pair_unord_el in R.
disj L.
disj R.
apply pair_property in H.
both H.
apply pair_property in H0.
both H0.
repl H2.
repl H3.
apply eq_refl.
apply pair_property in H.
both H.
apply pair_property in H0.
both H0.
repl H1 in H.
take zero_not_equals_to_one.
apply (H0 H).
disj R.
apply pair_property in H.
both H.
apply pair_property in H0.
both H0.
repl H1 in H.
take zero_not_equals_to_one.
apply eq_symm in H.
apply (H0 H).
apply pair_property in H.
both H.
apply pair_property in H0.
both H0.
repl H2.
repl H3.
apply eq_refl.
Qed.

Definition n_in_m_implies_Sn_in_m_OR_sn_eq_m(n m: Set) (n_in_N: n ∈ N): m ∈ n -> (S m ∈ n ∨ S m = n).
apply (induction_applied n n_in_N).
intro.
take (set_in_zero_causes_contradiction H).
apply H0.
intros.
apply union_el in H1.
apply disj_comm in H1.
disj H1.
apply element_of_unit_set in H2.
repl H2.
right.
apply eq_refl.
take H0 H2.
disj H1.
left.
apply S_in.
left.
ass.
repl <- H3 in H2.
repl_in_goal_backward H3.
left.
apply S_in.
right.
apply eq_refl.
Qed.


Definition n_in_Sn(n: Set): n ∈ S n.
apply S_in.
right.
apply eq_refl.
Qed.

Definition compatible(f g: Set) := ∀x::((domain f) ∩ (domain g)). f⦅x⦆ = g⦅x⦆.

Definition union_of_compatible_functions_is_a_function (s: Set) 
(s_set_of_functions: set_of_functions s) 
(pairwise_compatible: (∀f::s. ∀g::s. compatible f g)): 
((function (⋃ s))).
take union_of_compatible_functions_is_a_function_deprecated s s_set_of_functions.
apply H.
intros.
take pairwise_compatible x H0 g H1.
unfold compatible in H2.
unfold compatible_deprecated.
intros.
take H2 x0 H3.
take s_set_of_functions x H0.
assert (function_on x (domain x)).
split.
ass.
unfold on.
apply eq_refl.
apply intersection_el in H3.
both H3.
take appl_prop_on x (domain x) x0 H6 H7.
ex_el H3.
both H3.
ex_in y.
split.
ass.
assert (function_on g (domain g)).
split.
take s_set_of_functions g H1.
ass.
apply eq_refl.
take appl_prop_on g (domain g) x0 H3 H8.
ex_el H11.
both H11.
repl H4 in H9.
apply eq_symm in H9.
take eq_trans _ _ _ H9 H12.
repl H11.
ass.
Qed.

Definition n_in_N_implies_n_subset_N (n: Set) (H: n ∈ N): n ⊆ N.
apply (induction_applied n).
ass.
apply empty_set_is_subset_of_any.
intros.
intros.
apply S_el in H2.
disj H2.
take H1 x0 H3.
ass.
repl H3.
ass.
Qed.

Ltac eq_refl := apply eq_refl.

Definition Sm_in_n_implies_m_in_n (m n: Set) (H:n ∈ N): S m ∈ n -> m ∈ n.
intro.
take n_in_Sn m.
take every_natual_number_is_transitive n H m (S m).
apply H2.
split; ass.
Qed.

Definition n_step_computation(t n x X f: Set) :=
t⦅0⦆ = x ∧ ∀k::n. (t⦅(S k)⦆) = (f⦅(t⦅k⦆)⦆).

Definition functional_equality(f1 f2 A B: Set) 
(H1: function_on_into f1 A B) (H2: function_on_into f2 A B): 
(∀x::A. f1⦅x⦆ = f2⦅x⦆) -> f1 = f2.
intro.
apply eq_in.
intros.
left H1.
left H3.
left H4.
take H5 x H0.
unfold ordered_pair in H6.
el H6.
repl H6.
right H3.
unfold on in H7.
repl H6 in H0.
take domain_in f1 a b H0.
apply eq_el_1 in H7.
take H7 a H8.
take H a H9.
take appl_prop _ _ _ a H1 H9.
ex_el H11.
both H11.
assert (b = y).
right H4.
take H11 a b y.
apply H14.
split; ass.
repl H11.
apply eq_symm in H12.
take eq_trans _ _ _ H12 H10.
take appl_prop _ _ _ a H2 H9.
ex_el H15.
both H15.
repl <- H10 in H16.
take eq_trans _ _ _ H12 H16.
repl H15.
ass.
intros.
left H2.
left H3.
left H4.
take H5 x H0.
unfold ordered_pair in H6.
el H6.
repl H6.
right H3.
unfold on in H7.
repl H6 in H0.
take domain_in f2 a b H0.
apply eq_el_1 in H7.
take H7 a H8.
take H a H9.
take appl_prop _ _ _ a H2 H9.
ex_el H11.
both H11.
assert (b = y).
right H4.
take H11 a b y.
apply H14.
split; ass.
repl H11.
take eq_trans _ _ _ H10 H12.
take appl_prop _ _ _ a H1 H9.
ex_el H15.
both H15.
repl H10 in H16.
apply eq_symm in H12.
take eq_trans _ _ _ H12 H16.
repl H15.
ass.
Qed.



Definition restriction_to_subset_is_still_a_function
(f X Y A g: Set) (H: function_on_into f X Y) (H2: A ⊆ X) (Hg: g = (f ↾ A)):
function_on_into g A Y.
repl Hg.
unfold restriction.
split.
split.
split.
intro.
intro.
apply intersection_el in H0.
both H0.
left H.
left H0.
left H4.
take H5 x H1.
ass.
intros.
el H0.
apply intersection_el in L, R.
el L.
el R.
fun_prop H.
take P x y z.
apply H0.
split. 
ass.
ass.
apply eq_in.
intros.
apply domain_el in H0.
ex_el H0.
apply intersection_el in H0.
both H0.
apply cartesian_product_el in H3.
left H3.
ass.
intros.
dom H.
apply eq_el_2 in P.
take H2 x H0.
take P x H1.
apply domain_el in H3.
ex_el H3.
apply (domain_in (f ∩ A × (range f)) x y).
apply intersection_in.
ass.
apply cartesian_product_in.
ass.
assert (y ∈ range f) as rrr.
apply range_in in H3.
ass.
ass.
intros.
apply range_el in H0.
ex_el H0.
apply intersection_el in H0.
both H0.
apply cartesian_product_el in H3.
both H3.
rename x into y.
rename x0 into x.
ran H.
take P y H4.
ass.
Qed.

Definition restriction_el_1 (p f A: Set): p ∈ f ↾ A -> p ∈ f.
intro.
unfold restriction in H.
apply intersection_el in H.
both H.
ass.
Qed.

Definition restriction_appl_same_as_original
(f X Y A g: Set) (H: function_on_into f X Y) (H2: A ⊆ X) (Hg: g = (f ↾ A)):
∀x::A. g⦅x⦆ = f⦅x⦆.
intros.
take restriction_to_subset_is_still_a_function f X Y A g H H2 Hg.
take H2 x H0.
take appl_prop _ _ _ x H H3.
ex_el H4.
both H4.
repl_in_goal H5.
take appl_prop _ _ _ x H1 asm.
ex_el H4.
both H4.
repl_in_goal H7.
apply eq_el_1 in Hg.
take Hg _ H8.
apply restriction_el_1 in H4.
fun_prop H.
take P x y0 y.
apply H9.
split; ass.
Qed.

Definition m_in_n_implies_Sm_in_Sn 
(m: Set) (m_is_natual_number: m ∈ N) 
(n: Set) (n_is_natual_number: n ∈ N)
: (m ∈ n) -> ((S m) ∈ (S n)).
take m_in_n_equiv_Sm_in_Sn m asm n asm.
left H.
apply H0.
Qed.

Definition m_in_n_n_in_N_implies_m_in_N (m n: Set) (H: m ∈ n) (H2: n ∈ N): m ∈ N.
generalize dependent m.
intro.
apply (induction_applied n).
ass.
intro.
apply any_set_in_empty_set_causes_contradiction in H.
apply H.
intros.
apply S_el in H1.
disj H1.
take H0 H3.
ass.
repl_in_goal H3.
ass.
Qed.

(* https://chatgpt.com/c/6a8d2c77-ea30-83ea-add3-5ba36473a278 *)
Definition two_n_step_computations_are_equal(n x X Y f: Set) (H: n ∈ N):
∀t. ∀u. function_on_into t (S n) Y -> function_on_into u (S n) Y ->
n_step_computation t n x X f -> n_step_computation u n x X f -> t = u.
unfold n_step_computation.
apply (induction_applied n).
ass.
intros.
both H2.
both H3.
apply (functional_equality _ _ _ _ H0 H1).
intros.
apply S_el in H3.
disj H3.
apply any_set_in_empty_set_causes_contradiction in H7.
apply H7.
repl H7.
repl_in_goal H4.
repl_in_goal H2.
eq_refl.
intros.
apply (functional_equality _ _ _ _ H2 H3).
assert (∀x1. x1 ∈ S x0 -> t⦅x1⦆ = u⦅x1⦆) as first_part.
intro.
intro.
assert (S x0 ⊆ S (S x0)).
intros.
apply S_in.
left.
ass.
spawn t' (restriction t (S x0)).
spawn u' (restriction u (S x0)).
take restriction_to_subset_is_still_a_function t (S (S x0)) Y (S x0) t'
asm H7 asm.
take restriction_to_subset_is_still_a_function u (S (S x0)) Y (S x0) u'
asm H7 asm.
take H1 t' u' asm asm.
both H4.
both H5.
assert (0 ∈ S x0).
apply S_in.
take exc_thrd (0 = x0).
disj H5.
right.
ass.
left.
assert (x0 ≠ 0).
intro.
apply eq_symm in H5.
apply (H16 H5).
take zero_in_every_natual_number x0 asm asm.
ass. 
take restriction_appl_same_as_original _ _ _ (S x0) t' H2 H7 asm.
take restriction_appl_same_as_original _ _ _ (S x0) u' H3 H7 asm.
assert ((t'⦅0⦆ = x
∧ (∀k::x0. t'⦅S k⦆ = f⦅t'⦅k⦆⦆))) as one.
split.
take H16 0 asm.
repl_in_goal H18.
ass.
intros.
assert (x2 ∈ S x0).
apply S_in.
left. 
ass.
take H14 x2 H19.
take H18.
apply m_in_n_implies_Sm_in_Sn in H21.
take H16 (S x2) asm.
repl_in_goal H22.
take H16 (x2) asm.
repl_in_goal H23.
ass.
take H0.
take m_in_n_n_in_N_implies_m_in_N _ _ H21 H22.
ass.
ass.
assert ((u'⦅0⦆ = x ∧ (∀k::x0. u'⦅S k⦆ = f⦅u'⦅k⦆⦆))) as two.
split.
take H17 0 asm.
repl_in_goal H18.
ass.
intros.
assert (x2 ∈ S x0).
apply S_in.
left. 
ass.
take H15 x2 H19.
take H18.
apply m_in_n_implies_Sm_in_Sn in H21.
take H17 (S x2) asm.
repl_in_goal H22.
take H17 (x2) asm.
repl_in_goal H23.
ass.
take H0.
take m_in_n_n_in_N_implies_m_in_N _ _ H21 H22.
ass.
ass.
take H12 one two.
take H17 x1 asm.
take H16 x1 asm.
repl_in_goal_backward H19.
repl_in_goal_backward H20.
repl H18.
eq_refl.
(* split *)
intros.
apply S_el in H6.
disj H6.
take first_part asm.
apply H6.
ass.
both H4.
both H5.
assert (x0 ∈ S x0).
apply S_in.
right.
eq_refl.
take H8 x0 H5.
take H9 x0 H5.
repl H7.
repl H10.
repl H11.
take first_part x0 asm.
repl H12.
eq_refl.
Qed.

Definition function_on_into_in(f X Y: Set): 
((∀x::f. (∃a. ∃b. x = ⟨ a, b ⟩)) ∧
(∀x. (∃y. ⟨x,y⟩ ∈ f) -> x ∈ X) ∧ 
(∀x. x ∈ X -> (∃y. ⟨x,y⟩ ∈ f)) ∧
(∀x. (∀y. (∀z. (⟨ x, y ⟩ ∈ f ∧ ⟨ x, z ⟩ ∈ f) -> y = z))) ∧
(∀y. (∃x. ⟨x,y⟩ ∈ f) -> y ∈ Y)) ->
function_on_into f X Y.
intro.
el H.
split.
split.
split.
apply L0.
ass.
unfold on.
apply eq_in.
intros.
apply domain_el in H.
ex_el H.
take R2 x.
apply H0.
ex_in y.
ass.
intros.
take R1 x.
take H0 H.
ex_el H1.
apply (domain_in f x y).
ass.
intros.
apply range_el in H.
ex_el H.
take R x.
apply H0.
ex_in x0.
ass.
Qed.

Definition S0_el(x: Set): x ∈ S 0 -> x = 0.
intro.
apply S_el in H.
disj H.
apply any_set_in_empty_set_causes_contradiction in H0.
apply H0.
ass.
Qed.

Definition S0_in(x: Set): x = 0 -> x ∈ S 0.
intro.
apply S_in.
right.
ass.
Qed.

Ltac appl_2 f x :=
let H := fresh "H" in
  lazymatch goal with
  | f_is_func : (function_on_into f ?A ?B) |- _ => 
      lazymatch goal with
      | x_in_domain : (x ∈ A) |- _ => 
          (pose proof appl_prop f A B x f_is_func x_in_domain as H;
          ex_el H; both H)
      | _ => fail "Unable to grab x_in_domain"
      end
  | _ => fail "Unable to grab f_is_func"
  end.

Ltac appl f x :=
let H := fresh "H" in
let H2 := fresh "H" in
let H3 := fresh "H" in
let xx := fresh "xx" in
  lazymatch goal with
  | f_is_func : (function_on_into f ?A ?B) |- _ => 
      lazymatch goal with
      | x_in_domain : (x ∈ A) |- _ => 
          (pose proof appl_prop f A B x f_is_func x_in_domain as H;
          ex_el_named H xx;
          pose proof conj_el_1 _ _ H as H2;
          pose proof conj_el_2 _ _ H as H3;
          clear H;
          repl <- H2 in H3;
          clear H2;
          clear xx)
      | _ => fail "Unable to grab x_in_domain"
      end
  | _ => fail "Unable to grab f_is_func"
  end.
  
Definition appl_in_trick(f x y: Set): 
(⟨x,y⟩ ∈ f) -> (∀z. ⟨x,z⟩ ∈ f -> z = y) -> f⦅x⦆ = y.
intros.
apply eq_in.
intros.
apply big_union_el in H1.
ex_el H1.
both H1.
apply relational_image_el in H3.
take H0 s H3.
repl_in_goal_backward H1.
ass.
intros.
apply big_union_in.
ex_in y.
split.
ass.
apply relational_image_in.
ass.
Qed.

Definition appl_in_from_pair(f P Q: Set) (f_func: function_on_into f P Q)
(x y: Set) (x_in_P: x ∈ P): ⟨ x, y ⟩ ∈ f -> f⦅x⦆ = y.
intro.
appl_2 f x.
repl H1.
fun_prop f_func.
take P0 x y0 y.
apply H0.
split.
all: ass.
Qed.

Definition zero_eq_Sn_implies_contradiction (n: Set):  ¬(0 = S n).
intro.
apply eq_el_2 in H.
take n_in_Sn n.
take H n H0.
apply any_set_in_empty_set_causes_contradiction in H1.
ass.
Qed.

Definition S_el_exclusive(n m: Set) (n_in_N: n ∈ N) (m_in_N: m ∈ N)
(H: n ∈ S m): 
(n ∈ m ∧ (¬(n = m))) ∨ (n = m ∧ (¬(n ∈ m))).
apply union_el in H.
disj H.
left.
split.
ass.
intro.
repl H in H0.
apply (no_natural_number_is_member_of_itself m).
ass.
ass.
apply unit_set_el in H0.
right.
split.
ass.
intro.
repl H0 in H.
apply (no_natural_number_is_member_of_itself m).
ass.
ass.
Qed.

Definition functional_equality_specific(f g A B C D: Set) 
(H1: function_on_into f A B) (H2: function_on_into g C D): 
(∀x::(A ∩ C). (∃y. ⟨x,y⟩ ∈ f ∧ ⟨x,y⟩ ∈ g) -> f⦅x⦆ = g⦅x⦆).
intros.
ex_el H0.
both H0.
apply intersection_el in H.
both H.
appl_2 f x.
appl_2 g x.
repl_in_goal H6.
repl_in_goal H8.
assert (y0 = y).
fun_prop H1.
take P x y0 y.
apply H.
split; ass.
assert (y1 = y).
fun_prop H2.
take P x y1 y.
apply H10.
split;ass.
repl_in_goal H.
repl_in_goal H10.
eq_refl.
Qed.



Definition recursion_theorem(f x X: Set) (x_in_X: x ∈ X) (F: function_on_into f X X):  
∃1g. function_on_into g N X ∧ g⦅0⦆ = x ∧ ∀n::N. (g⦅(S n)⦆) = (f⦅(g⦅n⦆)⦆).
subset (power_set(N × X)) (fun t => t⦅0⦆ = x ∧ 
∃n::N. (function_on_into t (S n) X) ∧ t⦅0⦆ = x ∧ ∀k::n. (t⦅(S k)⦆) = (f⦅(t⦅k⦆)⦆)).
rename b into G.
assert (∀t. t ∈ G -> (t ⦅ 0 ⦆ = x ∧ 
(∃ n :: N . (function_on_into t (S n) X) ∧ t ⦅ 0 ⦆ = x ∧ (∀ k :: n . t ⦅ S k ⦆ = f ⦅ t ⦅ k ⦆ ⦆)))).
intro.
take H x0.
left H0.
intro.
take H1 H2.
both H3.
ass.
rename H0 into GP1.
assert (∀t::G. t ⊆ N × X).
intros.
take H x0.
left H1 H0.
left H2.
apply power_set_el in H3.
ass.
assert (∀x1. ∀y1. ∀t. ⟨x1,y1⟩ ∈ t -> t ∈ G -> x1 ∈ N).
intros.
take H0 t H2.
take H3 ⟨ x0, y1 ⟩ H1.
apply cartesian_product_el in H4.
left H4.
ass.
rename H0 into GP2.
rename H1 into NN.
split.
ex_in (⋃ G).
assert (set_of_functions G) as set_of_f.
(* proof of set_of_functions G*)
intros.
take GP1 x0 H0.
el H1.
left L2.
left H1.
ass.
assert (∀f::G. (∀g::G. compatible f g)) as pairwise_compatible_prop.
(* proof of pairwise compatibility *)
intro t.
intro.
intro u.
intro.
unfold compatible.
intros.
apply intersection_el in H2.
both H2.
spawn n (domain t).
spawn m (domain u).
take H3.
take H4.
repl <- H2 in H6.
repl <- H5 in H7.
assert (n ∈ N).
take GP1 t H0.
right H8.
clear H8.
ex_el H9.
both H9.
left H10.
left H9.
clear H10 H9.
take H8.
apply PN2_succ in H9.
dom H11.
repl H2.
repl P.
ass.
assert (m ∈ N).
take GP1 u H1.
right H9.
clear H9.
ex_el H10.
both H10.
left H11.
left H10.
take H9.
apply PN2_succ in H13.
dom H12.
repl H5.
repl P.
ass.
assert (x0 ∈ N) as x0_in_N.
apply domain_el in H3.
ex_el H3.
take NN x0 y t H3 H0.
ass.
(* prepare all I need here *)
take GP1 t H0.
both H10.
ex_el H12.
both H12.
both H13.
both H12.
clear H15.
take GP1 u H1.
both H12.
ex_el H16.
both H16.
both H17.
both H16.
clear H19.
assert (n = S n0).
dom H13.
repl_in_goal_backward P.
ass.
assert (m = S n1).
dom H17.
repl_in_goal_backward P.
ass.
rename n1 into m0.
take trichotomy_for_set_inclusion_only_disj m asm n asm.
apply disj_comm in H20.
disj H20.
(* case n ∈ m*)
assert (n ⊆ m).
intros.
take every_natual_number_is_transitive m asm x1 n.
apply H22.
split; ass.
subset n (fun k => t⦅k⦆ ≠ u⦅k⦆).
apply DN_el.
intro.
assert (nonempty b).
ex_in x0.
take H22 x0.
apply_b H24.
split.
ass.
ass.
assert (b ⊆ N).
intros.
take H22 x1.
left H26 H25.
both H27.
apply n_in_N_implies_n_subset_N in H8.
take H8 x1.
apply H27.
ass.
take n_lt_is_strictly_well_ordered.
right H26.
take H27 b H25 H24.
ex_el H28.
rename y into k'.
unfold least_strict in H28.
el H28.
clear R0 L.
assert (k' ∈ n).
take H22 k'.
left H28 R1.
left H29.
ass.
assert (k' ∈ N) as k_in_N.
take H25.
take H29 k'.
apply H30.
ass.
assert(k' ≠ 0).
intro.
take H22 k'.
left H30 R1.
right H31.
apply H32.
repl_in_goal H29.
repl H11.
repl H15.
eq_refl.
take k_in_N.
apply N_el in H30.
disj H30.
apply H29.
ass.
ex_el H31.
both H31.
rename p into k.
assert (t⦅k⦆ = u⦅k⦆).
apply DN_el.
intro.
take H22 k.
right H33.
assert ((k ∈ n ∧ t⦅k⦆ ≠ u⦅k⦆)).
split.
take H28.
repl <- H32 in H35.
take H30.
apply Sm_in_n_implies_m_in_n.
ass.
ass.
ass.
take H34 H35.
change (∀x::b. x = k' ∨ k' < x) in R.
take R k H36.
disj H37.
repl <- H32 in H38.
apply (m_eq_Sm_implies_contradiction k asm).
ass.
repl <- H32 in H38.
assert (k < S k).
apply lt_n_in.
ass.
apply PN2_succ.
ass.
apply union_in.
right.
apply every_set_is_in_unit_set.
take n_lt_is_strictly_lineary_ordered.
left H39.
left H40.
right H41.
assert (S k ∈ N).
apply PN2_succ.
ass.
take H42 k asm (S k) H43 H37.
apply H44.
ass.

assert (k ∈ n0) as k_in_n0.
take H28.
repl H16 in H33.
repl <- H32 in H33.
apply Sm_in_Sn_implies_m_in_Sn in H33.
apply S_el in H33.
disj H33.
ass.
take H28.
repl <- H32 in H33.
repl H16 in H33.
repl H34 in H33.
repl H34 in H30. 
assert (S n0 ∈ N).
apply PN2_succ.
ass.
take no_natural_number_is_member_of_itself (S n0) H35.
apply (H36 H33).
ass.
ass. 
assert (k ∈ m0) as k_in_m0.
assert (k' ∈ m) as H33.
take H20 k' H28.
ass.
repl H19 in H33.
repl <- H32 in H33.
apply Sm_in_Sn_implies_m_in_Sn in H33.
apply S_el in H33.
disj H33.
ass.
take H28.
take H20 k' H33.
repl H19 in H35.
repl <- H32 in H35.
repl H34 in H35.
take PN2_succ m0 H12.
take no_natural_number_is_member_of_itself (S m0) asm.
apply (H37 H35).
ass.
ass.

(* problem here*)
take H14 k asm.
assert (f⦅t⦅k⦆⦆ = f⦅u⦅k⦆⦆).
repl H31.
eq_refl.
assert (S k ∈ N).
apply PN2_succ.
ass.
take H18 k asm.
take H22 k'.
left H37 R1.
right H38.
apply H39.
repl_in_goal_backward H32.
repl_in_goal H33.
repl_in_goal H36.
ass.
(* case m ∈ n*)
disj H21.
assert (m ⊆ n).
intros.
take every_natual_number_is_transitive n asm x1 m.
apply H22.
split; ass.
subset m (fun k => t⦅k⦆ ≠ u⦅k⦆).
apply DN_el.
intro.
assert (nonempty b).
ex_in x0.
take H22 x0.
apply_b H24.
split.
ass.
ass.
assert (b ⊆ N).
intros.
take H22 x1.
left H26 H25.
both H27.
apply n_in_N_implies_n_subset_N in H9.
take H9 x1.
apply H27.
ass.
take n_lt_is_strictly_well_ordered.
right H26.
take H27 b H25 H24.
ex_el H28.
rename y into k'.
unfold least_strict in H28.
el H28.
clear R0 L.
assert (k' ∈ m).
take H22 k'.
left H28 R1.
left H29.
ass.
assert (k' ∈ N) as k_in_N.
take H25.
take H29 k'.
apply H30.
ass.
assert(k' ≠ 0).
intro.
take H22 k'.
left H30 R1.
right H31.
apply H32.
repl_in_goal H29.
repl H11.
repl H15.
eq_refl.
take k_in_N.
apply N_el in H30.
disj H30.
apply H29.
ass.
ex_el H31.
both H31.
rename p into k.
assert (t⦅k⦆ = u⦅k⦆).
apply DN_el.
intro.
take H22 k.
right H33.
assert ((k ∈ m ∧ t⦅k⦆ ≠ u⦅k⦆)).
split.
take H28.
repl <- H32 in H35.
take H30.
apply Sm_in_n_implies_m_in_n.
ass.
ass.
ass.
take H34 H35.
change (∀x::b. x = k' ∨ k' < x) in R.
take R k H36.
disj H37.
repl <- H32 in H38.
apply (m_eq_Sm_implies_contradiction k asm).
ass.
repl <- H32 in H38.
assert (k < S k).
apply lt_n_in.
ass.
apply PN2_succ.
ass.
apply union_in.
right.
apply every_set_is_in_unit_set.
take n_lt_is_strictly_lineary_ordered.
left H39.
left H40.
right H41.
assert (S k ∈ N).
apply PN2_succ.
ass.
take H42 k asm (S k) H43 H37.
apply H44.
ass.

assert (k ∈ m0) as k_in_m0.
take H28.
repl H19 in H33.
repl <- H32 in H33.
apply Sm_in_Sn_implies_m_in_Sn in H33.
apply S_el in H33.
disj H33.
ass.
take H28.
repl <- H32 in H33.
repl H19 in H33.
repl H34 in H33.
repl H34 in H30. 
assert (S m0 ∈ N).
apply PN2_succ.
ass.
take no_natural_number_is_member_of_itself (S m0) H35.
apply (H36 H33).
ass.
ass. 
assert (k ∈ n0) as k_in_n0.
assert (k' ∈ n) as H33.
take H21 k' H28.
ass.
repl H16 in H33.
repl <- H32 in H33.
apply Sm_in_Sn_implies_m_in_Sn in H33.
apply S_el in H33.
disj H33.
ass.
take H28.
take H21 k' H33.
repl H16 in H35.
repl <- H32 in H35.
repl H34 in H35.
take PN2_succ n0 H10.
take no_natural_number_is_member_of_itself (S n0) asm.
apply (H37 H35).
ass.
ass.

take H14 k asm.
assert (f⦅t⦅k⦆⦆ = f⦅u⦅k⦆⦆).
repl H31.
eq_refl.
assert (S k ∈ N).
apply PN2_succ.
ass.
take H18 k asm.
take H22 k'.
left H37 R1.
right H38.
apply H39.
repl_in_goal_backward H32.
repl_in_goal H33.
repl_in_goal H36.
ass.
(* case n = m*)
take PN5_induction (fun x0 => x0 ∈ domain t -> x0 ∈ domain u -> t⦅x0⦆ = u⦅x0⦆).
assert ((0 ∈ domain t -> 0 ∈ domain u -> t⦅0⦆ = u⦅0⦆)).
intros.
repl H15.
repl H11.
eq_refl.
assert ((∀x::N. (x ∈ domain t ->
x ∈ domain u -> t⦅x⦆ = u⦅x⦆) ->
S x ∈ domain t ->
S x ∈ domain u -> t⦅S x⦆ = u⦅S x⦆)).
intros.
apply Sm_in_n_implies_m_in_n in H25.
apply Sm_in_n_implies_m_in_n in H26.
take H24 H25 H26.
repl <- H2 in H25.
take H25.
repl H16 in H28.
(* inductive hyp *)
apply union_el in H28.
disj H28.
take H14 x1 H29.
assert (n0 = m0).
apply eq_symm in H19.
repl H20 in H19.
take eq_trans _ _ _ H19 H16.
apply PN4_injection.
ass.
ass.
apply eq_symm.
ass.
take H29.
repl H30 in H31.
take H18 x1 H31.
repl H27 in H28.
apply eq_symm in H32.
take eq_trans _ _ _ H28 H32.
ass.
apply unit_set_el in H29.
(* case x1 = n0 *)
assert (n0 = m0).
apply eq_symm in H19.
repl H20 in H19.
take eq_trans _ _ _ H19 H16.
apply PN4_injection.
ass.
ass.
apply eq_symm in H28.
ass. 
assert (n_step_computation t n0 x X f).
split.
ass.
repl H16.
ass.
assert (n_step_computation u n0 x X f).
split.
ass.
repl_in_goal H28.
ass.
repl <- H28 in H17.
take two_n_step_computations_are_equal (n0) x X X f asm t u H13 asm.
take H32 asm asm.
repl H33.
eq_refl.
repl_in_goal_backward H5.
ass.
repl_in_goal_backward H2.
ass.
take H21 H22 H23.
apply H24.
ass.
ass.
ass.
assert (on (⋃ G) N) as ug_on_n.
(* on (⋃ G) N *)
unfold on.
apply eq_in.
intros.
apply domain_el in H0.
ex_el H0.
apply big_union_el in H0.
ex_el H0.
both H0.
take GP2 s H2.
take H0 (⟨ x0, y ⟩) H1.
apply cartesian_product_el in H3.
left H3.
ass.
intros.
apply (induction_applied x0).
ass.
apply (domain_in _ 0 x).
apply big_union_in.
spawn t ({`⟨0, x⟩}).
ex_in t.
split.
repl H1.
apply every_set_is_in_unit_set.
take H t.
apply_b H2.
split.
apply power_set_in.
intros.
repl H1 in H2.
apply unit_set_el in H2.
repl H2.
apply cartesian_product_in.
apply PN1_empty_set.
ass.
split.
assert (t⦅0⦆ = x).
take appl_prop_on t {`0} 0.
assert (function_on t {`0}).
split.
split.
intros.
repl H1 in H3.
apply element_of_unit_set in H3.
repl H3.
ex_in 0.
ex_in x.
eq_refl.
intros.
both H3.
repl H1 in H4.
repl H1 in H5.
apply element_of_unit_set in H4.
apply element_of_unit_set in H5.
apply eq_symm in H5.
take eq_trans _ _ _ H4 H5.
apply pair_property in H3.
both H3.
ass.
apply eq_in.
intros.
apply domain_el in H3.
ex_el H3.
repl H1 in H3.
apply element_of_unit_set in H3.
apply pair_property in H3.
both H3.
repl H4.
apply every_set_is_in_unit_set.
intros.
apply element_of_unit_set in H3.
repl H3.
apply (domain_in t 0 x).
repl H1.
apply every_set_is_in_unit_set.
take H2 H3. 
assert (0 ∈ {`0}).
apply every_set_is_in_unit_set.
take H4 H5.
ex_el H6.
both H6.
repl H1 in H8.
apply element_of_unit_set in H8.
apply pair_property in H8.
el H8.
repl_in_goal_backward R.
ass.
apply H2.
ex_in 0.
split.
apply PN1_empty_set.
split.
assert (function_on_into t (S 0) X) as t_is_func.
apply function_on_into_in.
repeat split.
intros.
repl H1 in H2.
apply unit_set_el in H2.
ex_in 0.
ex_in x.
ass.
intros.
ex_el H2.
apply S0_in.
repl H1 in H2.
apply unit_set_el in H2.
apply pair_property in H2.
both H2.
ass.
intros.
apply S0_el in H2.
repl_in_goal H2.
repl_in_goal H1.
ex_in x.
apply unit_set_in.
eq_refl.
intros.
both H2.
repl H1 in H3.
repl H1 in H4.
apply unit_set_el in H3, H4.
apply pair_property in H3, H4.
both H3.
both H4.
repl H5.
repl H6.
eq_refl.
intros.
ex_el H2.
repl H1 in H2.
apply unit_set_el in H2.
apply pair_property in H2.
both H2.
repl H4.
ass.
split.
ass.
(assert (0 ∈ S 0)).
apply S0_in.
eq_refl.
take appl_prop t (S 0) X 0 t_is_func H2.
ex_el H3.
both H3.
repl H1 in H5.
apply unit_set_el in H5.
apply pair_property in H5.
both H5.
repl_in_goal_backward H6.
ass.
intro.
intro.
apply any_set_in_empty_set_causes_contradiction in H2.
apply H2.
intro.
intros.
rename x1 into n.
apply domain_el in H2.
ex_el H2.
apply big_union_el in H2.
ex_el H2.
both H2.
rename s into t.
apply domain_in in H3.
assert (domain t ∈ N).
take GP1 t H4.
both H2.
ex_el H6.
both H6.
el H7.
dom L0.
repl_in_goal P.
apply PN2_succ.
ass.
take n_in_m_implies_Sn_in_m_OR_sn_eq_m (domain t) n H2 H3.
(* key disjoint: S n ∈ domain t ∨ S n = domain t *)
disj H5.
apply domain_el in H6.
ex_el H6.
apply (domain_in _ (S n) y0).
apply big_union_in.
ex_in t.
split; ass.
rename H6 into key_H.
apply (domain_in _ (S n) (f⦅t⦅n⦆⦆)).
apply big_union_in.
spawn t' (t ∪ {`⟨ S n, f⦅t⦅n⦆⦆ ⟩}).
rename H5 into TPrime.
take GP1 t H4.
both H5.
rename H6 into t_0.
ex_el H7.
el H7.
assert (n0 = n) as temp.
dom L1.
take eq_trans _ _ _ key_H P.
take PN4_injection n asm n0 asm H5.
apply eq_symm.
ass.
repl temp in L1.
repl temp in R0.
clear L temp n0.

clear R.
rename L1 into t_func.
rename R0 into t_ind.
assert (function_on_into t' (S (S n)) X) as TPrime_is_func.
apply function_on_into_in.
repeat split.
intros.
repl TPrime in H5.
apply union_el in H5.
disj H5.
set_of_pairs t_func.
apply (P x1 H6).
ex_in (S n).
ex_in (f⦅t⦅n⦆⦆).
apply unit_set_el in H6.
ass.
intros.
ex_el H5.
repl TPrime in H5.
apply union_el in H5.
disj H5.
dom t_func.
apply eq_el_1 in P.
take P x1.
apply S_in.
left.
apply H5.
apply domain_in in H6.
ass.
apply unit_set_el in H6.
apply pair_property in H6.
both H6.
repl_in_goal H5.
apply S_in.
right.
eq_refl.
intros.
apply S_el in H5.
disj H5.
repl_in_goal TPrime.
ex_in (t⦅x1⦆).
apply union_in.
left.
appl_2 t x1.
repl_in_goal H7.
ass.
repl_in_goal H6.
ex_in (f⦅t⦅n⦆⦆).
repl TPrime.
apply union_in.
right.
apply unit_set_in.
eq_refl.
intro.
intros.
both H5.
repl TPrime in H6.
repl TPrime in H7.
apply union_el in H6, H7.
disj H6.
disj H7.
fun_prop t_func.
take P x1 x2 z.
apply H7.
split; ass.
apply unit_set_el in H6.
apply pair_property in H6.
both H6.
dom t_func.
take P.
apply eq_el_1 in P.
take P (x1).
apply domain_in in H5.
take H9 H5.
repl H7 in H10.
apply PN2_succ in H1.
take no_natural_number_is_member_of_itself (S n) asm.
apply (H11 H10).
disj H7.
apply unit_set_el in H5.
apply pair_property in H5.
both H5.
apply domain_in in H6.
dom t_func.
apply eq_el_1 in P.
take P x1 H6.
repl H7 in H5.
apply PN2_succ in H1.
take no_natural_number_is_member_of_itself (S n) asm.
apply (H9 H5).
apply unit_set_el in H5, H6.
apply pair_property in H5, H6.
both H5.
both H6.
repl_in_goal H8.
repl_in_goal H9.
eq_refl.
intros.
ex_el H5.
repl TPrime in H5.
apply  union_el in H5.
disj H5.
ran t_func.
apply range_in in H6.
take P x1 H6.
ass.
apply unit_set_el in H6.
apply pair_property in H6.
both H6.
ran F.
take P x1.
apply H6.
assert (n ∈ S n).
apply S_in.
right.
eq_refl.
appl_2 t n.
repl <- H10 in H11.
take H11.
apply range_in in H11.
apply domain_in in H9.
ran t_func.
take P0 (t⦅n⦆) H11.
appl_2 f (t⦅n⦆).
apply range_in in H15.
repl H7.
repl <- H14 in H15.
ass.

ex_in (t').
split.
repl_in_goal TPrime.
apply union_in_2.
apply unit_set_in.
eq_refl.
take H (t ∪ {`⟨ S n, f⦅t⦅n⦆⦆ ⟩}).
repl_in_goal TPrime.
apply_b H5.
repeat split.
apply power_set_in.
intros.
apply union_el in H5.
disj H5.
take GP2 t asm.
take H5 x1 H6.
ass.
apply unit_set_el in H6.
repl H6.
apply cartesian_product_in.
apply PN2_succ.
ass.
take GP1 t H4.
both H5.
ex_el H8.
el H8.
assert (n ∈ S n).
apply S_in.
right.
eq_refl.
assert (function_on_into t (S n) X).
split.
split.
left L1.
both H8.
ass.
unfold on.
apply eq_symm.
apply key_H.
right L1.
ass.
assert (t⦅n⦆ ∈ X).
take appl_prop _ _ _ n H8 H5.
ex_el H9.
both H9.
repl_in_goal H10.
ran H8.
take P y0.
apply H9.
apply (range_in t y0 n).
ass.
take appl_prop _ _ _ (t⦅n⦆) F H9.
ex_el H10.
both H10.
repl_in_goal H11.
ran F.
take P y0.
apply H10.
apply range_in in H12.
ass.
assert ((t ∪ {`⟨ S n, f⦅t⦅n⦆⦆ ⟩})⦅0⦆ = x) as t_prime_at_zero.
assert (0 ∈ S (S n)).
apply S_in.
left.
assert (S n ∈ N).
apply PN2_succ.
ass.
take zero_is_less_than_successor_of_any_nn n H1.
apply H6.
take appl_prop _ _ _ 0 (TPrime_is_func) H5.
ex_el H6.
both H6.
repl_in_goal_backward TPrime.
repl_in_goal H7.
repl TPrime in H8.
apply union_el in H8.
disj H8.
assert (0 ∈ S n).
assert (S n ∈ N).
apply PN2_succ.
ass.
take zero_is_less_than_successor_of_any_nn n H1.
apply H9.
take appl_in_from_pair _ _ _ t_func 0 y0 H8 H6.
repl_in_goal_backward t_0.
repl_in_goal_backward H9.
eq_refl.
apply unit_set_el in H6.
apply pair_property in H6.
both H6.
take zero_eq_Sn_implies_contradiction n.
apply (H6 H8).
(* t_prime_at_zero ends *)
ass.
ex_in (S n).
repl_in_goal_backward TPrime.
split.
apply PN2_succ.
ass.
split.
split.
ass.
assert ((t ∪ {`⟨ S n, f⦅t⦅n⦆⦆ ⟩})⦅0⦆ = x) as t_prime_at_zero.
assert (0 ∈ S (S n)).
apply S_in.
left.
assert (S n ∈ N).
apply PN2_succ.
ass.
take zero_is_less_than_successor_of_any_nn n H1.
apply H6.
take appl_prop _ _ _ 0 (TPrime_is_func) H5.
ex_el H6.
both H6.
repl_in_goal_backward TPrime.
repl_in_goal H7.
repl TPrime in H8.
apply union_el in H8.
disj H8.
assert (0 ∈ S n).
assert (S n ∈ N).
apply PN2_succ.
ass.
take zero_is_less_than_successor_of_any_nn n H1.
apply H9.
take appl_in_from_pair _ _ _ t_func 0 y0 H8 H6.
repl_in_goal_backward t_0.
repl_in_goal_backward H9.
eq_refl.
apply unit_set_el in H6.
apply pair_property in H6.
both H6.
take zero_eq_Sn_implies_contradiction n.
apply (H6 H8).
repl_in_goal TPrime.
ass.
intros.
assert (x1 ∈ S (S n)).
apply S_in.
left.
ass.
appl_2 t' x1.
repl TPrime in H9.
apply union_el in H9.
apply disj_comm in H9.
disj H9.
apply unit_set_el in H7.
apply pair_property in H7.
both H7.
repl H9 in H5.
assert (S n ∈ N).
apply PN2_succ.
ass.
take no_natural_number_is_member_of_itself (S n) asm.
apply (H11 H5).
take appl_in_from_pair  _ _ _ t_func x1 y0 H5 H7.
assert (x1 ∈ N) as x1_in_N.
assert (S n ∈ N).
apply PN2_succ.
ass.
take every_number_inside_nn_is_nn (S n) H10 x1 H5.
ass.
assert (t⦅x1⦆ = t'⦅x1⦆) as t_eq.
repl_in_goal H8.
repl_in_goal H9.
eq_refl.

(* x1 either < n or =  n *)
apply S_el_exclusive in H5.
move H5 at bottom.
disj H5.
both H10.
take t_ind x1 asm.
repl_in_goal_backward t_eq.
repl_in_goal_backward H10.
assert (S x1 ∈ S (S n)).
assert ((S n) ∈ N).
apply PN2_succ.
ass.
take m_in_n_equiv_Sm_in_Sn x1 asm (n) asm.
left H13.
take H14 H5.
apply union_in.
left.
ass.
(*  t'⦅S x1⦆ = t⦅S x1⦆
must be equal in t
*)
assert (S x1 ∈ S n).
apply union_el in H12.
disj H12.
ass.
take m_in_n_equiv_Sm_in_Sn x1 asm (n) asm.
left H12.
apply H14.
ass.
eapply functional_equality_specific.
apply TPrime_is_func.
apply t_func.
apply intersection_in.
ass.
ass.
ex_in (f⦅t⦅x1⦆⦆).
split.
repl TPrime.
apply union_in.
left.
repl_in_goal_backward H10.
appl (t) (S x1).
ass.
repl_in_goal_backward H10.
appl (t) (S x1).
ass.
both H10.
repl_in_goal_backward t_eq.
repl_in_goal H5.
assert (S n ∈ S (S n)).
apply S_in.
right.
eq_refl.
appl_2 t' (S n).
repl_in_goal H13.
repl TPrime in H14.
apply union_el in H14.
disj H14.
apply domain_in in H12.
repl <- key_H in H12.
assert (S n ∈ N).
apply PN2_succ.
ass.
take no_natural_number_is_member_of_itself (S n) asm.
apply (H15 H12).
apply unit_set_el in H12.
apply pair_property in H12.
both H12.
ass.
ass.
ass.
(* into (⋃ G) X *)
assert (into (⋃ G) X) as ug_into.
intros.
apply range_el in H0.
ex_el H0.
apply big_union_el in H0.
ex_el H0.
both H0.
take GP2 s H2.
take H0 (⟨ x1, x0 ⟩) H1.
apply cartesian_product_el in H3.
both H3.
ass.
assert (function_on_into (⋃ G) N X) as ug_function_on_into.
split.
split.
apply union_of_compatible_functions_is_a_function.
ass.
ass.
ass.
ass.
split.
split.
ass.
dom ug_function_on_into.
apply eq_el_2 in P.
take P 0 PN1_empty_set.
apply domain_el in H0.
ex_el H0.
apply big_union_el in H0.
ex_el H0.
both H0.
take GP1 s H2.
left H0.
rename s into t.
take appl_in_from_pair _ _ _ ug_function_on_into 0 x PN1_empty_set.
apply H4.
apply big_union_in.
ex_in t.
split.
take PN1_empty_set.
right H0.
ex_el H6.
el H6.
assert (0 ∈ S n).
assert (S n ∈ N).
apply PN2_succ.
ass.
take zero_is_less_than_successor_of_any_nn (n) asm.
apply H7.
appl t 0.
repl R in H9.
ass.
ass.
(* ∀n::N. (⋃ G)⦅S n⦆ = f⦅(⋃ G)⦅n⦆⦆ *)
intros.
assert ((S x0) ∈ N).
apply PN2_succ.
ass.
appl (⋃ G) (x0).
appl (⋃ G) (S x0).
apply big_union_el in H4.
apply big_union_el in H5.
el H4.
el H5.
rename s into t.
rename s0 into t'.
take GP1 t R.
el H2.
take GP1 t' R0.
el H2.
take L.
apply domain_in in H2.
take L0.
apply domain_in in H3.
dom L4.
dom L7.
repl P in H2.
repl P0 in H3.
take appl_in_from_pair _ _ _ L4 x0 ((⋃ G)⦅x0⦆) H2 L.
take appl_in_from_pair _ _ _ L7 (S x0) ((⋃ G)⦅S x0⦆) H3 L0.
repl_in_goal_backward H4.
repl_in_goal_backward H5.
(* t'⦅S x0⦆ = f⦅t⦅x0⦆⦆ *)
assert ((S n0) ∈ N).
apply PN2_succ.
ass.
take m_in_n_equiv_Sm_in_Sn (x0) asm (n0) asm.
right H7.
take H8 H3.
assert (x0 ∈ S n0).
apply S_in.
left.
ass.
take R3 x0 H9.
repl_in_goal H11.
assert ((t'⦅x0⦆ = t⦅x0⦆) -> f⦅t'⦅x0⦆⦆ = f⦅t⦅x0⦆⦆).
intro. 
repl H12.
eq_refl.
apply H12.
take pairwise_compatible_prop t asm t' asm x0.
apply eq_symm.
apply H13.
repl_in_goal P.
repl_in_goal P0.
apply intersection_in.
ass.
ass.
intros g1 g2 H1 H2.
el H2.
el H1.
take functional_equality _ _ _ _ L1 L0.
apply H0.
intros.
apply (induction_applied x0).
ass.
repl R0.
repl R2.
eq_refl.
intros.
take R x1 asm.
take R1 x1 asm.
repl_in_goal H4.
repl_in_goal H5.
repl_in_goal H3.
eq_refl.
Qed.


Definition S_set_ex: ∃1f. (function_on_into f N N) ∧
 ∀n::N. f⦅n⦆ = S n.
split.
take subset_of_cartesian_short_exists N N 
(fun x => fun y => y = S x).
ex_el H.
both H.
ex_in c.
split.
apply function_on_into_in.
repeat split.
intros.
take H0 x H.
apply cartesian_product_el_2 in H2.
el H2.
ex_in a.
ex_in b.
ass.
intros.
ex_el H.
take H0 (⟨ x, y ⟩) H.
apply cartesian_product_el in H2.
both H2.
ass.
intros.
take H1 x H (S x).
ex_in (S x).
assert (S x ∈ N).
apply PN2_succ.
ass.
take H2 H3.
apply_b H4.
eq_refl.
intros.
both H.
take H0 ⟨ x, y ⟩ H2.
take H0 ⟨ x, z ⟩ H3.
apply cartesian_product_el in H, H4.
both H.
both H4.
take H1 x asm y asm.
left H4 H2.
take H1 x asm z asm.
left H9 H3.
repl H8.
repl H10.
eq_refl.
intros.
ex_el H.
take H0 _ H.
apply cartesian_product_el in H2.
both H2.
ass.
intros.
take H1 x H (S x).
assert (S x ∈ N).
apply PN2_succ.
ass.
take H2 H3.
right H4.
assert ((⟨ x, S x ⟩ ∈ c)).
apply H5.
eq_refl.
apply appl_in_trick.
ass.
intros.
take H0 (⟨ x, x0 ⟩) H7.
apply cartesian_product_el in H8.
both H8.
take H1 x asm x0 asm.
left H8.
apply H11.
ass.
intros a b H1 H2.
both H1.
both H2.
take functional_equality _ _ _ _ H H1.
apply H2.
intros.
take H0 x asm.
take H3 x asm.
repl H5.
repl H6.
eq_refl.
Qed.

Definition S_set := ι _ S_set_ex.

Definition S_set_func: function_on_into S_set N N.
extract_iota_from_goal S_set.
left iota_prop.
ass.
Qed.

Ltac set_el H :=
let H2:= fresh "H2" in
let H3:= fresh "H3" in
match type of H with
| ?A ∈ ?B => 
  lazymatch goal with
  | H3 : (∀x. x ∈ B ⇔ _) |- _ => 
  (pose proof H3 A as H2; left H2 H; clear H2)
  | _ => fail "Unable to find (∀x. x ∈ B ⇔ _) in context"
  end
| _ => fail "H type not matched with ?A ∈ ?B"
end.

Definition S_set_el_appl(x: Set) (x_in_N: x ∈ N): S_set⦅x⦆ = S x.
extract_iota_from_goal (S_set).
both iota_prop.
take H0 x asm.
ass.
Qed.


Definition plus_set_ex: ∃1plus_set. 
function_on_into plus_set (N×N) N ∧
∀m::N. ∀n::N. plus_set⦅m,0⦆ = m ∧ (plus_set⦅m,(S n)⦆ = (S (plus_set⦅m,n⦆))).
Proof.
subset ((N×N)×N) (fun triple => ∃m::N. ∃n::N. ∃p::N. triple = ⟨m,n,p⟩∧
∃fm. function_on_into fm N N ∧ fm⦅0⦆ = m ∧ (∀k::N. (fm⦅(S k)⦆ = S_set⦅fm⦅k⦆⦆)) ∧ fm⦅n⦆ = p).
rename b into op.
split.
assert (function_on_into op (N × N) N) as op_func.
apply function_on_into_in.
repeat split.
intros.
take H x.
left H1 H0.
left H2.
apply cartesian_product_el_2 in H3.
el H3.
ex_in a.
ex_in b.
ass.
intros.
ex_el H0.
take H ⟨ x, y ⟩.
left H1 H0.
left H2.
apply cartesian_product_el_2 in H3.
el H3.
apply pair_property in L0.
both L0.
repl H3.
ass.
intros.
apply cartesian_product_el_2 in H0.
el H0.
repl L0.
rename a into m.
rename b into n.
take recursion_theorem S_set m N R0 S_set_func.
ex_el H0.
el H0.
rename g into fm.
ex_in (fm⦅n⦆).
take H (⟨ ⟨ m, n ⟩, fm⦅n⦆ ⟩).
apply_b H0.
repeat split.
apply cartesian_product_in.
apply cartesian_product_in.
ass.
ass.
take appl_in_range _ _ _ L1 n R.
ass.
ex_in m.
split.
ass.
ex_in n.
split.
ass.
ex_in (fm⦅n⦆).
split.
take appl_in_range _ _ _ L1 n asm.
ass.
split.
eq_refl.
ex_in fm.
split.
split.
split.
ass.
ass.
ass.
eq_refl.
intros x y z H2.
both H2.
take H ⟨ x, y ⟩.
left H2 H0.
take H ⟨ x, z ⟩.
left H4 H1.
el H3.
el H5.
assert (n = n0) as n_eq_n0.
apply pair_property in L9.
apply pair_property in L3.
el L3.
el L9.
repl L11 in L3.
apply pair_property in L3.
el L3.
ass.
assert (m = m0) as m_eq_m0.
apply pair_property in L9.
apply pair_property in L3.
el L3.
el L9.
repl L11 in L3.
apply pair_property in L3.
el L3.
ass.
assert (fm = fm0).
take recursion_theorem S_set m N L0 S_set_func.
right H3.
apply H5.
split.
split.
ass.
ass.
ass.
split.
split.
ass.
repl_in_goal m_eq_m0.
ass.
ass.
apply pair_property in L3.
right L3.
apply pair_property in L9.
right L9.
repl H5.
repl H6.
repl_in_goal_backward R3.
repl_in_goal_backward R0.
repl_in_goal H3.
repl_in_goal n_eq_n0.
eq_refl.
intros.
ex_el H0.
take H ⟨ x0, x ⟩.
left H1 H0.
el H2.
apply cartesian_product_el in L.
both L.
ass.
ex_in op.
split.
ass.
intros.
split.
assert (⟨x,0⟩ ∈ N × N).
apply cartesian_product_in.
ass.
apply PN1_empty_set.
appl op ⟨x,0⟩.
set_el H5.
el H4.
apply pair_property in L3.
both L3.
repl_in_goal H4.
repl_in_goal_backward R0.
apply pair_property in H3.
both H3.
repl_in_goal H6.
repl_in_goal_backward R1.
repl_in_goal H7.
eq_refl.
assert (⟨x, S n⟩ ∈ (N × N)).
apply cartesian_product_in.
ass.
apply PN2_succ.
ass.
assert (⟨x, n⟩ ∈ (N × N)).
apply cartesian_product_in.
ass.
ass.
appl op ⟨ x, S n ⟩.
appl op ⟨ x, n ⟩.
set_el H6.
el H5.
set_el H7.
el H5.
assert (m = m0) as m_eq_m0.
apply pair_property in L9.
apply pair_property in L3.
el L3.
el L9.
apply pair_property in L11.
apply pair_property in L3.
both L11.
both L3.
repl_in_goal_backward H4.
repl_in_goal_backward H8.
eq_refl.
assert (fm = fm0).
take recursion_theorem S_set m N L0 S_set_func.
right H4.
apply H5.
split.
split.
ass.
ass.
ass.
split.
split.
ass.
repl_in_goal m_eq_m0.
ass.
ass.
apply pair_property in L3.
both L3.
apply pair_property in L9.
both L9.
repl_in_goal H8.
repl_in_goal H10.
repl_in_goal_backward R3.
repl_in_goal_backward R0.
repl_in_goal_backward H4.
take R n asm.
assert (n0 = S n).
apply pair_property in H5.
both H5.
apply eq_symm.
ass.
repl H12.
assert (n1 = n).
apply pair_property in H9.
both H9.
apply eq_symm.
ass.
repl_in_goal H13.
take appl_in_range _ _ _ L4 x asm.
take S_set_func.
appl S_set (fm⦅x⦆).
take appl_in_range _ _ _ L4 n asm.
take S_set_el_appl (fm⦅n⦆) asm.
repl H17 in H11.
ass.
intros f g H1 H2.
el H1.
el H2.
take functional_equality f g (N × N) N asm asm.
apply H0.
intros.
apply cartesian_product_el_2 in H1.
ex_el H1.
ex_el H1.
el H1.
rename a into m.
rename b into n.
repl_in_goal L2.
take R m asm n asm.
take R0 m asm n asm.
el H1.
el H2.
apply (induction_applied n).
ass.
repl_in_goal L1.
repl_in_goal L3.
eq_refl.
intros.
take R m asm x0 asm.
take R0 m asm x0 asm.
el H3.
el H4.
repl_in_goal R5.
repl_in_goal R6.
repl_in_goal H2.
eq_refl.
Qed.




