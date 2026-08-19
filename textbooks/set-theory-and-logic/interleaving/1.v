(* August 11, 2026 - August 13, 2026 *)


Definition PN3_not_zero: ∀n. (n ∈ N) -> ¬((S n) = 0).
intro.
intro.
intro.
apply extension_backwards in H0.
take H0 x.
left H1.
apply (@any_set_in_empty_set_causes_contradiction x).
apply H2.
apply S_in.
right.
apply eq_refl.
Qed.

Definition PN5_induction: forall (P: Set->Prop), 
(P 0) -> (∀x :: N. P x -> (P (S x))) ->  (∀x :: N. P x).
intros.
intro.
intro.
take n_properties.
both H2.
take ZF2_subsets P N.
ex_el H2.
take H2 x.
rename H2 into ii.
assert ((b = N) -> P x).
intro.
repl H2 in H5.
left H5.
take H6 H1.
both H7.
ass.
apply H2.
take H4 b.
apply extensionality_for_subsets.
intro.
intro.
take ii x0.
left H8 H7.
both H9.
ass.
apply H6.
split.
take ii ∅.
apply_b H7.
split.
both H3.
ass.
apply H.
both H3.
intro.
intro.
take ii x0.
left H9 H3.
both H10.
take H8 x0 H11.
take ii (S x0).
apply_b H13.
split.
ass.
take H0 x0.
apply H13.
ass.
ass.
Qed.


Definition every_set_is_in_unit_set: ∀m. m ∈ {`m}.
intro.
apply unit_set_in.
apply eq_refl.
Qed.

Definition PN2_succ: ∀n. (n ∈ N) -> ((S n) ∈ N).
intro.
intro.
take n_properties.
both H0.
right H1.
take H0 x H.
ass.
Qed.