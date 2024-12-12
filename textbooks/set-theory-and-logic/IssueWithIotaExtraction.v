Require Import Ltac.
From BASE Require Import MathLogic.
From BASE Require Import Chap7_InformalAxiomaticSetTheory.


Ltac extract_iota_from_goal' obj :=
let uniqueness_proof := fresh "uniqueness_proof" in
let s := fresh "s" in
let prop := fresh "iota_prop" in
let eq_to_iota := fresh "eq_to_iota" in
let eq_to_iota_backwards := fresh "eq_to_iota_backwards" in
let replaced_H := fresh "replaced_H" in
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
| |- ?a ?B => idtac a; apply(eq_subs a _ _ eq_to_iota);
clear eq_to_iota;
clear eq_to_iota_backwards
end
| _ => idtac "error inside nested match"
end
| _ => idtac "error inside outer match"
end.

Ltac extract_iota' obj H :=
let uniqueness_proof := fresh in
let s := fresh "s" in
let iota_prop := fresh "iota_prop" in
let eq_to_iota := fresh "eq_to_iota" in
let eq_to_iota_backwards := fresh "eq_to_iota_backwards" in
let replaced_H := fresh "replaced_H" in
let h_expanded := fresh "h_expanded" in
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
clear eq_to_iota;
clear eq_to_iota_backwards;
clear h_expanded;
move iota_prop before H
end
| _ => idtac "error inside nested match"
end
| _ => idtac "error inside outer match"
end.

Definition test2(a b: Set): (∅ ∈ a)  ->  (a ∈ ∅) -> (a ∈ ∅) .
intros.
extract_iota' ∅ H.
extract_iota' ∅ H0.


Definition test(a b: Set): (∅ ∈ a) ∧  (a ∈ ∅).
apply (conj_in _ _).
(*Unset Printing Notations.*)


2:{
extract_iota_from_goal ∅.
}

