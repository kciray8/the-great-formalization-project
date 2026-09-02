(* started on Sep 1, 2026 *)
Require Import Ltac.
From BASE Require Export Sets2.

Definition initial_segment_below (n: Set) := n.

Notation "[ 0 , n ]" := (initial_segment_below (S n)). (* seems perfect *)
Notation "[ 0 , n - 1 ]" := (initial_segment_below n).

Definition seq(s n A: Set) := 
(function_on_into s (initial_segment_below n) A).

Definition gt_n(x y: Set) := ⟨y,x⟩ ∈ <.

Notation "a > b" := (gt_n a b)(at level 70):natural_numbers.

Definition ge_n (a b: Set) := (a > b) ∨ (a = b).

Notation "a ≥ b" := (ge_n a b)(at level 70):natural_numbers.

Definition path_of_len(v k u u' V E: Set) := 
seq v (S k) V ∧ v⦅0⦆ = u ∧ v⦅k⦆ = u' ∧
∀i. (i ≥ 0 ∧ i < k) -> ⟨v⦅i⦆, v⦅S i⦆⟩ ∈ E.

Definition path(p u v V E: Set) := ∃k. (path_of_len p k u v V E).

Definition simple_path(p u v V E: Set) := (path p u v V E) ∧ 
(∀i::domain(p). ∀j::domain(p). p⦅i⦆ = p⦅j⦆ -> i = j).

Definition path_from_u_to_v_exists(u v V E: Set) := (∃p. path p u v V E).
Definition simple_path_from_u_to_v_exists(u v V E: Set) := (∃sp. simple_path sp u v V E).

(* CLRS B.4-2 *)
(* Show that if an undirected graph contains a path between two vertices
u and v, then it contains a simple path between u and v. *)
Definition path_implies_simple_path(V E u v: Set): 
path_from_u_to_v_exists u v V E -> simple_path_from_u_to_v_exists u v V E.
intros.
unfold path_from_u_to_v_exists in H.
ex_el H.
unfold simple_path_from_u_to_v_exists.
unfold path in H.
ex_el H.
generalize dependent k.


