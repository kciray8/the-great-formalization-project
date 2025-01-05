From Rob Require Import NaturalDeduction.
Require Import Ltac.

Definition eq (S: Set) (x y: S) : Prop := forall P: (S -> Prop), (P x ⇔ P y).
Notation "A = B" := (eq _ A B)(at level 51, right associativity).

Definition eq_refl (S: Set)(x: S) : x = x.
intro.
unfold biimpl.
assert (P x ⇒ P x).
intro.
exact H.
exact (biimpl_in _ _ H H).
Defined.

Definition eq_subs (S: Set)(P: (S -> Prop)) (x y: S) (u: x = y) (v: P x) : P y.
pose proof u P.
pose proof biimpl_el_1 _ _ H.
apply H0.
exact v.
Defined.

Definition eq_cong (S T: Set)(f: (S -> T)) (x y: S) (u: x = y) : (f x) = (f y).
pose proof eq_subs S (fun z: S => f x = f z) x y.
cbv beta in H.
apply H.
exact u.
exact (eq_refl T (f x)).
Defined.

Definition refl (S: Set) (R: S -> S -> Prop) : Prop := ∀x : S . (R x x).

Definition trans (S: Set) (R: S -> S -> Prop) : Prop := 
∀x : S . ∀y : S . ∀z : S . ((R x y) ⇒ (R y z) ⇒ (R x z)).

Definition pre_ord (S: Set) (R: S -> S -> Prop) := (refl S R) ∧ (trans S R).

Definition symm (S: Set) (R: S -> S -> Prop) :=
 ∀x : S . ∀y : S . ((R x y) ⇒ (R y x)).

Definition antisymm (S: Set) (R: S -> S -> Prop) :=
 ∀x : S . ∀y : S . ((R x y) ⇒ (R y x) ⇒ (x = y)).

Definition part_ord (S: Set) (R: S -> S -> Prop) := (pre_ord S R) ∧ (antisymm S R).


Definition eq_symm (S: Set) : ∀x:S . ∀y : S . ((x = y) ⇒ (y = x)).
intro.
intro y.
intro.
intro.
pose proof H P.
pose proof biimpl_el_1 _ _ H0.
pose proof biimpl_el_2 _ _ H0.
pose proof biimpl_in _ _ H2 H1.
exact H3.
Defined.
 

Definition eq_trans (S: Set) 
: ∀x:S . ∀y : S . ∀z : S . ((x = y) ⇒ (y = z) ⇒ (x = z)).
intro x.
intro y.
intro z.
intro.
intro.
pose proof eq_subs S (fun w => x = w) y z.
cbv beta in H1.
apply H1.
exact H0.
exact H.
Defined.

Definition Least (S: Set) (R: S -> S -> Prop) (m : S) := ∀n : S . (R m n).
  
Definition ex_more (S: Set) (P: S -> Prop) := ex S P.

Notation "'∃≥1' x . p" := (ex_more _ (fun x => p))
  (at level 200, x binder, right associativity,
   format "'[' '∃≥1' '/ ' x . '/ ' p ']'").

Definition ex_less (S: Set) (P: S -> Prop) := 
∀y: S. ∀z: S . (P y ⇒ P z ⇒ (y = z)).

Notation "'∃≤1' x . p" := (ex_less _ (fun x => p))
  (at level 200, x binder, right associativity,
   format "'[' '∃≤1' '/ ' x . '/ ' p ']'").

Definition ex_unique (S: Set) (P: S -> Prop) := (∃≥1 x:S. P x) ∧ (∃≤1 x:S. P x).

Notation "'∃1' x . p" := (ex_unique _ (fun x => p))
  (at level 200, x binder, right associativity,
   format "'[' '∃1' '/ ' x . '/ ' p ']'").

(* 
Definition 12.1.1 Let S be a set and ≤ a binary relation on S.
Then m ∈ S is a least element of S with respect to ≤ if ∀n∈S(m ≤ n).

Lemma 12.1.2 Let S be a set, partially ordered by ≤. Assume that
S has a least element with respect to ≤. Then this least element is
unique.
*)

Definition lemma_12_1_2 (S: Set) (R: S -> S -> Prop) 
(u: part_ord S R) : (∃ l:S. Least S R l) -> (∃1 l:S. Least S R l).
intro.
unfold ex_unique.
unfold ex_more.
refine (conj_in _ _ H _).
unfold ex_less.
intro x.
intro y.
intro.
intro.
unfold Least in H0.
unfold Least in H1.
pose proof H0 y.
pose proof H1 x.
cbv beta in H2, H3.
unfold part_ord in u.
pose proof conj_el_2 _ _ u.
unfold antisymm  in H4.
pose proof H4 x y.
cbv beta in H5.
apply H5.
exact H2.
exact H3.
Defined.

Axiom ι: forall (S: Set) (P: S -> Prop) (u: (∃1 x:S. P x)), S.

Axiom ι_prop: forall (S: Set) (P: S -> Prop) (u: (∃1 x:S. P x)), P ((ι S P u)).

(* Lemma 12.7.1 Let S be a set, P a predicate on S and assume
∃1x∈S(P(x)). Then ∀z∈S(P(z) ⇒ (z =S ιx∈S(P(x)))). *)

Definition lemma_12_7_1 (S: Set) (P: S -> Prop) (u: ∃1x:S. (P(x))): 
∀z:S. (P(z) ⇒ ((z = (ι S P u)))).
intro.
intro.
unfold ex_unique in u.
pose proof conj_el_2 _ _ u.
unfold ex_less in H0.
pose proof H0 x (ι S P u).
cbv beta in H1.
apply H1.
exact H.
pose proof ι_prop S P u.
exact H2.
Defined.

Definition Min (S: Set) (R: S -> S -> Prop) (r: part_ord S R) 
(w : ∃≥1 x : S. (Least S R x)): S.
pose proof lemma_12_1_2 S R r w.
pose proof ι S (fun l => Least S R l) H.
exact H0.
Defined.

Definition Min_Prop (S: Set) (R: S -> S -> Prop) 
(r: part_ord S R) (w : ∃≥1 x : S. (Least S R x))
: (∀x : S . ((Least S R x)) ⇒ (x = (Min S R r w))).
intro.
intro.
unfold Min.
cbv beta.
unfold part_ord in r.
pose proof lemma_12_7_1 S ((fun l : S => Least S R l)).
cbv beta in H0.
pose proof H0 (lemma_12_1_2 S R r w) x.
cbv beta in H1.
apply H1.
exact H.
Defined.

Definition biimpl_symm (A B: Prop): (A ⇔ B) ⇒ (B ⇔ A).
intro.
unfold biimpl.
unfold biimpl in H.
pose proof conj_el_1 _ _ H.
pose proof conj_el_2 _ _ H.
exact (conj_in _ _ H1 H0).
Defined.

Definition exercise_12_1 (S: Set) : ∀x:S . ∀y : S . ((x = y) ⇒ (y = x)).
intro x.
intro y.
intro.
intro.
pose proof H P.
exact (biimpl_symm _ _ H0).
Defined.

Definition eq_alt (S: Set) (x y: S) : Prop := forall P: (S -> Prop), (P x -> P y).

Definition subs_prop (S: Set) (R: S -> S -> Prop) : Prop 
:= forall (P: S -> Prop) (x y: S) (u: R x y) (v: P x), P y.

Definition eq_statisfies_subs_prop: forall S: Set, subs_prop S (eq S).
intro.
intro.
exact (eq_subs S P).
Defined.

Definition exercise_12_2_a (S: Set) : refl S (eq_alt S).
intro.
intro.
intro.
exact H.
Defined.

Definition exercise_12_2_b (S: Set) : symm S (eq_alt S).
intro x.
intro y.
intro.
pose proof H (fun z => eq_alt S z x).
cbv beta in H0.
apply H0.
pose proof exercise_12_2_a S.
unfold refl in H1.
exact (H1 x).
Defined.

Definition exercise_12_2_c (S: Set) : trans S (eq_alt S).
intro x.
intro y.
intro z.
intro.
intro.
pose proof H0 (fun k => eq_alt S x k).
cbv beta in H1.
apply H1.
exact H.
Defined.

Definition exercise_12_2_d:  forall S: Set, subs_prop S (eq_alt S).
intro.
intro.
intro x.
intro y.
intro.
pose proof u P.
exact H.
Defined.

(* 12.3 
(a) Check that line (3) of Figure 12.10 and line (2) of Figure 12.12 satisfy
the derivation rules of λD. --> Proved in eq_symm and eq_trans
(b) The same question for lines (1) and (2) of Figure 12.18.
--> Proved in Min and Min_Prop
 *)

Module exercise_12_4.
Parameter S: Set.
Parameter le: S -> S -> Prop.
Parameter ordered: part_ord S le.
Notation "A ≤ B" := (le A B)(at level 52, left associativity).

(* 12.4 (a) *)
Definition lt (m n: S):= (m ≤ n) ∧ (¬(m = n)).
Notation "A < B" := (lt A B)(at level 52, left associativity).

Ltac left x := pose proof conj_el_1 _ _ x.
Ltac right x := pose proof conj_el_2 _ _ x.

Ltac conj_el x:= left x; right x.

Definition exercise_12_4_b: ∀m:S. (¬(m<m)).
intro.
intro.
unfold lt in H.
conj_el H.
pose proof ordered.
unfold part_ord in H2.
right H2.
pose proof H3 x x H0 H0.
apply (H1 H4).
Defined.

Definition exercise_12_4_c: ∀m:S. ∀n:S. (¬((m < n) ∧ (n < m))).
pose proof ordered.
unfold part_ord in H.
right H.
unfold antisymm  in H0.
intro x.
intro y.
intro.
conj_el H1.
conj_el H2.
conj_el H3.
pose proof H0 x y H4 H6.
exact (H5 H8).
Defined.

Definition exercise_12_4_d: trans S lt.
unfold trans.
intro x.
intro y.
intro z.
intro.
intro.
conj_el H.
conj_el H0.
unfold lt.
eapply (conj_in _ _ _).
intro.
pose proof eq_subs S (fun k => k ≤ y) x z H5 H1.
cbv beta in H6.
apply H4.
pose proof ordered.
unfold part_ord in H7.
right H7.
unfold antisymm in H8.
pose proof H8 y z H3 H6.
exact H9.
Unshelve.
pose proof ordered.
unfold part_ord in H5.
left H5.
unfold pre_ord in H6.
right H6.
pose proof H7 x y z H1 H3.
exact H8.
Defined.

Definition exercise_12_5_a (S: Set) (P: S -> Prop) 
(n: S) (u: (P n)) (v: (∀x:S. (P(x) ⇒ (x = n))))
: ∃1 x:S. (P(x)).
unfold ex_unique.
pose proof (ex_in S P n u):∃≥1 x. P x.
refine (conj_in _ _ H _).
unfold ex_less.
intro y.
intro z.
intro.
intro.
pose proof v y H0.
pose proof v z H1.
pose proof eq_symm S z n H3.
exact (eq_trans S y n z H2 H4).
Defined.

Definition exercise_12_5_b (S: Set) (P: S -> Prop) (n: S) 
(u: (P n)) (v: (∀x:S. (P(x) ⇒ (x = n)))) (w: ∃1 x:S. (P(x)))
: n = (ι S P w).
pose proof lemma_12_7_1 S P w n.
cbv beta in H.
apply H.
exact u.
Defined.


Module exercise_12_6.
Parameter S: Set.
Parameter le: S -> S -> Prop.
Parameter ordered: part_ord S le.

Definition minimal (m:S) := ∀x:S. ((le x m) ⇒ x = m).

Definition exercise_12_6_b (m: S): (Least S le m) -> minimal m.
intro.
intro x.
intro.
unfold Least in H.
pose proof H x.
cbv in H1.
pose proof ordered.
right H2.
pose proof H3 x m H0 H1.
exact H4.
Defined.

Definition exercise_12_6_c (m: S): (Least S le m) -> (forall k: S, (minimal k) -> m = k).
intro.
intro.
intro.
pose proof H0 m.
cbv beta in H1.
apply H1.
unfold Least in H.
apply (H k).
Defined.

Definition exercise_12_6_c' (m: S): (Least S le m) -> 
forall (w: ∃1 x:S. minimal x), (m = (ι S (fun g => minimal g) w)).
intro.
intro.
pose proof exercise_12_5_b S (fun g : S => minimal g) m (exercise_12_6_b m H).
cbv beta in H0.
apply H0.
clear H0.
intro.
right w.
unfold ex_less in H0.
pose proof H0 x m.
cbv beta in H1.
pose proof exercise_12_6_b m H.
intro.
exact (H1 H3 H2).
Defined.

End exercise_12_6.

Definition associative_closed (S: Set) (R: S -> S -> S) :=
 ∀x : S . ∀y : S . ∀z : S . ((R (R x y) z) = (R x (R y z))).

Definition monoid (S: Set) (op: S -> S -> S) := associative_closed S op.

Definition has_unit (S: Set) (op: S -> S -> S) := ∃e:S. ∀x:S. (op e x) = x ∧ (op x e) = x.

Definition unit (S: Set) (op: S -> S -> S) (e: S) := ∀x:S. ((op e x) = x ∧ (op x e) = x).

Definition exercise_12_7_b (S: Set) (op: S -> S -> S) (M: monoid S op):
(∃e:S. (unit S op e)) ⇒ (∃1 e:S. (unit S op e)).
unfold monoid in M.
unfold associative_closed  in M.
intro.
refine (conj_in _ _ H _).
intro x.
intro y.
intro unitx.
intro unity.
unfold unit in unitx.
unfold unit in unity.
pose proof unitx x.
cbv beta in H0.
pose proof unity y.
cbv beta in H1.
pose proof unitx y.
cbv beta in H2.
pose proof unity x.
cbv beta in H3.
left H3.
pose proof eq_symm S (op y x) x H4.
right H2.
pose proof eq_trans S x (op y x) y H5 H6.
exact H7.
Defined.

Definition inverse (S: Set) (op: S -> S -> S) (x: S) (y: S) (e: S):= 
((op x y)) = e ∧ ((op y x) = e). (* exercise_12_7_d *)

Definition exercise_12_7_c (S: Set) (op: S -> S -> S) (M: monoid S op) 
(e: S) (e_is_unit: unit S op e):
(∀x:S. ∃y:S. (inverse S op x y e)) -> (∀x:S. ∃1 y:S. (inverse S op x y e)).
intro each_x_has_inverse_y.
intro.
unfold ex_unique.
refine (conj_in _ _ (each_x_has_inverse_y x) _).
refine (_:∃≤1 y. inverse S op x y e).
unfold ex_less.
intro y.
intro z.
intro y_inverse_for_x.
intro z_inverse_for_x.
unfold inverse in y_inverse_for_x.
unfold inverse in z_inverse_for_x.
unfold inverse in each_x_has_inverse_y.
unfold monoid in M.
unfold associative_closed in M.
unfold unit in e_is_unit.
pose proof e_is_unit y.
cbv beta in H.
right H.
pose proof eq_symm S (op y e) y H0.
left z_inverse_for_x.
pose proof eq_symm S (op x z) e H2.
pose proof eq_subs S (fun e => y = op y e) e (op x z) H3 H1.
cbv beta in H4.
pose proof M y x z.
cbv beta in H5.
pose proof eq_symm S (op (op y x) z) (op y (op x z)) H5.
pose proof eq_subs S (fun R => y = R) (op y (op x z)) (op (op y x) z) H6 H4.
cbv beta in H7.
right y_inverse_for_x.
pose proof eq_subs S (fun R => y = op (R) z) (op y x) (e) H8 H7.
cbv beta in H9.
pose proof e_is_unit z.
left H10.
pose proof eq_trans S y (op e z) z H9 H11.
exact H12.
Defined.

Definition exercise_12_8 (S: Set) (R: S -> S -> Prop) 
(r: part_ord S R) (w : ∃≥1 x : S. (Least S R x))
: (∀x : S . (x = (Min S R r w)) ⇒ ((Least S R x))).
intro.
intro.
intro y.
unfold Min in H.
unfold Least in w.
unfold ex_more in w.
unfold ex in w.
pose proof w (R x y).
apply H0.
intro z.
intro.
pose proof H1 y.
cbv beta in H2.
pose proof H1: (Least S R z).
pose proof lemma_12_7_1 S (fun l : S => Least S R l) (lemma_12_1_2 S R r w) z.
cbv beta in H4.
pose proof H4 H3.
pose proof eq_symm S _ _ H5.
pose proof eq_trans S _ _ _ H H6.
pose proof eq_symm S _ _ H7.
pose proof eq_subs S (fun q => R q y) z x H8 H2.
exact H9.
Defined.

Module exercise_12_9.
Parameter R: Set.
Parameter O: R.
Parameter sub: R -> R -> R.
Parameter add: R -> R -> R.
Parameter half: R -> R.

Notation "x - y" := (sub x y)(at level 51, right associativity).
Notation "x + y" := (add x y)(at level 51, right associativity).

Parameter gt: R -> R -> Prop.
Parameter ge: R -> R -> Prop.
Parameter lt: R -> R -> Prop.

Notation "x > y" := (gt x y)(at level 51, right associativity).
Notation "x ≥ y" := (ge x y)(at level 51, right associativity).
Notation "x < y" := (lt x y).

Parameter abs: R -> R.

Axiom abs_is_positive: forall r:R, (abs r) ≥ O.
Axiom half_of_positive_is_positive: forall r:R, (r ≥ O) -> (half r) ≥ O.
Axiom unequality_entails_not_equal_to_zero: 
forall a b:R, (¬ (a = b)) -> ¬((half (abs (a-b)) = O)).
Axiom le_intro: 
forall a b:R, ((a ≥ b) ∧ (¬ (a = b))) -> (a > b).

Axiom impossible: 
forall a b:R, (a ≥ b) -> (a < b) -> ⊥.

Notation " | x | " := (abs x).

Parameter N: Set.
Parameter gt_N: N -> N -> Prop.

Notation "x >N y" := (gt_N x y)(at level 51, right associativity).

Axiom always_ex_gt: forall (a b:N), ∃K:N. (K >N a) ∧ (K >N b).

Definition limit (f : N -> R) (l: R) := 
∀ε:R. (ε>O) -> ∃K:N. ∀n:N. (n >N K) -> ((abs ((f n) - l)) < ε).

Axiom triangle_inequality: ∀x:R. ∀y:R. ∀z:R. 
(((abs (x - y)) + (abs (x - z))) ≥ (abs (y - z))).

Axiom sum_of_inequalities: forall (x y a b:R), 
(x < y) -> (a < b) -> ((x + a) < (y + b)).

Axiom sum_of_halvs: forall (x:R), 
((half x) + (half x)) = x.

Definition exercise_12_9 (f : N -> R):
(∃ l:R. (limit f l)) -> (∃1 l:R. (limit f l)).
intro.
unfold ex_unique.
refine (conj_in _ _ H _).
intro l1.
intro l2.
intro a.
intro b.
pose proof DN_el (l1 = l2).
apply H0.
clear H0.
intro.
unfold limit in a, b.
pose proof a (half (abs (l1 - l2))).
cbv beta in H1.
pose proof b (half (abs (l1 - l2))).
cbv beta in H2.
pose proof abs_is_positive (l1 - l2).
pose proof half_of_positive_is_positive (abs (l1 - l2)) H3.
pose proof unequality_entails_not_equal_to_zero l1 l2 H0.
pose proof conj_in _ _ H4 H5.
pose proof le_intro (half (abs (l1 - l2))) 
(O) H6.
pose proof H1 H7 as a'.
pose proof H2 H7 as b'.
pose proof ex_el N _ a' ⊥.
cbv beta in H8.
apply H8.
intro K1.
intro a''.
pose proof ex_el N _ b' ⊥.
cbv beta in H9.
apply H9.
intro K2.
intro b''.
pose proof always_ex_gt K1 K2.
pose proof ex_el N _ H10 ⊥.
apply H11.
intro K.
intro cond.
conj_el cond.
pose proof a'' K H12.
pose proof b'' K H13.
pose proof triangle_inequality (f K) l1 l2.
cbv beta in H16.
pose proof sum_of_inequalities _ _ _ _ H14 H15.
pose proof sum_of_halvs (abs (l1 - l2)). 
pose proof eq_subs _ 
(fun k => abs (f K - l1) + abs (f K - l2) < k) _ _ H18 H17.
cbv beta in H19.
pose proof triangle_inequality (f K) l1 l2.
cbv beta in H20.
pose proof impossible _ _ H20 H19.
apply H21.
Defined.

End exercise_12_9.