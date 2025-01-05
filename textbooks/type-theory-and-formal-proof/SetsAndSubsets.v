Require Import Ltac.
From Rob Require Import NaturalDeduction.
From Rob Require Import MathematicsFirstAttempt.

Definition ps(S: Set) := (S -> Prop): Type.

Definition element (S: Set) (x:S) (V: (ps S)) := (V x): Prop.
Notation "x ∈ V" := (element _ x V)(at level 52, left associativity).

Definition subset (S: Set) (V: (ps S)) (W: (ps S)) := ∀x : S . ((x ∈ V) ⇒ (x ∈ W)) : Prop.
Notation "V ⊆ W" := (subset _ V W)(at level 52, left associativity).

Definition union (S: Set) (V: (ps S)) (W: (ps S)) := (fun x : S => (x ∈ V ∨ x ∈ W)) : ps(S).
Notation "V ∪ W" := (union _ V W)(at level 52, left associativity).

Notation "{ x | P }" := (fun x : _ => P)
(at level 52, x binder, left associativity).

Notation "{ x : A | P }" := (fun x : A => P)
(at level 52, x binder, left associativity).

Definition IS (S: Set) (V: (ps S)) (W: (ps S)) := (V ⊆ W ∧ W ⊆ V ) : Prop.
Notation "V == W" := (IS _ V W)(at level 70, left associativity).

Definition intersection (S: Set) (V: (ps S)) (W: (ps S)) := (fun x : S => (x ∈ V ∧ x ∈ W)) : ps(S).
Notation "V ∩ W" := (intersection _ V W)(at level 52, left associativity).

Definition difference (S: Set) (V: (ps S)) (W: (ps S)) := (fun x : S => (x ∈ V ∧ ¬(x ∈ W))) : ps(S).
Notation "V \ W" := (difference _ V W)(at level 52, left associativity).

Definition complement (S: Set) (V: (ps S)) := {x : S | ¬(x ∈ V )} : ps(S).
Notation "V ꟲ" := (complement _ V)(at level 10, left associativity).

Definition element_in (S: Set) (P: (ps S)) (y: S) (u: P y) 
:= u : (y ∈ { x : S | P x }).
Notation "∈_in V W" := (element_in _ V W)(at level 52, left associativity).

Definition element_el (S: Set) (P: (ps S)) (y: S) (v : (y ∈ {x : S |P x})) 
:= v : P y.
Notation "∈_el V W" := (element_el _ V W)(at level 52, left associativity).


Definition figure_13_4 (S : Set) (V : ps(S)) (W : ps(S)) : (V ⊆ (Wꟲ)) ⇒ (V\W == V ).
intro.
unfold IS.
apply (conj_in _ _).
unfold subset.
intro.
intro.
unfold difference in H0.
pose proof element_el _ _ x H0.
cbv beta in H1.
left H1.
exact H2.
intro.
intro.
eapply (element_in _ _ x _).
Unshelve.
unfold difference.
apply (conj_in _ _).
apply H0.
unfold subset in H.
pose proof H x H0.
apply H1.
Defined.

Definition eq_subset (S: Set) (V: (ps S)) (W: (ps S)) 
:= forall K : ps(S) -> Prop, (K V ⇔ K W) : Prop.

Notation "V ⩮ W" := (eq_subset _ V W)(at level 52, left associativity).

(* Axiom of extensionality !!! *)
Axiom IS_prop: forall (S: Set) (V: (ps S)) (W: (ps S)) (u: V == W), V ⩮ W.

Definition empty_set (S: Set) := {x : S | ⊥} : ps(S).
Notation "∅( S )" := (empty_set S)(at level 52, left associativity
, format "'∅(' S ')'").

Definition full_set (S: Set) := {x : S | ¬⊥} : ps(S).
Notation "⦿( S )" := (full_set S)(at level 52, left associativity
, format "'⦿(' S ')'").
 
(*Notation "A ⊆ B ⊆ C" := (A ⊆ B ∧ B ⊆ C) (at level 70, B at next level).*)
 
Definition empty_set_is_subset_of_any_set (S: Set) (V: (ps S)) : ∅(S) ⊆ V.
intro.
intro.
cbv in H.
pose proof H (x ∈ V).
apply H0.
Defined.

Definition any_set_is_subset_of_full_set (S: Set) (V: (ps S)) : V ⊆ ⦿(S).
intro.
intro.
unfold full_set.
pose proof element_in S (fun _ => ¬ ⊥) x.
apply H0.
intro.
apply H1.
Defined.


Definition  figure_13_8 (S: Set) (V: (ps S)) : (¬(V == ∅(S))) ⇔ ∃x : S . (x ∈ V ).
refine (biimpl_in (¬ (V == ∅(S))) ((∃ x. x ∈ V)) _ _).
intro.
assert (¬(V ⊆ ∅(S))).
intro.
pose proof empty_set_is_subset_of_any_set S V.
pose proof (conj_in _ _ H0 H1): (V == ∅(S)).
apply (abs_in _ H2 H).
unfold subset in H0.
pose proof H0:(¬ (∀ x. ¬(x ∈ V))).
pose proof ex_in_alt S (fun x => x ∈ V) H1.
apply H2.
intro.
intro.
unfold IS in H0.
left H0.
unfold subset in H1.
pose proof H1:(∀ x. (x ∈ V) ⇒ ⊥).
pose proof ex_el S (fun x=> x ∈ V) H ⊥.
cbv beta in H3.
apply (H3 H2).
Defined.


Definition reflexive (S: Set) (R: S -> S -> Prop) := ∀x : S . (R x x) : Prop.

Definition symmetric (S: Set) (R: S -> S -> Prop) := ∀x : S . ∀y : S . (R x y) ⇒ (R y x) : Prop.

Definition transitive (S: Set) (R: S -> S -> Prop) := ∀x : S . ∀y : S . ∀z : S .  (R x y) ⇒ (R y z) ⇒ (R x z) : Prop.

Definition equivalence_relation (S: Set) (R: S -> S -> Prop) := 
(reflexive S R) ∧ (symmetric S R) ∧ (transitive S R) : Prop.

Definition class (S: Set) (R: S -> S -> Prop) (u : (equivalence_relation S R)) (x: S)
:= {y : S | R x y} : ps(S).

Notation "[ x | R | u ]" := (class _ R u x)(at level 52, left associativity).

Lemma figure_13_11_lemma (S: Set) (R: S -> S -> Prop) (u : (equivalence_relation S R)) :
∀x: S. ∀y: S. ∀z: S. (z ∈ ([x | R | u])) ⇒ (z ∈ ([y | R | u])) ⇒ 
[x | R | u] ⊆ ([y | R | u]).
intro x.
intro y.
intro z.
intro z_in_x.
intro z_in_y.
cbv.
intro m.
intro.
cbv in z_in_x.
cbv in z_in_y.
unfold equivalence_relation in u.
left u.
right H0.
pose proof H1 y z.
cbv in H2.
pose proof H2 z_in_y.
right u.
pose proof H4 x z y z_in_x H3.
pose proof H1 x y H5.
pose proof H4 y x m H6 H.
exact H7.
Defined.

Definition figure_13_11 (S: Set) (R: S -> S -> Prop) (u : (equivalence_relation S R)) :
∀x: S. ∀y: S. ∀z: S. (z ∈ ([x | R | u])) ⇒ (z ∈ ([y | R | u])) ⇒ 
[x | R | u] == [y | R | u].
intro x.
intro y.
intro z.
intro z_in_x.
intro z_in_y.
unfold IS.
pose proof conj_in ([x | R | u] ⊆ ([y | R | u])) ([y| R| u]⊆ ([x| R | u])).
apply H.
apply (figure_13_11_lemma S R u x y z z_in_x z_in_y).
apply (figure_13_11_lemma S R u y x z z_in_y z_in_x).
Defined.

Definition R' (S: Set) (T: Set) (F: S->T) := 
(fun x:S => fun y:T => (y = (F x ))): S -> T -> Prop.

Definition ttf_to_fr (S: Set) (T: Set) (F: S->T) : 
∀x : S . ∃1y : T . ((R' S T F) x y).
intro x.
unfold ex_unique.
apply (conj_in (∃≥1 y. R' S T F x y) (∃≤1 y. R' S T F x y)).
intro C.
unfold R'.
intro H.
apply (H (F x)).
apply (eq_refl T (F x)).
unfold ex_less.
intro y.
intro z.
unfold R'.
intro.
intro.
pose proof eq_symm T z (F x) H0.
pose proof eq_trans T y (F x) z H H1.
exact H2.
Defined.

Definition fr_to_ttf (S: Set) (T: Set) 
(R: S->T->Prop) (u : ∀x : S . ∃1 y : T . (R x y)): S -> T.
intro s.
pose proof u s.
cbv beta in H.
pose proof ι T (fun y => (R s y)) H.
exact H0.
Defined.

Definition injective (S T: Set) (F: S->T) := ∀x1:S . ∀x2 : S . ((F x1 = F x2) ⇒ x1 = x2): Prop.
Definition surjective (S T: Set) (F: S->T) := ∀y : T . ∃x : S . (F x = y): Prop.
Definition bijective (S T: Set) (F: S->T) := (injective S T F) ∧ (surjective S T F): Prop.

Definition exercise_13_12_b (S T: Set) (F: S->T) (u: (bijective S T F)) 
: ∀y : T . ∃1x : S . (F x = y).
intro y.
unfold ex_unique.
right u.
unfold surjective in H.
refine (conj_in _ _ (H y) _).
intro a.
intro b.
intro.
intro.
left u.
unfold injective in H2.
apply (H2 a b).
pose proof eq_symm T (F b) y H1.
pose proof eq_trans T (F a) y (F b) H0 H3.
exact H4.
Defined.

Definition inv (S T: Set) (F: S -> T) (u: (bijective S T F)): T -> S.
intro y.
pose proof exercise_13_12_b S T F u y.
cbv beta in H.
pose proof ι S (fun x => F x = y) H.
exact H0.
Defined.

Definition inj_subset (S T: Set) (V: ps(S)) (F : forall x : S, ((x ∈ V ) -> T)) := 
∀x1 : S. ∀x2 : S . forall p : (x1 ∈ V ), forall q : (x2 ∈ V ), ((F x1 p = F x2 q) ⇒ x1 = x2).

Definition image (S T: Set) (F: S -> T) (V : ps(S)):= 
{y : T | ∃x : S . (x ∈ V ∧ (F x = y))} : ps(T).

Definition origin (S T: Set) (F: S -> T) (W : ps(T)):= 
{x : S | (F x) ∈ W} : ps(S).

Definition figure_13_16 (S T: Set) (F: S -> T) (V : ps(S)) 
: V ⊆ (origin S T F (image S T F V)).
intro m.
intro m_in_V.
unfold element.
unfold origin.
unfold element.
unfold image.
pose proof eq_refl T (F m).
pose proof conj_in _ _ m_in_V H.
pose proof ex_in S (fun g => g ∈ V ∧ F g = F m) m H0.
exact H1.
Defined.

Definition exercise_13_1 (S: Set) (V W: ps(S)) (u: eq_subset S V W): (V == W).
unfold IS.
refine (conj_in (V ⊆ W) (W ⊆ V) _ _).
intro m.
intro m_in_V.
unfold element.
unfold element in m_in_V.
unfold eq_subset in u.
pose proof u (fun g => g m).
cbv beta in H.
left H.
apply H0.
apply m_in_V.
intro m.
intro m_in_W.
unfold element.
unfold element in m_in_W.
unfold eq_subset in u.
pose proof u (fun g => g m).
cbv beta in H.
right H.
apply H0.
apply m_in_W.
Defined.

Definition exercise_13_2_a (S: Set) (V: ps(S)): ∀x : S . ((x ∈ (Vꟲ)) ⇔ ¬(x ∈ V )).
intro x.
pose proof eq_refl S x.
unfold eq in H.
pose proof H (fun x => x ∈ (V ꟲ)).
cbv beta in H0.
apply H0.
Defined.

Definition exercise_13_2_b (S: Set) (V W: ps(S)): (V ⊆ W) ⇒ ((Wꟲ) ⊆ (Vꟲ)).
intro.
unfold subset.
intro x.
unfold element.
unfold complement.
intro x_not_in_W.
intro x_in_V.
pose proof H x x_in_V.
pose proof abs_in (x ∈ W) H0 x_not_in_W.
apply H1.
Defined.

Definition PS(T: Type) := T->Prop.

Definition exercise_13_3 (S : Set): Set.
pose proof PS(PS(PS(S))).
exact S.
Defined.

Definition exercise_13_4_a (S: Set) (V: (ps S)) : V ∪ (∅(S)) == V.
unfold union.
unfold IS.
refine (conj_in _ _ _ _).
intro m.
unfold element.
intro.
unfold empty_set in H.
pose proof disj_el (V m) ⊥ (V m) H (fun x=>x) (fun (a:⊥) => a (V m)).
exact H0.
intro m.
unfold element.
intro.
apply (disj_in_1 (V m) ((∅(S)) m) H).
Defined.

Declare Scope S_scope.
Open Scope S_scope.
Parameter S: Set.

Notation "∅" := (empty_set S): S_scope.
Notation "⦿" := (full_set S): S_scope.

Definition exercise_13_4_b (V: (ps S)) : (V ∩ ∅) == ∅.
refine (conj_in _ _ _ _).
intro m.
unfold intersection.
unfold element.
intro.
right H.
exact H0.
pose proof empty_set_is_subset_of_any_set S (V ∩ ∅).
exact H.
Defined.

Ltac split_is := refine (conj_in _ _ _ _).

Definition exercise_13_4_c (V: (ps S)) : (V ∪ ⦿) == ⦿.
split_is.
intro m.
intro.
unfold union in H.
unfold element in H.
unfold element.
unfold full_set.
intro.
apply H0.
intro m.
intro.
unfold element.
unfold union.
apply (disj_in_2 (m ∈ V) (m ∈ ⦿) H).
Defined.

Definition exercise_13_4_d (V: (ps S)) : (V ∩ ⦿) == V.
split_is.
intro m.
intro.
unfold intersection in H.
pose proof element_el S (fun x=>x ∈ V ∧ x ∈ ⦿) m H.
cbv beta in H0.
left H0.
apply H1.
intro m.
intro.
unfold intersection.
pose proof element_in S (fun x=>x ∈ V ∧ x ∈ ⦿) m.
apply H0.
assert (m ∈ ⦿).
intro.
apply H1.
pose proof conj_in _ _ H H1.
apply H2.
Defined.

Definition exercise_13_5_a (V: (ps S)) : (V ∪ (Vꟲ)) == ⦿.
split_is.
pose proof any_set_is_subset_of_full_set S (V ∪ (V ꟲ)).
apply H.
intro m.
intro.
unfold full_set in H.
unfold element in H.
unfold element.
unfold union.
unfold complement.
unfold element.
pose proof exc_thrd (V m).
apply H0.
Defined.

Definition exercise_13_5_b (V: (ps S)) : (V ∩ (Vꟲ)) == ∅.
split_is.
Focus 2.
pose proof empty_set_is_subset_of_any_set S (V ∩ (V ꟲ)).
apply H.
intro m.
intro.
unfold element in H.
unfold intersection in H.
unfold complement in H.
unfold element in H.
left H.
right H.
pose proof H1 H0 (m ∈ ∅).
apply H2.
Defined.

Definition exercise_13_6_a (V: (ps S)) : ⦿ == ∅ꟲ.
split_is.
intro m.
intro.
unfold element.
unfold complement.
intro.
unfold full_set in H.
unfold element in H.
unfold empty_set in H0.
unfold element in H0.
apply H0.
unfold full_set.
intro m.
unfold complement.
unfold element.
intro.
intro.
apply H0.
Defined.

Definition de_morgan (A B: Prop): ¬ (A ∧ B) -> ¬A ∨ ¬B.
intro.
pose proof exc_thrd (A).
pose proof exc_thrd (B).
apply (disj_el A (¬ A) (¬ A ∨ ¬ B) H0).
intro.
apply (disj_el B (¬ B) (¬ A ∨ ¬ B) H1).
intro.
pose proof conj_in A B H2 H3.
pose proof H H4 (¬ A ∨ ¬ B).
apply H5.
intro.
apply (disj_in_2 (¬ A) (¬ B) H3).
intro.
apply (disj_in_1 (¬ A) (¬ B) H2).
Defined.

(* HARDCORE *)
Definition exercise_13_6_b (V: (ps S)) : ¬(V == ⦿) ⇔ ∃x : S . ¬(x ∈ V ).
refine (conj_in _ _ _ _).
intro.
unfold IS in H.
pose proof de_morgan (V ⊆ ⦿) (⦿ ⊆ V) H.
pose proof disj_el ( ¬ (V ⊆ ⦿)) (¬ (⦿ ⊆ V)) (∃ x. ¬ (x ∈ V)) H0.
apply H1.
clear H1.
intro.
pose proof any_set_is_subset_of_full_set S V.
apply (H1 H2 (∃ x. ¬ (x ∈ V))).
intro.
pose proof ex_in_alt S (fun x => ¬ (x ∈ V)).
cbv beta in H3.
apply H3.
intro.
assert (∀ x. ((x ∈ V))).
intro x.
pose proof H4 x.
cbv beta in H5.
pose proof DN_el (x ∈ V) H5.
apply H6.
unfold full_set in H2.
unfold subset in H2.
unfold element in H2.
assert ((∀ x. ¬ ⊥ ⇒ V x)).
intro.
intro.
pose proof H5 x.
cbv beta in H7.
apply H7.
apply (H2 H6).
intro.
intro.
unfold IS in H0.
right H0.
unfold subset in H1.
unfold full_set in H1.
unfold element in H1.
pose proof ex_el S (fun x => ¬ (x ∈ V)) H ⊥.
apply H2.
intro x.
intro.
pose proof H1 x.
cbv beta in H4.
unfold element in H3.
assert (¬ ⊥).
intro.
apply H5.
pose proof H4 H5.
apply (H3 H6).
Defined.

Definition intersection_el (V W: (ps S)) (m: S): m ∈ (V ∩ W) -> m ∈ V ∧ m ∈ W.
intro.
unfold element in H.
unfold intersection in H.
exact H.
Defined.

Definition exercise_13_7_a (V W: (ps S)) : (V ∩ W == V ) ⇒ (V ⊆ W).
intro.
right H.
intro m.
intro.
pose proof H0 m.
cbv beta in H2.
pose proof H2 H1.
pose proof intersection_el V W m H3.
right H4.
exact H5.
Defined.

Definition exercise_13_7_b (V W: (ps S)) : V \ W == V ∩ (Wꟲ).
split_is.
intro m.
intro.
apply H.
intro.
intro.
apply H.
Defined.

Definition exercise_13_7_c (V W: (ps S)) : V ⊆ W ⇔ (V \ W) == ∅.
refine (conj_in _ _ _ _).
intro.
split_is.
intro m.
intro.
pose proof H m.
cbv beta in H1.
unfold difference in H0.
unfold element in H0.
left H0.
pose proof H1 H2.
pose proof H m H2.
right H0.
pose proof H5 H4 (m ∈ ∅).
apply H6.
pose proof empty_set_is_subset_of_any_set S (V \ W).
apply H0.
intro.
intro m.
intro.
left H.
pose proof H1 m.
cbv beta in H2.
assert (¬¬(m ∈ W)).
intro.
pose proof conj_in _ _ H0 H3.
pose proof H2 H4.
apply H5.
pose proof DN_el (m ∈ W) H3.
apply H4.
Defined.

Definition exercise_13_8 (R: S -> S -> Prop) (s: symmetric S R) (t: transitive S R)
(u: ∀x : S . ∃y : S . (R x y)): (reflexive S R).
intro x.
pose proof u x.
cbv beta in H.
pose proof ex_el S (fun y => R x y) H (R x x).
apply H0.
intro y.
intro.
pose proof s x y H1.
pose proof t x y x H1 H2.
apply H3.
Defined.

Definition second_characteristic_v1 (R: S -> S -> Prop) (u: equivalence_relation S R) := 
∀x: S.  ∀y : S . ([x | R | u] == [y | R | u] ∨ (([x | R | u] ∩ [y | R | u]) == ∅)).

Definition second_characteristic_v2 (R: S -> S -> Prop) (u: equivalence_relation S R) := 
∀x: S.  ∀y : S.  ∀z : S . ((z ∈ [x | R | u]) 
⇒ (z ∈ [y | R | u]) 
⇒ ([x |R | u] == [y | R | u])).

Definition intersection_in (A B: ps (S)) (x: S) 
(u: x ∈ A) (v: x ∈ B):  x ∈ (A ∩ B).
cbv.
intro.
intro.
apply (H u v).
Defined.

(* HARDCORE 2 *)
Definition exercise_13_9 (R: S -> S -> Prop) (u: equivalence_relation S R) :
(second_characteristic_v1 R u) ⇔ (second_characteristic_v2 R u).
unfold second_characteristic_v1.
unfold second_characteristic_v2.
refine (conj_in _ _ _ _).
intro.
intros x y z.
intro.
intro.
pose proof H x y.
cbv beta in H2.
pose proof disj_el ([x | R | u] == [y | R | u])
([x | R | u] ∩ ([y | R | u]) == ∅) 
([x | R | u] == [y | R | u]) H2 (fun x=>x).
apply H3.
intro.
left H4.
pose proof H5 z.
cbv beta in H6.
assert ((z ∈ ∅) -> ([x | R | u] == [y | R | u])).
intro.
apply (H7 ([x | R | u] == [y | R | u])).
apply H7.
apply H6.
pose proof intersection_in _ _ z H0 H1.
apply H8.
intro.
intros x y.
pose proof exc_thrd ([x | R | u] == [y | R | u]).
pose proof disj_el _ _ 
([x | R | u] == [y | R | u] ∨ [x | R | u] ∩ ([y | R | u]) == ∅) H0.
apply H1.
clear H0 H1 H.
intro.
apply (disj_in_1 ([x | R | u] == [y | R | u]) 
([x | R | u] ∩ ([y | R | u]) == ∅) H).
clear H0 H1.
intro.
apply (disj_in_2 ([x | R | u] == [y | R | u]) 
([x | R | u] ∩ ([y | R | u]) == ∅)).
split_is.
intro m.
intro.
pose proof intersection_el _ _ m H1.
left H2.
right H2.
pose proof H x y m H3 H4.
pose proof H0 H5.
apply H6.
apply (empty_set_is_subset_of_any_set S ([x | R | u] ∩ ([y | R | u]))).
Defined.

Definition exercise_13_10_a (R: S -> S -> Prop) (u: equivalence_relation S R) :
∀x. ¬([x | R | u] == ∅).
intro x.
pose proof figure_13_8 S ([x | R | u]).
right H.
apply H0.
left u.
left H1.
pose proof H2 x.
cbv beta in H3.
pose proof H3: (x ∈ ([x | R | u])).
pose proof (ex_in S (fun y => y ∈ ([x | R | u]))) x H4.
apply H5.
Defined.



Definition class_is_reflexive (R: S -> S -> Prop) (u: equivalence_relation S R) :
∀x. x ∈ ([x | R | u]).
intro x.
cbv.
left u.
left H.
apply H0.
Defined.

Definition class_is_symmetric (R: S -> S -> Prop) (u: equivalence_relation S R) :
∀x. ∀y. ((x ∈ ([y | R | u])) ⇒ (y ∈ ([x | R | u]))).
intros x y.
intro.
cbv.
cbv in H.
left u.
right H0.
apply (H1 y x H).
Defined.

Definition class_el (R: S -> S -> Prop) (u: equivalence_relation S R) (x: S) (y: S) 
(v: x ∈ ([y | R | u])): R y x.
apply v.
Defined.

Definition class_is_transitive (R: S -> S -> Prop) (u: equivalence_relation S R) :
∀x. ∀y. ∀z. ((x ∈ ([y | R | u])) ⇒ (y ∈ ([z | R | u])) ⇒ (x ∈ ([z | R | u]))).
intros x y z a b.
right u.
cbv.
cbv in a.
cbv in b.
pose proof H z y x b a.
apply H0.
Defined.

Definition exercise_13_10_b (R: S -> S -> Prop) (u: equivalence_relation S R) :
∀x. ∀y. ∀z : S . (((y ∈ [x | R | u]) ∧ (z ∈ [x | R| u])) ⇒ R y z).
intros x y z.
intro.
apply (class_el R u z y).
left H.
right H.
pose proof class_is_symmetric R u y x H0.
pose proof class_is_transitive R u z x y H1 H2.
apply H3.
Defined.

Definition exercise_13_10_c (R: S -> S -> Prop) (u: equivalence_relation S R) :
∀y : S . ∃x : S . (y ∈ [x | R | u]).
intro y.
pose proof (ex_in S (fun x => y ∈ ([x | R | u])) y).
cbv beta in H.
apply H.
apply (class_is_reflexive R u y).
Defined.

Definition big_union (T: Set) (F: T -> ps(S)) := {x: S | ∃y:T. F y x}.

Definition exercise_13_11 (R: S -> S -> Prop) (u: equivalence_relation S R) :
(∀y : S . ∃x : S . (y ∈ [x | R | u])) ⇔ (big_union S (fun x => [x | R | u]) == full_set S).
refine (conj_in _ _ _ _).
intro.
split_is.
apply (any_set_is_subset_of_full_set S (big_union S ({ x | [x | R | u]}))).
intro m.
intro.
unfold big_union.
unfold element.
pose proof H m.
cbv beta in H1.
apply H1.
intro.
right H.
intro y.
pose proof H0 y.
cbv beta in H1.
assert ((y ∈ ⦿)).
cbv.
intro.
apply H2.
pose proof H1 H2.
unfold big_union in H3.
unfold element in H3.
apply H3.
Defined.

Definition composition (S1 S2 S3: Set) (F: S1->S2) (G: S2->S3) 
:= fun x : S1 => (G(F x)).

Notation "G ◦ F" := (composition _ _ _ F G) (at level 10).


Definition exercise_13_13_a (S1 S2 S3: Set) (F: S1->S2) 
(G: S2->S3) (u: injective S1 S2 F)  (v: injective S2 S3 G):  injective S1 S3 (G ◦ F).
intros x y.
intro.
unfold injective in u.
unfold injective in v.
pose proof u x y.
apply H0.
pose proof v (F x).
pose proof v (F y).
cbv beta in H2.
pose proof H2 ( F x).
cbv beta in H3.
pose proof eq_symm S3 _ _ H.
pose proof H3 H4.
pose proof eq_symm S2 _ _ H5.
apply H6.
Defined.

Definition exercise_13_13_b (S1 S2 S3: Set) (F: S1->S2) 
(G: S2->S3) (u: surjective S1 S2 F)  (v: surjective S2 S3 G):  surjective S1 S3 (G ◦ F).
intro y.
unfold surjective in u , v.
unfold composition.
pose proof v y.
cbv beta in H.
pose proof ex_el S2 (fun x => G x = y) H (∃ x. G (F x) = y).
cbv beta in H0.
apply H0.
clear H0.
intro x.
intro.
pose proof u x.
cbv beta in H1.
pose proof ex_el S1 (fun x0 => F x0 = x) H1 (∃ x0. G (F x0) = y).
apply H2.
clear H2.
intro x'.
intro.
pose proof eq_symm S2 _ _ H2.
pose proof eq_subs S2 (fun x3 => (G x3) = y) x (F x') H3 H0.
cbv beta in H4.
pose proof ex_in S1 (fun x0 => G (F x0) = y) x' H4.
cbv beta in H5.
apply H5.
Defined.

(* HARDCORE 3 *)
Definition exercise_13_14 (T: Set) (F: S -> T) (u: bijective S T F): 
∀y : T . (F((inv S T F u) y) = y).
intro y.
pose proof ι_prop S (fun x => F x = y) ((exercise_13_12_b S T F u y)) as F_iota.
cbv beta in F_iota.
apply F_iota.
Defined.


Definition sur_subset (T: Set) (V: ps(S)) (F : forall x : S, ((x ∈ V ) -> T)) := 
∀y : T. ∃x: S. ∃p: (x ∈ V). F x p = y.

Definition bij_subset (T: Set) (V: ps(S)) (F : forall x : S, ((x ∈ V ) -> T)) := 
(inj_subset S T V F) ∧ (sur_subset T V F).

(* HARDCORE 4 *)
Definition inv_is_a_function (T: Set) (V: ps(S)) (F : forall x : S, ((x ∈ V ) -> T)) 
(u: (bij_subset T V F)) 
: ∀y : T. ∃1x: S. ∃ p: (x ∈ V). F x p = y.
intro y.
left u.
right u.
unfold sur_subset in H0.
pose proof H0 y.
cbv beta in H1.
refine (conj_in (∃≥1 x. ∃ p : x ∈ V . F x p = y) (∃≤1x. ∃ p : x ∈ V . F x p = y) H1 _).
intros a b.
intro.
intro.
pose proof H a b.
cbv beta in H4.
apply (H2 (a = b)).
intro p.
intro.
apply (H3 (a = b)).
intro q.
intro.
pose proof H4 p q.
pose proof eq_symm T (F b q) y H6.
pose proof eq_trans T (F a p) y ((F b q)) H5 H8.
apply (H7 H9).
Defined.


Definition inv_subset (T: Set) (V: ps(S)) (F : forall x : S, ((x ∈ V ) -> T)) 
(u: (bij_subset T V F)): T -> S.
intro y.
pose proof inv_is_a_function T V F u y.
cbv beta in H.
pose proof ι S (fun x => ∃ p : x ∈ V . F x p = y) H.
apply H0.
Defined.

Definition exercise_13_16 (T: Set) (F: S -> T) (u: injective S T F) (V : ps(S))
: ∀x : S . (((F x) ∈ (image S T F V )) ⇒ (x ∈ V) ).
intro x.
intro.
unfold image in H.
unfold element in H.
unfold element.
apply (H (V x)).
intro z.
intro.
left H0.
right H0.
pose proof u z x H2.
pose proof eq_subs S (fun x => V x) z x H3 H1.
apply H4.
Defined.


