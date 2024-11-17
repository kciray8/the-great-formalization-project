Require Import Ltac.
Notation "A -> B" := (forall (_ : A), B) (at level 99, right associativity).
Parameter In: Set -> Set -> Prop.
Notation "a ∈ b" := (In a b)(at level 80, left associativity).

Axiom unique_subset: forall (A: (Set -> Prop)) (b: Set), Set.
Axiom set: forall (A: (Set -> Prop)) (b: Set), Set.
Axiom f: forall s: Set, Prop.

Notation "{ x 'ε' a | A }" := (unique_subset (fun x => A) a).

Notation "b ≔ { x | A }" := (set (fun x => A) b)
(at level 70, x binder).

Axiom pair_unord: forall a b: Set, Set.


Axiom unit_set: forall a: Set,Set .


Notation "{ a , b }" := (pair_unord a b).

Notation "{ a }" := (unit_set a).


Definition everySetIsElementOfSomeSet: forall (x y: Set), Set.
intros.
pose proof (f({x,x})).
pose proof (f({x})).
pose proof (f(y ≔ {x | x ∈ x} )).
pose proof (f({x ε y | (x ∈ x)})).

apply x.
Defined.




