Require Import Ltac.
From BASE Require Import MathLogic.

(* DON'T FORGET TO ADD "-noinit" TO OPTIONS !!!*)

(* https://www.let.rug.nl/bos/lpn//lpnpage.php?pageid=online *)

(* Core definition *)
Axiom Term: Type.
Axiom uni: Term -> Term -> Prop.
Axiom uni_refl: forall a: Term, uni a a.
Notation "A = B" := (uni A B)(at level 51, right associativity).
Axiom kb: Term->Prop.
(* Chapter 1 Facts, Rules, and Queries *)

Axiom mia: Term. 
Axiom mia_in_kb: kb(mia).
Axiom yolanda: Term.
Axiom yolanda_in_kb: kb(yolanda).
Axiom jody: Term.
Axiom jody_in_kb: kb(jody).
Axiom butch: Term.
Axiom butch_in_kb: kb(butch).
Axiom marcellus: Term.
Axiom marcellus_in_kb: kb(marcellus).
Axiom zed: Term.
Axiom zed_in_kb: kb(zed).

Axiom woman: Term -> Term.
Axiom playsAirGuitar: Term -> Term.
Axiom killer: Term -> Term.

Axiom mia_is_woman:  kb(woman(mia)).
Axiom jody_plays_ag: kb(playsAirGuitar(jody)).

Axiom party: Term.
Axiom party_in_kb: kb(party).

Goal kb(woman(mia)).
apply mia_is_woman.
Qed.

Goal kb(playsAirGuitar(jody)).
apply jody_plays_ag.
Qed.

Axiom happy: Term -> Term.
Axiom listens2Music: Term -> Term.

Axiom yolana_is_happy: kb(happy(yolanda)).
Axiom mia_listens: kb(listens2Music(mia)).
Axiom happy_then_listens: kb(happy(yolanda)) -> kb(listens2Music(yolanda)).

Goal kb(listens2Music(yolanda)).
apply(happy_then_listens).
apply yolana_is_happy.
Qed.

Goal ∃a. kb(woman(a)).
apply (ex_in _ mia mia_is_woman).
Qed.

Axiom butch_is_killer: kb(killer(butch)).
Axiom married: Term -> Term -> Term.
Axiom gives_massage: Term -> Term -> Term.
Axiom kills: Term -> Term -> Term.
Axiom dead: Term -> Term.
Axiom married_m_m: kb(married mia marcellus).
Axiom zed_is_dead: kb(dead(zed)).
Axiom kills_then_dead: ∀x. ∀k. (kb((kills k x)) -> kb(dead x)).
Axiom marcellus_kills: ∀x. (kb(gives_massage x mia)) -> kb(kills marcellus x).
Axiom jody_gives_m: kb(gives_massage jody mia).

Goal kb(dead(jody)).
apply (kills_then_dead jody marcellus).
apply (marcellus_kills).
apply jody_gives_m.
Qed.

(* Chapter 2 Unification and Proof Search *)

Goal jody = jody.
apply (uni_refl jody).
Qed.

Axiom k2: Term->Term->Term.
Axiom k0: Term.
Axiom s: Term->Term.
Axiom t: Term->Term.
Axiom g: Term.
Goal ∃X. ∃Y. (k2 (s g) Y)  =  (k2 X (t k0)).
apply (ex_in _ (s g)).
apply (ex_in _ (t k0)).
apply uni_refl.
Qed.

Axiom vincent: Term.
Axiom loves: Term -> Term -> Term.
Axiom jealous: Term -> Term -> Term.
Axiom loves_v_m: kb(loves vincent mia).
Axiom loves_m_m: kb(loves marcellus mia).
Axiom jealous_def: ∀A. ∀B. ∀C. (kb(loves A C) ∧ kb(loves B C)) -> kb(jealous A B).

Goal kb(jealous vincent marcellus).
apply (jealous_def vincent marcellus mia).
apply conj_in.
apply loves_v_m.
apply loves_m_m.
Qed.

(* Chapter 3 Recursion *)
Axiom anne: Term.
Axiom bridget: Term.
Axiom caroline: Term.
Axiom donna: Term.
Axiom emily: Term.

Axiom child: Term->Term->Term.
Axiom child_a_b: kb(child anne bridget).
Axiom child_b_c: kb(child bridget caroline).
Axiom child_c_d: kb(child caroline donna).
Axiom child_d_e: kb(child donna emily).

Axiom descend: Term->Term->Term.
Axiom descend_base: ∀A. ∀B. kb (child A B) -> kb (descend A B).
Axiom descend_rec: ∀A. ∀B. ∀C. kb(descend A B) ∧ kb(child B C) -> kb (descend A C).

Goal kb(descend anne donna).
apply (descend_rec anne caroline donna).
apply (conj_in).
apply (descend_rec anne bridget caroline).
apply (conj_in).
apply (descend_base).
apply child_a_b.
apply child_b_c.
apply child_c_d.
Qed.


(* Chapter 4 Lists *)
Axiom nil: Term.
Axiom cons: Term->Term->Term.

Notation "[ ]" := nil (format "[ ]").
Notation "[ x ]" := (cons x nil).
Notation "[ x , y | T ]" := (cons x (cons y T)).
Notation "[ x , y , .. , z ]" := (cons x (cons y .. (cons z nil) ..)).
Notation "[ H | T ]" := (cons H T).


Goal  ∃Head. ∃Tail. [Head|Tail]  =  [mia,  vincent, yolanda].
apply (ex_in _ mia).
apply (ex_in _ [vincent, yolanda]).
apply uni_refl.
Qed.

Axiom member: Term -> Term -> Term.
Axiom member_base: ∀E. ∀L. kb(member E [E|L]).
Axiom member_rec: ∀E. ∀L. ∀K. kb(member E L) -> kb(member E [K|L]).

Goal kb(member vincent [mia,  vincent, yolanda]).
apply member_rec.
apply member_base.
Qed.

Goal ∀a. ∀b. ∀c. ∀d. [a,b,c,d]  =  [a|[b,c,d]].
intro.
intro.
intro.
intro.
apply uni_refl.
Qed.

Axiom last: Term -> Term -> Term.
Axiom last_base: ∀E. kb(last E [E|nil]).
Axiom last_rec: ∀E. ∀L. ∀K. kb(last E L) -> kb(last E [K|L]).

Goal kb(last yolanda [mia,  vincent, yolanda]).
apply last_rec.
apply last_rec.
apply last_base.
Qed.

Axiom twice: Term -> Term -> Term.
Axiom twice_base: kb(twice [] []).
Axiom twice_rec: ∀H. ∀T1. ∀T2. kb(twice T1 T2) -> kb(twice [H|T1] [H, H | T2]).

Goal kb(twice [mia, yolanda] [mia,mia,yolanda,yolanda]).
apply twice_rec.
apply twice_rec.
apply twice_base.
Qed.

Axiom zero: Term.
Axiom succ: Term->Term.
Axiom add: Term->Term->Term->Term.

Notation "A + B == C" := (add A B C)(at level 70).

Axiom add_base: ∀Y. kb (add zero Y Y).
Axiom add_rec:  ∀X. ∀Y. ∀Z. kb (add X Y Z) -> kb (add (succ X) Y (succ Z)).

Notation "0" := zero.
Notation "1" := (succ zero).
Notation "2" := (succ (succ zero)).
Notation "3" := (succ (succ (succ zero))).
Notation "4" := (succ (succ (succ (succ zero)))).
Notation "5" := (succ (succ (succ (succ (succ zero))))).
Notation "6" := (succ (succ (succ (succ (succ (succ zero)))))).

Goal kb(1 + 2 == 3).
apply add_rec.
apply add_base.
Qed.

(* Chapter 5 Arithmetic *)
Axiom inc: Term->Term->Term.
Axiom inc_base: kb(inc 0 1).
Axiom inc_rec: ∀X. kb(inc X (succ X)) -> kb(inc (succ X) (succ (succ X))).
Goal kb(inc 2 3).
apply inc_rec.
apply inc_rec.
apply inc_base.
Qed.

Axiom length: Term->Term->Term.
Axiom length_base: kb(length [] 0).
Axiom length_rec: ∀X. ∀L. ∀Y.  kb(length X L) -> kb(length [Y|X] (succ L)).

Goal kb(length [mia, yolanda] 2).
apply length_rec.
apply length_rec.
apply length_base.
Qed.

Axiom le: Term->Term->Term.
Notation "A <= B" := (le A B)(at level 70).
Axiom le_base: ∀X. kb(X <= X).
Axiom le_rec: ∀X. ∀Y. kb(X <= Y) -> kb(X <= (succ Y)).

Axiom gt: Term->Term->Term.
Notation "A > B" := (gt A B)(at level 70).
Axiom gt_base: ∀X. kb((succ X) > X).
Axiom gt_rec: ∀X. ∀Y. kb(X > Y) -> kb((succ X) > Y).

Goal kb(1 <= 2).
apply le_rec.
apply le_base.
Qed.

Definition dick(A B: Prop) := B -> A.
Notation "~ A ~" := (kb A)(at level 70).
Notation "~ A :- B ~" := (dick (kb A) (kb B))(at level 70, B at next level).
Notation "~ A :- B , .. , Y , Z ~" := (dick (kb A) (conj (kb B) .. (conj (kb Y) (kb Z)) ..))
(at level 70, B at next level, Y at next level, Z at next level).

Axiom max_acc: Term->Term->Term->Term.
Axiom max_acc_base: ∀X. ~ max_acc [] X X ~.

Axiom max_acc_rec1: ∀H. ∀T. ∀A. ∀M. ~ (max_acc [H|T] A M) :- (max_acc T A M) , (H <= A) ~.
Axiom max_acc_rec2: ∀H. ∀T. ∀A. ∀M. ~ (max_acc [H|T] A M) :- (max_acc T H M) , (H > A) ~.

Axiom max: Term->Term->Term.
Axiom max_base: ∀H. ∀T. ∀M. ~ (max [H|T] M) :- (max_acc [H|T] H M) ~. 

Goal kb(max [2,3,1] 3).
apply max_base.
apply (max_acc_rec1 2).
apply (conj_in).
apply (max_acc_rec2 3).
apply (conj_in).
apply (max_acc_rec1).
apply (conj_in).
apply max_acc_base.
apply le_rec.
apply le_rec.
apply le_base.
apply gt_base.
apply le_base.
Qed.

Axiom add_one: Term->Term->Term.
Axiom add_one_base: 
~ add_one [] [] ~.
Axiom add_one_rec: ∀H. ∀H2. ∀T1. ∀T2. 
~ add_one [H|T1] [H2|T2] :- add_one T1 T2, inc H H2 ~.

Goal ~ add_one [1,2] [2,3] ~.
apply add_one_rec.
apply (conj_in).
apply add_one_rec.
apply (conj_in).
apply add_one_base.
apply inc_rec.
apply inc_rec.
apply inc_base.
apply inc_rec.
apply inc_base.
Qed.

Axiom append: Term -> Term -> Term -> Term.
Axiom append_base: ∀L. ~ append [] L L ~.
Axiom append_rec: ∀A. ∀B. ∀H. ∀T. ~ append [H|T] A [H|B] :- append T A B ~.

Goal ~append [mia] [yolanda] [mia, yolanda]~.
apply append_rec.
apply append_base.
Qed.

Axiom reverse: Term -> Term -> Term.
Axiom reverse_base: ~ reverse [] [] ~.
Axiom reverse_rec:  ∀H. ∀T. ∀K. ∀L. ~ reverse [H|T] K :- append L [H] K, reverse L T ~.

Goal ~reverse [mia, yolanda, jody] [jody, yolanda, mia]~.
apply (reverse_rec mia [yolanda, jody] [jody, yolanda, mia] [jody, yolanda]).
apply (conj_in).
apply (append_rec).
apply (append_rec).
apply (append_base).
apply (reverse_rec jody [yolanda] [yolanda, jody] [yolanda]).
apply (conj_in).
apply (append_rec).
apply (append_base).
apply (reverse_rec yolanda [] [yolanda] []).
apply (conj_in).
apply (append_base).
apply (reverse_base).
Qed.

