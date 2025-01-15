Require Import Ltac.
From BASE Require Import SetTheory.
From BASE Require Import MathLogic.

(* TODO
1) ADD Z
2) Properly formalise <= and use it
3) More automation 
4) Folders for each machine
5) Software Foundations experienve definitely will be useful
6) I need more deep set theory understanding 
(families of sets and cardinality, maybe even chapter one on functions can help)
7) !!! (research) reduce tuple7 to tuple6 ???
8) The full proof of config transition correctness ONLY after addition of Z and <=
9) Should definitely learn coq techniques to autogenerate N proofs for 
0..100 naturals and also autogenerate finit function definition 
and application results
*)


(* 
Textbook Typos:
*)

(* 
https://turingmachine.io/

blank: ' '
input: "00"
start state: start
table:
  scan:
    ' ': {write: ' ', L: finish}
    0: {write: 1, R: start}
  finish:
*)

(* === Turing Machine : Binary Flipper === *)

(* States *)
Definition state_scan := 1.
Definition state_finish := 2.

(* Alphabet *)
Definition blank := 4.

Definition blank_in_range := four_in_N.

(* Directions *)
Definition D_left := 1.
Definition D_right := 2.

Definition bf_states := {state_scan, state_finish}.

Definition bf_input_symbols := {0, 1}.

Definition bf_tape_symbols := triple_unord 0 1 blank.

Definition bf_transition_function_exists: ∃1t. ∀x. ((x ∈ t) ⇔
(
    (x = <<state_scan, 0>, <state_scan, 1, D_right>>) ∨ 
    (x = <<state_scan, 1>, <state_scan, 0, D_right>>)  ∨ 
    (x = <<state_scan, blank>, <state_finish, blank, D_left>> )
    )).
apply (conj_in).
pose proof subset_of_cartesian5_for_2_args_exists N N N N N
(fun x=>(x = <<state_scan, 0>, <state_scan, 1, D_right>>) ∨ 
    (x = <<state_scan, 1>, <state_scan, 0, D_right>>)  ∨ 
    (x = <<state_scan, blank>, <state_finish, blank, D_left>> )).
2: apply any_biimpl_set_is_no_more_than_one.
left H.
cbv beta in H0.
destruct_ex H0 super_cartesian.
clear H H0.
apply (ex_in _ super_cartesian).
intro w.
apply (conj_in).
intro.
set_el_1 H1 w H.
right H0.
apply H2.
intro.
set_right H1 w.
apply H0.
apply (conj_in).
destruct_3_disj H.
unfold state_scan in d_1.
unfold D_right in d_1.
apply (tuple5_arg2_obviously_exists w 1 0 1 1 2 d_1
one_in_N zero_in_N one_in_N one_in_N two_in_N).
apply (tuple5_arg2_obviously_exists w 1 1 1 0 2 d_2
one_in_N one_in_N one_in_N zero_in_N two_in_N).
unfold blank in d_3.
unfold state_scan in d_3.
unfold state_finish in d_3.
unfold D_left in d_3.
apply (tuple5_arg2_obviously_exists w 1 4 2 4 1 d_3
one_in_N four_in_N two_in_N four_in_N one_in_N).
apply H.
Defined.

Definition bf_transition_function := ι _ (bf_transition_function_exists).

Definition bf_blank_symbol := blank.

Definition bf_start_state := state_scan.

Definition bf_final_states := {`state_finish}.

Definition binary_flip_tm := tuple7 
bf_states bf_input_symbols bf_tape_symbols bf_transition_function bf_start_state bf_blank_symbol bf_final_states.

Definition zero_in_bf_ts: 0 ∈ bf_tape_symbols.
unfold bf_tape_symbols.
extract_iota_from_goal (triple_unord 0 1 blank).
set_right iota_prop 0.
apply iota_prop0.
apply disj_in_1.
apply disj_in_1.
apply eq_refl.
Defined.

Definition one_in_bf_ts: 1 ∈ bf_tape_symbols.
unfold bf_tape_symbols.
extract_iota_from_goal (triple_unord 0 1 blank).
set_right iota_prop 1.
apply iota_prop0.
apply disj_in_1.
apply disj_in_2.
apply eq_refl.
Defined.

Definition blank_in_bf_ts: blank ∈ bf_tape_symbols.
unfold bf_tape_symbols.
extract_iota_from_goal (triple_unord 0 1 blank).
set_right iota_prop blank.
apply iota_prop0.
apply disj_in_2.
apply eq_refl.
Defined.

Definition init_tape := piecewise_function_nat_3_elements  
0 0 blank blank bf_tape_symbols
zero_in_bf_ts zero_in_bf_ts blank_in_bf_ts blank_in_bf_ts.

Definition config1 := <state_scan, 0, init_tape>.

Definition tape_1 := piecewise_function_nat_3_elements 
1 0 blank blank bf_tape_symbols
one_in_bf_ts zero_in_bf_ts blank_in_bf_ts blank_in_bf_ts.

Definition config2 := <state_scan, 1, tape_1>.

Definition tape_2 := piecewise_function_nat_3_elements 
1 1 blank blank bf_tape_symbols
one_in_bf_ts one_in_bf_ts blank_in_bf_ts blank_in_bf_ts.

Definition config3 := <state_scan, 2, tape_2>.

Definition config4 := <state_finish, 1, tape_2>.

Definition correct_config_transition (tm: Set) (config_a config_b: Set) := 
∃state_a. ∃head_position_a. ∃tape_a. (config_a = <state_a, head_position_a, tape_a>) ∧ 
∃state_b. ∃head_position_b. ∃tape_b. (config_b = <state_b, head_position_b, tape_b>) ∧ 
∃states. ∃input_symbols. ∃tape_symbols. ∃transition_function. ∃start_state. ∃blank_symbol. ∃final_states.
(tm = tuple7 states input_symbols tape_symbols transition_function start_state blank_symbol final_states) ∧ 
∃tape_a_is_func: (is_function tape_a N tape_symbols).
∃a_in_X: (head_position_a ∈ N).
∃tape_b_is_func: (is_function tape_b N tape_symbols).
(let head_a := f_appl tape_a N tape_symbols tape_a_is_func head_position_a a_in_X in
let head_a_after_transition := f_appl tape_b N tape_symbols tape_b_is_func head_position_a a_in_X in

((head_position_a < head_position_b) ->
(<<state_a, head_a>, <state_b, head_a_after_transition, D_right>>) ∈ transition_function)
∧
((head_position_b < head_position_a) ->
(<<state_a, head_a>, <state_b, head_a_after_transition, D_left>>) ∈ transition_function)).

Notation "'∃' x : T . p" := (@ex T (fun x => p))
  (at level 200, x binder, right associativity).

Definition init_tape_is_function: is_function init_tape N bf_tape_symbols.
unfold init_tape.
pose proof piecewise_function_nat_3_elements_is_function
0 0 blank blank bf_tape_symbols
zero_in_bf_ts zero_in_bf_ts blank_in_bf_ts blank_in_bf_ts.
apply H.
Defined.

Definition tape1_is_function: is_function tape_1 N bf_tape_symbols.
unfold tape_1.
pose proof piecewise_function_nat_3_elements_is_function
1 0 blank blank bf_tape_symbols
one_in_bf_ts zero_in_bf_ts blank_in_bf_ts blank_in_bf_ts.
apply H.
Defined.

Definition init_tape_0_eq_0: f_appl init_tape N bf_tape_symbols init_tape_is_function 0 zero_in_N = 0.
extract_iota_from_goal (f_appl init_tape N bf_tape_symbols init_tape_is_function 0 zero_in_N).
left iota_prop.
right iota_prop.
unfold init_tape in H0.
extract_iota (piecewise_function_nat_3_elements 0 0 blank blank
bf_tape_symbols zero_in_bf_ts zero_in_bf_ts blank_in_bf_ts
blank_in_bf_ts) H0.
set_left iota_prop0 (< 0, s >).
pose proof iota_prop1 H0.
destruct_4_disj H1.
pose proof pair_property d_1.
right H1.
apply H2.
pose proof zero_not_equals_to_one.
apply (pr1_not_equal_in_pairs_leads_to_contradiction d_2 H1).
pose proof zero_not_equals_to_two.
apply (pr1_not_equal_in_pairs_leads_to_contradiction d_3 H1).
destruct_ex d_4 n.
right H1.
left H1.
left H3.
right H3.
pose proof pair_property H2.
left H6.
repl H7 H5.
pose proof two_is_not_lt_than_zero.
apply (H9 H8).
Defined.

Definition tape1_0_eq_1: (f_appl tape_1 N bf_tape_symbols tape1_is_function 0 zero_in_N) = 1.
extract_iota_from_goal (f_appl tape_1 N bf_tape_symbols tape1_is_function 0 zero_in_N).
left iota_prop.
right iota_prop.
unfold tape_1 in H0.
extract_iota (piecewise_function_nat_3_elements 1 0
blank blank bf_tape_symbols
one_in_bf_ts zero_in_bf_ts
blank_in_bf_ts blank_in_bf_ts) H0.
set_left iota_prop0 (< 0, s >).
pose proof iota_prop1 H0.
clear iota_prop0 iota_prop1.
destruct_4_disj H1.
pose proof pair_property d_1.
right H1.
apply H2.
pose proof zero_not_equals_to_one.
apply (pr1_not_equal_in_pairs_leads_to_contradiction d_2 H1).
pose proof zero_not_equals_to_two.
apply (pr1_not_equal_in_pairs_leads_to_contradiction d_3 H1).
destruct_ex d_4 n.
left H1.
right H2.
left H2.
right H1.
pose proof pair_property H5.
left H6.
right H6.
assert (¬(0 = n)).
intro.
repl H9 H3.
pose proof two_is_not_lt_than_zero.
apply (H11 H10).
apply (pr1_not_equal_in_pairs_leads_to_contradiction H5 H9).
Defined.

Definition transition1_correct: correct_config_transition binary_flip_tm config1 config2.
unfold correct_config_transition.
apply (ex_in _ state_scan).
apply (ex_in _ 0).
apply (ex_in _ init_tape).
apply conj_in.
apply (eq_refl config1).
apply (ex_in _ state_scan).
apply (ex_in _ 1).
apply (ex_in _ tape_1).
apply conj_in.
apply (eq_refl config2).
apply (ex_in _ bf_states).
apply (ex_in _ bf_input_symbols). 
apply (ex_in _ bf_tape_symbols). 
apply (ex_in _ bf_transition_function). 
apply (ex_in _ bf_start_state). 
apply (ex_in _ bf_blank_symbol). 
apply (ex_in _ bf_final_states).
apply conj_in.
apply eq_refl.
apply (ex_in _ init_tape_is_function).
apply (ex_in _ zero_in_N).
apply (ex_in _ tape1_is_function).
apply conj_in.
intro.
unfold state_scan.
pose proof init_tape_0_eq_0.
pose proof eq_symm _ _ H0.
pose proof (eq_subs (fun g=> <
< 1, g >,
< 1, f_appl tape_1 N bf_tape_symbols tape1_is_function 0 zero_in_N,
D_right > > ∈ bf_transition_function) _ _ H1).
apply H2.
clear H0 H1 H2.
pose proof tape1_0_eq_1.
pose proof eq_symm _ _ H0.
pose proof (eq_subs (fun g=> < < 1, 0 >,
< 1,g, D_right > > ∈ bf_transition_function) _ _ H1).
apply H2.
clear H0 H1 H2.
extract_iota_from_goal bf_transition_function.
unfold state_scan in iota_prop.
set_right iota_prop (< < 1, 0 >, < 1, 1, D_right > >).
apply iota_prop0.
apply disj_in_1.
apply disj_in_1.
apply eq_refl.
intro.
pose proof one_is_not_lt_than_zero.
apply (H0 H).
Defined.
