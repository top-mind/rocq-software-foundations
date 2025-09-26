Set Warnings "-notation-overridden,-parsing".
From Stdlib Require Export String.
From VFA Require Import Color.

Parameter MISSING: Type.

Module Check.

Ltac check_type A B :=
    match type of A with
    | context[MISSING] => idtac "Missing:" A
    | ?T => first [unify T B; idtac "Type: ok" | idtac "Type: wrong - should be (" B ")"]
    end.

Ltac print_manual_grade A :=
    match eval compute in A with
    | Some (_ ?S ?C) =>
        idtac "Score:"  S;
        match eval compute in C with
          | ""%string => idtac "Comment: None"
          | _ => idtac "Comment:" C
        end
    | None =>
        idtac "Score: Ungraded";
        idtac "Comment: None"
    end.

End Check.

From VFA Require Import Color.
Import Check.

Goal True.

idtac "-------------------  Sremove_elements  --------------------".
idtac " ".

idtac "#> Sremove_elements".
idtac "Possible points: 3".
check_type @Sremove_elements (
(forall (i : E.t) (s : S.t) (_ : S.In i s),
 @eq (list S.elt) (S.elements (S.remove i s))
   (@List.filter BinNums.positive
      (fun x : BinNums.positive => if E.eq_dec x i then false else true)
      (S.elements s)))).
idtac "Assumptions:".
Abort.
Print Assumptions Sremove_elements.
Goal True.
idtac " ".

idtac "-------------------  InA_map_fst_key  --------------------".
idtac " ".

idtac "#> InA_map_fst_key".
idtac "Possible points: 2".
check_type @InA_map_fst_key (
(forall (A : Type) (j : BinNums.positive) (l : list (prod M.E.t A)),
 iff
   (@SetoidList.InA BinNums.positive E.eq j
      (@ListDef.map (prod M.E.t A) M.E.t (@fst M.E.t A) l))
   (@ex A
      (fun e : A =>
       @SetoidList.InA (prod M.key A) (@M.eq_key_elt A)
         (@pair BinNums.positive A j e) l)))).
idtac "Assumptions:".
Abort.
Print Assumptions InA_map_fst_key.
Goal True.
idtac " ".

idtac "-------------------  Sorted_lt_key  --------------------".
idtac " ".

idtac "#> Sorted_lt_key".
idtac "Possible points: 3".
check_type @Sorted_lt_key (
(forall (A : Type) (al : list (prod BinNums.positive A)),
 iff (@Sorted.Sorted (prod M.key A) (@M.lt_key A) al)
   (@Sorted.Sorted BinNums.positive E.lt
      (@ListDef.map (prod BinNums.positive A) BinNums.positive
         (@fst BinNums.positive A) al)))).
idtac "Assumptions:".
Abort.
Print Assumptions Sorted_lt_key.
Goal True.
idtac " ".

idtac "-------------------  cardinal_map  --------------------".
idtac " ".

idtac "#> cardinal_map".
idtac "Possible points: 6".
check_type @cardinal_map (
(forall (A B : Type) (f : forall _ : A, B) (g : M.t A),
 @eq nat (@M.cardinal B (@M.map A B f g)) (@M.cardinal A g))).
idtac "Assumptions:".
Abort.
Print Assumptions cardinal_map.
Goal True.
idtac " ".

idtac "-------------------  Sremove_cardinal_less  --------------------".
idtac " ".

idtac "#> Sremove_cardinal_less".
idtac "Possible points: 6".
check_type @Sremove_cardinal_less (
(forall (i : S.elt) (s : S.t) (_ : S.In i s),
 lt (S.cardinal (S.remove i s)) (S.cardinal s))).
idtac "Assumptions:".
Abort.
Print Assumptions Sremove_cardinal_less.
Goal True.
idtac " ".

idtac "-------------------  Mremove_elements  --------------------".
idtac " ".

idtac "#> Mremove_elements".
idtac "Possible points: 6".
check_type @Mremove_elements (
(forall (A : Type) (i : M.key) (s : M.t A) (_ : @M.In A i s),
 @SetoidList.eqlistA (prod M.key A) (@M.eq_key_elt A)
   (@M.elements A (@M.remove A i s))
   (@List.filter (prod BinNums.positive A)
      (fun x : prod BinNums.positive A =>
       if E.eq_dec (@fst BinNums.positive A x) i then false else true)
      (@M.elements A s)))).
idtac "Assumptions:".
Abort.
Print Assumptions Mremove_elements.
Goal True.
idtac " ".

idtac "-------------------  Mremove_cardinal_less  --------------------".
idtac " ".

idtac "#> Mremove_cardinal_less".
idtac "Possible points: 3".
check_type @Mremove_cardinal_less (
(forall (A : Type) (i : M.key) (s : M.t A) (_ : @M.In A i s),
 lt (@M.cardinal A (@M.remove A i s)) (@M.cardinal A s))).
idtac "Assumptions:".
Abort.
Print Assumptions Mremove_cardinal_less.
Goal True.
idtac " ".

idtac "-------------------  two_little_lemmas  --------------------".
idtac " ".

idtac "#> fold_right_rev_left".
idtac "Possible points: 1".
check_type @fold_right_rev_left (
(forall (A B : Type) (f : forall (_ : A) (_ : B), A) (l : list B) (i : A),
 @eq A (@List.fold_left A B f l i)
   (@List.fold_right A B (fun (x : B) (y : A) => f y x) i (@List.rev B l)))).
idtac "Assumptions:".
Abort.
Print Assumptions fold_right_rev_left.
Goal True.
idtac " ".

idtac "#> Snot_in_empty".
idtac "Possible points: 1".
check_type @Snot_in_empty ((forall n : S.elt, not (S.In n S.empty))).
idtac "Assumptions:".
Abort.
Print Assumptions Snot_in_empty.
Goal True.
idtac " ".

idtac "-------------------  Sin_domain  --------------------".
idtac " ".

idtac "#> Sin_domain".
idtac "Possible points: 3".
check_type @Sin_domain (
(forall (A : Type) (n : S.elt) (g : M.t A),
 iff (S.In n (@Mdomain A g)) (@M.In A n g))).
idtac "Assumptions:".
Abort.
Print Assumptions Sin_domain.
Goal True.
idtac " ".

idtac "-------------------  subset_nodes_sub  --------------------".
idtac " ".

idtac "#> subset_nodes_sub".
idtac "Possible points: 3".
check_type @subset_nodes_sub (
(forall (P : forall (_ : node) (_ : nodeset), bool) (g : graph),
 S.Subset (subset_nodes P g) (nodes g))).
idtac "Assumptions:".
Abort.
Print Assumptions subset_nodes_sub.
Goal True.
idtac " ".

idtac "-------------------  select_terminates  --------------------".
idtac " ".

idtac "#> select_terminates".
idtac "Possible points: 3".
check_type @select_terminates (
(forall (K : nat) (g : graph) (n : S.elt)
   (_ : @eq (option S.elt) (S.choose (subset_nodes (low_deg K) g))
          (@Some S.elt n)),
 lt (@M.cardinal nodeset (remove_node n g)) (@M.cardinal nodeset g))).
idtac "Assumptions:".
Abort.
Print Assumptions select_terminates.
Goal True.
idtac " ".

idtac "-------------------  adj_ext  --------------------".
idtac " ".

idtac "#> adj_ext".
idtac "Possible points: 2".
check_type @adj_ext (
(forall (g : graph) (i j : BinNums.positive) (_ : E.eq i j),
 S.eq (adj g i) (adj g j))).
idtac "Assumptions:".
Abort.
Print Assumptions adj_ext.
Goal True.
idtac " ".

idtac "-------------------  in_colors_of_1  --------------------".
idtac " ".

idtac "#> in_colors_of_1".
idtac "Possible points: 3".
check_type @in_colors_of_1 (
(forall (i : S.elt) (s : S.t) (f : M.t S.elt) (c : S.elt)
   (_ : S.In i s)
   (_ : @eq (option S.elt) (@M.find S.elt i f) (@Some S.elt c)),
 S.In c (colors_of f s))).
idtac "Assumptions:".
Abort.
Print Assumptions in_colors_of_1.
Goal True.
idtac " ".

idtac "-------------------  color_correct  --------------------".
idtac " ".

idtac "#> color_correct".
idtac "Possible points: 6".
check_type @color_correct (
(forall (palette : S.t) (g : graph) (_ : no_selfloop g) (_ : undirected g),
 coloring_ok palette g (color palette g))).
idtac "Assumptions:".
Abort.
Print Assumptions color_correct.
Goal True.
idtac " ".

idtac " ".

idtac "Max points - standard: 51".
idtac "Max points - advanced: 51".
idtac "".
idtac "Allowed Axioms:".
idtac "functional_extensionality".
idtac "functional_extensionality_dep".
idtac "FunctionalExtensionality.functional_extensionality_dep".
idtac "int".
idtac "Abs".
idtac "Abs_inj".
idtac "ltb".
idtac "ltb_lt".
idtac "leb".
idtac "leb_le".
idtac "Extract.int".
idtac "Extract.Abs".
idtac "Extract.Abs_inj".
idtac "Extract.ltb".
idtac "Extract.ltb_lt".
idtac "Extract.leb".
idtac "Extract.leb_le".
idtac "".
idtac "".
idtac "********** Summary **********".
idtac "".
idtac "Below is a summary of the automatically graded exercises that are incomplete.".
idtac "".
idtac "The output for each exercise can be any of the following:".
idtac "  - 'Closed under the global context', if it is complete".
idtac "  - 'MANUAL', if it is manually graded".
idtac "  - A list of pending axioms, containing unproven assumptions. In this case".
idtac "    the exercise is considered complete, if the axioms are all allowed.".
idtac "".
idtac "********** Standard **********".
idtac "---------- Sremove_elements ---------".
Print Assumptions Sremove_elements.
idtac "---------- InA_map_fst_key ---------".
Print Assumptions InA_map_fst_key.
idtac "---------- Sorted_lt_key ---------".
Print Assumptions Sorted_lt_key.
idtac "---------- cardinal_map ---------".
Print Assumptions cardinal_map.
idtac "---------- Sremove_cardinal_less ---------".
Print Assumptions Sremove_cardinal_less.
idtac "---------- Mremove_elements ---------".
Print Assumptions Mremove_elements.
idtac "---------- Mremove_cardinal_less ---------".
Print Assumptions Mremove_cardinal_less.
idtac "---------- fold_right_rev_left ---------".
Print Assumptions fold_right_rev_left.
idtac "---------- Snot_in_empty ---------".
Print Assumptions Snot_in_empty.
idtac "---------- Sin_domain ---------".
Print Assumptions Sin_domain.
idtac "---------- subset_nodes_sub ---------".
Print Assumptions subset_nodes_sub.
idtac "---------- select_terminates ---------".
Print Assumptions select_terminates.
idtac "---------- adj_ext ---------".
Print Assumptions adj_ext.
idtac "---------- in_colors_of_1 ---------".
Print Assumptions in_colors_of_1.
idtac "---------- color_correct ---------".
Print Assumptions color_correct.
idtac "".
idtac "********** Advanced **********".
Abort.

(* 2025-08-24 13:54 *)

(* 2025-08-24 13:54 *)
