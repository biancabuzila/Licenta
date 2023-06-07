module LemmasForClauses.AndClauses

open FStar.List.Tot
module L = FStar.List.Tot.Base
module LP = FStar.List.Tot.Properties
open FStar.Classical
open FormulaT
open CnfFormula
open TseitinCore



let and_clauses (v1:int {valid_variable v1}) 
                (v2:int {valid_variable v2}) 
                (v:int {valid_variable v}) 
    : r : list (list int) {valid_cnf_formula r}
    = [[neg_var_to_lit v; pos_var_to_lit v1];
       [neg_var_to_lit v; pos_var_to_lit v2];
       [neg_var_to_lit v1; neg_var_to_lit v2; pos_var_to_lit v]]


let and_clauses_up_to (v1:int) (v2:int) (v:int) (n:nat)
    : Lemma (requires valid_variable v1 && valid_variable v2 && valid_variable v &&
                      n > v1 && n > v2 && n > v)
            (ensures variables_up_to_cnf_formula (and_clauses v1 v2 v) n)
    = ()


let lemma_and_clauses (v1:int) (v2:int) (v:int) (tau : list bool)
    : Lemma (requires valid_variable v1 && valid_variable v2 && valid_variable v &&
                      L.length tau > v1 && L.length tau > v2 && L.length tau > v)
            (ensures variables_up_to_cnf_formula (and_clauses v1 v2 v) (L.length tau) /\
                     truth_value_cnf_formula (and_clauses v1 v2 v) tau <==>
                        ((truth_value_literal (pos_var_to_lit v1) tau && 
                        truth_value_literal (pos_var_to_lit v2) tau) <==>
                        truth_value_literal (pos_var_to_lit v) tau))
    = and_clauses_up_to v1 v2 v (L.length tau)


let and_clauses_in_interval (v1:int) (v2:int) (v:int) (n:nat) (start_interval:nat) (mid:nat) (end_interval:nat)
    : Lemma (requires n <= start_interval && start_interval <= mid && mid <= v &&
                      valid_variable v1 && valid_variable v2 && valid_variable v &&
                      variable_in_interval v1 n start_interval mid &&
                      variable_in_interval v2 n mid v &&
                      end_interval = v + 1)
            (ensures variables_in_interval (and_clauses v1 v2 v) n start_interval end_interval)
    = ()


#set-options "--split_queries always"
let prove_same_value_can_extend_and (f1:formula_t) (rf1 : list (list int)) (v1:int)
                         (f2:formula_t) (rf2 : list (list int)) (v2:int)
                         (n:nat) (start_interval:nat) (mid:nat) (v:int) (end_interval:nat)
                         (rf : list (list int))
    : Lemma (requires n <= start_interval /\ start_interval <= mid /\ mid <= v /\
                      valid f1 rf1 v1 n start_interval mid /\
                      tseitin_same_value f1 rf1 v1 n start_interval mid /\
                      valid f2 rf2 v2 n mid v /\
                      tseitin_same_value f2 rf2 v2 n mid v /\
                      rf = rf1 @ rf2 @ (and_clauses v1 v2 v) /\
                      end_interval = v + 1)
            (ensures valid (And f1 f2) rf v n start_interval end_interval /\
                     tseitin_same_value (And f1 f2) rf v n start_interval end_interval /\
                     tseitin_can_extend (And f1 f2) rf v n start_interval end_interval)
    = LP.append_assoc rf1 rf2 (and_clauses v1 v2 v);
      append_valid_cnf_formulas rf1 rf2;
      append_valid_cnf_formulas (rf1 @ rf2) (and_clauses v1 v2 v);

      variables_in_interval_monotone rf1 n start_interval start_interval mid end_interval;
      variables_in_interval_monotone rf2 n mid start_interval v end_interval;

      and_clauses_in_interval v1 v2 v n start_interval mid end_interval;
      append_variables_in_interval rf1 rf2 n start_interval end_interval;
      append_variables_in_interval (rf1 @ rf2) (and_clauses v1 v2 v) n start_interval end_interval;

      assert (valid (And f1 f2) rf v n start_interval end_interval);

      let aux (tau : list bool) 
          : Lemma (requires L.length tau >= end_interval &&
                            variables_up_to_cnf_formula rf (L.length tau) &&
                            truth_value_cnf_formula rf tau)
                  (ensures variables_up_to (And f1 f2) (L.length tau) &&
                           variables_up_to_literal (pos_var_to_lit v) (L.length tau) &&truth_value_literal (pos_var_to_lit v) tau = truth_value (And f1 f2) tau)
          = assert (variables_up_to_cnf_formula rf (L.length tau));

            variables_up_to_monotone f1 n (L.length tau);
            variables_up_to_monotone f2 n (L.length tau);
            assert (variables_up_to_cnf_formula rf1 (L.length tau));
            assert (variables_up_to_cnf_formula rf2 (L.length tau));
            assert (variables_up_to_cnf_formula (and_clauses v1 v2 v) (L.length tau));
           
            append_valid_cnf_formulas rf2 (and_clauses v1 v2 v);
            append_variables_in_interval rf2 (and_clauses v1 v2 v) n start_interval end_interval;
            assert (variables_in_interval (rf2 @ (and_clauses v1 v2 v)) n start_interval end_interval);
            assert (variables_up_to_cnf_formula (rf2 @ (and_clauses v1 v2 v)) (L.length tau));

            true_parts_of_cnf_formula (rf1 @ rf2) (and_clauses v1 v2 v) tau;
            true_parts_of_cnf_formula rf1 (rf2 @ (and_clauses v1 v2 v)) tau;
            true_parts_of_cnf_formula rf1 rf2 tau;

            lemma_and_clauses v1 v2 v tau
      in
      forall_intro (move_requires aux)
#reset-options
