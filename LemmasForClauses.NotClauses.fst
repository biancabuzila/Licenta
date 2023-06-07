module LemmasForClauses.NotClauses

open FStar.List.Tot
module L = FStar.List.Tot.Base
open FStar.Classical
open FormulaT
open CnfFormula
open TseitinCore



let not_clauses (v1:int {valid_variable v1})
                (v:int {valid_variable v})
    : r : list (list int) {valid_cnf_formula r}
    = [[neg_var_to_lit v; neg_var_to_lit v1];
       [pos_var_to_lit v1; pos_var_to_lit v]]


let not_clauses_up_to (v1:int) (v:int) (n:nat)
    : Lemma (requires valid_variable v1 && valid_variable v &&
                      n > v1 && n > v)
            (ensures variables_up_to_cnf_formula (not_clauses v1 v) n)
    = ()


let lemma_not_clauses (v1:int) (v:int) (tau : list bool)
    : Lemma (requires valid_variable v1 && valid_variable v && L.length tau > v && L.length tau > v1)
            (ensures variables_up_to_cnf_formula (not_clauses v1 v) (L.length tau) /\
                     truth_value_cnf_formula (not_clauses v1 v) tau <==> 
                       ((not (truth_value_literal (pos_var_to_lit v1) tau)) <==> 
                       truth_value_literal (pos_var_to_lit v) tau))
    = not_clauses_up_to v1 v (L.length tau)


let not_clauses_in_interval (v1:int) (v:int) (n:nat) (start_interval:nat) (end_interval:nat)
    : Lemma (requires n <= start_interval /\ start_interval <= v &&
                      valid_variable v1 && valid_variable v &&
                      variable_in_interval v1 n start_interval v &&
                      end_interval = v + 1)
            (ensures variables_in_interval (not_clauses v1 v) n start_interval end_interval)
    = ()


#set-options "--split_queries always"
let prove_same_value_can_extend_not (f1:formula_t) (rf1 : list (list int)) (v1:int) (n:nat)
                         (start_interval:nat) (v:int) (end_interval:nat)
                         (rf : list (list int)) 
    : Lemma (requires n <= start_interval /\ start_interval <= v /\
                      valid f1 rf1 v1 n start_interval v /\
                      tseitin_same_value f1 rf1 v1 n start_interval v /\
                      rf = rf1 @ (not_clauses v1 v) /\
                      end_interval = v + 1)
            (ensures valid (Not f1) rf v n start_interval end_interval /\
                     tseitin_same_value (Not f1) rf v n start_interval end_interval /\
                     tseitin_can_extend (Not f1) rf v n start_interval end_interval)
    = append_valid_cnf_formulas rf1 (not_clauses v1 v);
      variables_in_interval_monotone rf1 n start_interval start_interval v end_interval;
      not_clauses_in_interval v1 v n start_interval end_interval;
      append_variables_in_interval rf1 (not_clauses v1 v) n start_interval end_interval;
      assert (valid (Not f1) rf v n start_interval end_interval);

      let aux (tau : list bool) 
          : Lemma (requires L.length tau >= end_interval &&
                            truth_value_cnf_formula rf tau)
                  (ensures variables_up_to (Not f1) (L.length tau) &&
                           variables_up_to_literal (pos_var_to_lit v) (L.length tau) &&
                           truth_value_literal (pos_var_to_lit v) tau = truth_value (Not f1) tau)
          = variables_up_to_monotone f1 n (L.length tau);
            true_parts_of_cnf_formula rf1 (not_clauses v1 v) tau;
            lemma_not_clauses v1 v tau
      in
      forall_intro (move_requires aux)
#reset-options
