module AuxLemma

open TseitinCore
open FormulaT
open CnfFormula
module L = FStar.List.Tot.Base
open FStar.Tactics
open FStar.Calc



let dimplies_clauses_aux (v1:int {valid_variable v1}) 
                     (v2:int {valid_variable v2}) 
                     (v:int {valid_variable v}) 
    : r : list (list int) {valid_cnf_formula r /\ L.length r = 4 /\ r = [L.index r 0; L.index r 1; L.index r 2; L.index r 3] /\ L.index r 0 = [neg_var_to_lit v; neg_var_to_lit v1; pos_var_to_lit v2] /\
    L.index r 1 = [neg_var_to_lit v1; neg_var_to_lit v2; pos_var_to_lit v] /\
    L.index r 2 = [pos_var_to_lit v1; pos_var_to_lit v2; pos_var_to_lit v] /\
    L.index r 3 = [neg_var_to_lit v; neg_var_to_lit v2; pos_var_to_lit v1]}
    = [[neg_var_to_lit v; neg_var_to_lit v1; pos_var_to_lit v2];
       [neg_var_to_lit v1; neg_var_to_lit v2; pos_var_to_lit v];
       [pos_var_to_lit v1; pos_var_to_lit v2; pos_var_to_lit v];
       [neg_var_to_lit v; neg_var_to_lit v2; pos_var_to_lit v1]]


// #set-options "--initial_fuel 20 --initial_ifuel 20"
let lemma_aux (v1:int) (v2:int) (v:int) (tau : list bool)
    : Lemma (requires valid_variable v1 && valid_variable v2 && valid_variable v &&
                      L.length tau > v1 && L.length tau > v2 && L.length tau > v)
            (ensures True)
    = let rf = dimplies_clauses_aux v1 v2 v in
      dimplies_clauses_up_to v1 v2 v (L.length tau);
      assert (forall clause . L.mem clause rf ==> (variables_up_to_clause clause (L.length tau)));
      assert (rf = [L.index rf 0; L.index rf 1; L.index rf 2; L.index rf 3]) by compute ();
      assert (truth_value_cnf_formula rf tau <==>
                truth_value_clause (L.index rf 0) tau &&
                truth_value_clause (L.index rf 1) tau &&
                truth_value_clause (L.index rf 2) tau &&
                truth_value_clause (L.index rf 3) tau) by compute ();
      assert (L.index rf 0 = [neg_var_to_lit v; neg_var_to_lit v1; pos_var_to_lit v2]) by compute ();
      assert (truth_value_clause (L.index rf 0) tau <==>
                truth_value_literal (L.index (L.index rf 0) 0) tau ||
                truth_value_literal (L.index (L.index rf 0) 1) tau ||
                truth_value_literal (L.index (L.index rf 0) 2) tau) by compute ();
      assert (truth_value_clause (L.index rf 1) tau <==>
                truth_value_literal (L.index (L.index rf 1) 0) tau ||
                truth_value_literal (L.index (L.index rf 1) 1) tau ||
                truth_value_literal (L.index (L.index rf 1) 2) tau) by compute ();
      assert (truth_value_clause (L.index rf 2) tau <==>
                truth_value_literal (L.index (L.index rf 2) 0) tau ||
                truth_value_literal (L.index (L.index rf 2) 1) tau ||
                truth_value_literal (L.index (L.index rf 2) 2) tau) by compute ();
      assert (truth_value_clause (L.index rf 3) tau <==>
                truth_value_literal (L.index (L.index rf 3) 0) tau ||
                truth_value_literal (L.index (L.index rf 3) 1) tau ||
                truth_value_literal (L.index (L.index rf 3) 2) tau) by compute ()
// #reset-options