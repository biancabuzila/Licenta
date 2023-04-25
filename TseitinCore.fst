module TseitinCore

module L = FStar.List.Tot.Base
open FormulaT
open CnfFormula
open Utils


let extend (tau : list bool) (tau' : list bool) (n:nat) (start_interval:nat) (end_interval:nat)
    : Pure (list bool) (requires n <= start_interval && 
                                 start_interval <= end_interval && 
                                 L.length tau = n && 
                                 L.length tau' = end_interval - start_interval)
                       (ensures fun r -> (L.length r = end_interval && 
                                          agree r tau 0 n && 
                                          interval_of_list r start_interval end_interval = tau'))
    = let up_to_start = L.append tau (n_falses (start_interval - n)) in
      L.append up_to_start tau'


let valid (f:formula_t) (rf : list (list int)) (v:int) (n:nat) (start_interval:nat) (end_interval:nat)
    = n <= start_interval /\ start_interval <= end_interval /\
      variables_up_to f n /\ valid_cnf_formula rf /\ valid_variable v /\
      variable_in_interval v n start_interval end_interval /\
      variables_in_interval rf n start_interval end_interval


let can_extend (tau : list bool) 
               (f:formula_t) 
               (rf : list (list int)) 
               (v:int) 
               (n:nat {L.length tau = n}) 
               (start_interval:nat) 
               (end_interval:nat {valid f rf v n start_interval end_interval})
    = exists (tau' : list bool) . (L.length tau <= L.length tau' && L.length tau' = end_interval) ==> 
        (truth_value_cnf_formula rf tau' /\
        truth_value f tau = truth_value_literal (pos_var_to_lit v) tau')


let tseitin_can_extend (f:formula_t) (rf : list (list int)) (v:int) (n:nat) (start_interval:nat) 
                       (end_interval:nat {valid f rf v n start_interval end_interval})
    = forall (tau : list bool) . L.length tau = n ==> can_extend tau f rf v n start_interval end_interval


let and_clauses (v1:int {valid_variable v1}) 
                (v2:int {valid_variable v2}) 
                (v:int {valid_variable v}) 
    : list (list int)
    = [[neg_var_to_lit v; pos_var_to_lit v1];
       [neg_var_to_lit v; pos_var_to_lit v2];
       [neg_var_to_lit v1; neg_var_to_lit v2; pos_var_to_lit v]]


let or_clauses (v1:int {valid_variable v1}) 
               (v2:int {valid_variable v2}) 
               (v:int {valid_variable v}) 
    : list (list int)
    = [[neg_var_to_lit v; pos_var_to_lit v1; pos_var_to_lit v2];
       [neg_var_to_lit v1; pos_var_to_lit v];
       [neg_var_to_lit v2; pos_var_to_lit v]]


let implies_clauses (v1:int {valid_variable v1}) 
                    (v2:int {valid_variable v2}) 
                    (v:int {valid_variable v}) 
    : list (list int)
    = [[neg_var_to_lit v; neg_var_to_lit v1; pos_var_to_lit v2];
       [pos_var_to_lit v1; pos_var_to_lit v];
       [neg_var_to_lit v2; pos_var_to_lit v]]


let dimplies_clauses (v1:int {valid_variable v1}) 
                     (v2:int {valid_variable v2}) 
                     (v:int {valid_variable v}) 
    : list (list int)
    = [[neg_var_to_lit v; neg_var_to_lit v1; pos_var_to_lit v2];
       [neg_var_to_lit v1; neg_var_to_lit v1; pos_var_to_lit v];
       [pos_var_to_lit v1; pos_var_to_lit v2; pos_var_to_lit v];
       [neg_var_to_lit v; neg_var_to_lit v2; pos_var_to_lit v1]]


let not_clauses (v1:int {valid_variable v1})
                (v:int {valid_variable v})
    : list (list int)
    = [[neg_var_to_lit v; neg_var_to_lit v1];
       [pos_var_to_lit v1; pos_var_to_lit v]]


let combine (tau : list bool) (tau1 : list bool) (tau2 : list bool) (n:nat) 
            (start_interval:nat) (mid:nat) (end_interval:nat) (last:bool)
    : Pure (list bool) (requires n <= start_interval && start_interval <= mid && mid <= end_interval &&
                                 L.length tau = n && L.length tau1 = mid && L.length tau2 = end_interval)
                       (ensures fun r -> (L.length r = end_interval + 1 &&
                                          agree r tau 0 n &&
                                          agree r tau1 start_interval mid &&
                                          agree r tau2 mid end_interval &&
                                          my_nth r (L.length r - 1) = last))
    = L.append (L.append (L.append (L.append tau (n_falses (start_interval - n))) 
    (interval_of_list tau1 start_interval mid)) (interval_of_list tau2 mid end_interval)) [last]


let combine1 (tau : list bool) (tau1 : list bool) (n:nat) (start_interval:nat)
             (end_interval:nat) (v:int) (last:bool)
    : Pure (list bool) (requires n <= start_interval &&
                                 start_interval <= v &&
                                 L.length tau = n &&
                                 L.length tau1 = v)
                       (ensures fun r -> (L.length r = v + 1 /\
                                          agree r tau 0 n /\
                                          agree r tau1 start_interval v))
    = L.append (L.append (L.append tau (n_falses (start_interval - n))) (interval_of_list tau1 start_interval v)) [last]
   

let tseitin_same_value (f:formula_t) (rf : list (list int)) (v:int) (n:nat) (start_interval:nat)
                       (end_interval:nat {valid f rf v n start_interval end_interval})
    = forall (tau : list bool) . L.length tau >= end_interval /\ truth_value_cnf_formula rf tau ==> 
      (
         variables_up_to_monotone f n (L.length tau);
         truth_value_literal (pos_var_to_lit v) tau = truth_value f tau
      )


let lemma_not_clauses (v1:int) (v:int) (tau : list bool)
    : Lemma (requires valid_variable v1 && valid_variable v && L.length tau > v && L.length tau > v1)
            (ensures truth_value_cnf_formula (not_clauses v1 v) tau <==> 
            ((not (truth_value_literal (pos_var_to_lit v1) tau)) <==> truth_value_literal (pos_var_to_lit v) tau))
    = let rf = not_clauses v1 v in
      assert (truth_value_cnf_formula rf tau <==> 
                truth_value_clause (my_nth rf 0) tau /\
                truth_value_clause (my_nth rf 1) tau);
      assert (truth_value_clause (my_nth rf 0) tau <==>
                truth_value_literal (my_nth (my_nth rf 0) 0) tau ||
                truth_value_literal (my_nth (my_nth rf 0) 1) tau);
      assert (truth_value_clause (my_nth rf 1) tau <==>
                truth_value_literal (my_nth (my_nth rf 1) 0) tau ||
                truth_value_literal (my_nth (my_nth rf 1) 1) tau)
