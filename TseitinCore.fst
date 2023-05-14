module TseitinCore

open FStar.List.Tot
module L = FStar.List.Tot.Base
module LP = FStar.List.Tot.Properties
open FormulaT
open CnfFormula
open Utils



let extend (tau : list bool) (tau' : list bool) (n:nat) (start_interval:nat) (end_interval:nat)
    : Pure (list bool) (requires n <= start_interval && 
                                 start_interval <= end_interval && 
                                 L.length tau = n && 
                                 L.length tau' = end_interval - start_interval)
                       (ensures fun r -> (L.length r = end_interval && 
                                          interval_of_list r 0 n = tau &&
                                          interval_of_list r start_interval end_interval = tau'))
    = let falses = n_falses (start_interval - n) in
      let r = tau @ falses @ tau' in 
      LP.append_assoc tau falses tau';
      LP.append_length tau falses;
      LP.append_length (tau @ falses) tau';
      same_values_append [] tau (falses @ tau');
      assert (interval_of_list r 0 n = tau);
      same_values_append (tau @ falses) tau' [];
      r


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


let not_clauses (v1:int {valid_variable v1})
                (v:int {valid_variable v})
    : r : list (list int) {valid_cnf_formula r}
    = [[neg_var_to_lit v; neg_var_to_lit v1];
       [pos_var_to_lit v1; pos_var_to_lit v]]


let or_clauses (v1:int {valid_variable v1}) 
               (v2:int {valid_variable v2}) 
               (v:int {valid_variable v}) 
    : r : list (list int) {valid_cnf_formula r}
    = [[neg_var_to_lit v; pos_var_to_lit v1; pos_var_to_lit v2];
       [neg_var_to_lit v1; pos_var_to_lit v];
       [neg_var_to_lit v2; pos_var_to_lit v]]


let and_clauses (v1:int {valid_variable v1}) 
                (v2:int {valid_variable v2}) 
                (v:int {valid_variable v}) 
    : r : list (list int) {valid_cnf_formula r}
    = [[neg_var_to_lit v; pos_var_to_lit v1];
       [neg_var_to_lit v; pos_var_to_lit v2];
       [neg_var_to_lit v1; neg_var_to_lit v2; pos_var_to_lit v]]


let implies_clauses (v1:int {valid_variable v1}) 
                    (v2:int {valid_variable v2}) 
                    (v:int {valid_variable v}) 
    : r : list (list int) {valid_cnf_formula r}
    = [[neg_var_to_lit v; neg_var_to_lit v1; pos_var_to_lit v2];
       [pos_var_to_lit v1; pos_var_to_lit v];
       [neg_var_to_lit v2; pos_var_to_lit v]]


let dimplies_clauses (v1:int {valid_variable v1}) 
                     (v2:int {valid_variable v2}) 
                     (v:int {valid_variable v}) 
    : r : list (list int) {valid_cnf_formula r}
    = [[neg_var_to_lit v; neg_var_to_lit v1; pos_var_to_lit v2];
       [neg_var_to_lit v1; neg_var_to_lit v2; pos_var_to_lit v];
       [pos_var_to_lit v1; pos_var_to_lit v2; pos_var_to_lit v];
       [neg_var_to_lit v; neg_var_to_lit v2; pos_var_to_lit v1]]


let combine (tau : list bool) (tau1 : list bool) (tau2 : list bool) (n:nat) 
            (start_interval:nat) (mid:nat) (end_interval:nat) (last:bool)
    : Pure (list bool) (requires n <= start_interval && start_interval <= mid && mid <= end_interval &&
                                 L.length tau = n && L.length tau1 = mid && L.length tau2 = end_interval)
                       (ensures fun r -> (L.length r = end_interval + 1 &&
                                          interval_of_list r 0 n = tau &&
                                          interval_of_list r start_interval mid = interval_of_list tau1 start_interval mid &&
                                          interval_of_list r mid end_interval = interval_of_list tau2 mid end_interval && 
                                          interval_of_list r end_interval (end_interval + 1) = [last]))
    = let falses = n_falses (start_interval - n) in
      let from_tau1 = interval_of_list tau1 start_interval mid in
      let from_tau2 = interval_of_list tau2 mid end_interval in
      let l1 = tau @ falses in
      let l2 = l1 @ from_tau1 in
      let l3 = l2 @ from_tau2 in
      let r = l3 @ [last] in

      LP.append_assoc tau falses from_tau1;
      LP.append_assoc tau falses (from_tau1 @ from_tau2);
      LP.append_assoc tau falses (from_tau1 @ from_tau2 @ [last]);

      LP.append_assoc l1 from_tau1 from_tau2;
      LP.append_assoc l1 from_tau1 (from_tau2 @ [last]);

      LP.append_assoc l2 from_tau2 [last];

      LP.append_length tau falses;
      LP.append_length l1 from_tau1;
      LP.append_length l2 from_tau2;
      LP.append_length l3 [last];

      assert (r = [] @ tau @ (falses @ from_tau1 @ from_tau2 @ [last]));
      same_values_append [] tau (falses @ from_tau1 @ from_tau2 @ [last]);

      assert (r = l1 @ from_tau1 @ (from_tau2 @ [last]));
      same_values_append l1 from_tau1 (from_tau2 @ [last]);

      assert (r = l2 @ from_tau2 @ [last]);
      same_values_append l2 from_tau2 [last];

      assert (r = l3 @ [last] @ []);
      same_values_append l3 [last] [];

      r


let combine1 (tau : list bool) (tau1 : list bool) (n:nat) (start_interval:nat)
             (end_interval:nat) (v:int) (last:bool)
    : Pure (list bool) (requires n <= start_interval &&
                                 start_interval <= v &&
                                 L.length tau = n &&
                                 L.length tau1 = v)
                       (ensures fun r -> (L.length r = v + 1 &&
                                          interval_of_list r 0 n = tau &&
                                          interval_of_list r start_interval v = interval_of_list tau1 start_interval v &&
                                          interval_of_list r v (v + 1) = [last]))
    = let falses =  n_falses (start_interval - n) in
      let from_tau1 = interval_of_list tau1 start_interval v in
      let l1 = tau @ falses in
      let l2 = l1 @ from_tau1 in
      let r = l2 @ [last] in

      LP.append_assoc tau falses from_tau1;
      LP.append_assoc tau falses (from_tau1 @ [last]);
      LP.append_assoc l1 from_tau1 [last];

      LP.append_length tau falses;
      LP.append_length l1 from_tau1;
      LP.append_length l2 [last];

      assert (r = [] @ tau @ (falses @ from_tau1 @ [last]));
      same_values_append [] tau (falses @ from_tau1 @ [last]);

      assert (r = l1 @ from_tau1 @ [last]);
      same_values_append l1 from_tau1 [last];

      assert (r = l2 @ [last] @ []);
      same_values_append l2 [last] [];

      r


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
               ((not (truth_value_literal (pos_var_to_lit v1) tau)) <==> 
               truth_value_literal (pos_var_to_lit v) tau))
    = let rf = not_clauses v1 v in
      assert (truth_value_cnf_formula rf tau <==> 
                truth_value_clause (L.index rf 0) tau /\
                truth_value_clause (L.index rf 1) tau);
      assert (truth_value_clause (L.index rf 0) tau <==>
                truth_value_literal (L.index (L.index rf 0) 0) tau ||
                truth_value_literal (L.index (L.index rf 0) 1) tau);
      assert (truth_value_clause (L.index rf 1) tau <==>
                truth_value_literal (L.index (L.index rf 1) 0) tau ||
                truth_value_literal (L.index (L.index rf 1) 1) tau)


let lemma_or_clauses (v1:int) (v2:int) (v:int) (tau : list bool)
    : Lemma (requires valid_variable v1 && valid_variable v2 && valid_variable v &&
                      L.length tau > v1 && L.length tau > v2 && L.length tau > v)
            (ensures variables_up_to_cnf_formula (or_clauses v1 v2 v) (L.length tau) /\
                     truth_value_cnf_formula (or_clauses v1 v2 v) tau <==>
                  ((truth_value_literal (pos_var_to_lit v1) tau || 
                  truth_value_literal (pos_var_to_lit v2) tau) <==>
                  truth_value_literal (pos_var_to_lit v) tau))
    = let rf = or_clauses v1 v2 v in
      assert (truth_value_cnf_formula rf tau <==>
                truth_value_clause (L.index rf 0) tau /\
                truth_value_clause (L.index rf 1) tau /\
                truth_value_clause (L.index rf 2) tau);
      assert (truth_value_clause (L.index rf 0) tau <==>
                truth_value_literal (L.index (L.index rf 0) 0) tau ||
                truth_value_literal (L.index (L.index rf 0) 1) tau ||
                truth_value_literal (L.index (L.index rf 0) 2) tau);
      assert (truth_value_clause (L.index rf 1) tau <==>
                truth_value_literal (L.index (L.index rf 1) 0) tau ||
                truth_value_literal (L.index (L.index rf 1) 1) tau);
      assert (truth_value_clause (L.index rf 2) tau <==>
                truth_value_literal (L.index (L.index rf 2) 0) tau ||
                truth_value_literal (L.index (L.index rf 2) 1) tau)
                  

let lemma_and_clauses (v1:int) (v2:int) (v:int) (tau : list bool)
    : Lemma (requires valid_variable v1 && valid_variable v2 && valid_variable v &&
                      L.length tau > v1 && L.length tau > v2 && L.length tau > v)
            (ensures variables_up_to_cnf_formula (and_clauses v1 v2 v) (L.length tau) /\
                     truth_value_cnf_formula (and_clauses v1 v2 v) tau <==>
                  ((truth_value_literal (pos_var_to_lit v1) tau && 
                  truth_value_literal (pos_var_to_lit v2) tau) <==>
                  truth_value_literal (pos_var_to_lit v) tau))
    = let rf = and_clauses v1 v2 v in
      assert (truth_value_cnf_formula rf tau <==>
                truth_value_clause (L.index rf 0) tau /\
                truth_value_clause (L.index rf 1) tau /\
                truth_value_clause (L.index rf 2) tau);
      assert (truth_value_clause (L.index rf 0) tau <==>
                truth_value_literal (L.index (L.index rf 0) 0) tau ||
                truth_value_literal (L.index (L.index rf 0) 1) tau);
      assert (truth_value_clause (L.index rf 1) tau <==>
                truth_value_literal (L.index (L.index rf 1) 0) tau ||
                truth_value_literal (L.index (L.index rf 1) 1) tau);
      assert (truth_value_clause (L.index rf 2) tau <==>
                truth_value_literal (L.index (L.index rf 2) 0) tau ||
                truth_value_literal (L.index (L.index rf 2) 1) tau ||
                truth_value_literal (L.index (L.index rf 2) 2) tau)
        

let lemma_implies_clauses (v1:int) (v2:int) (v:int) (tau : list bool)
    : Lemma (requires valid_variable v1 && valid_variable v2 && valid_variable v &&
                      L.length tau > v1 && L.length tau > v2 && L.length tau > v)
            (ensures variables_up_to_cnf_formula (implies_clauses v1 v2 v) (L.length tau) /\
                     truth_value_cnf_formula (implies_clauses v1 v2 v) tau <==>
                  ((truth_value_literal (pos_var_to_lit v1) tau ==> 
                  truth_value_literal (pos_var_to_lit v2) tau) <==>
                  truth_value_literal (pos_var_to_lit v) tau))
    = let rf = implies_clauses v1 v2 v in
      assert (truth_value_cnf_formula rf tau <==>
                truth_value_clause (L.index rf 0) tau /\
                truth_value_clause (L.index rf 1) tau /\
                truth_value_clause (L.index rf 2) tau);
      assert (truth_value_clause (L.index rf 0) tau <==>
                truth_value_literal (L.index (L.index rf 0) 0) tau ||
                truth_value_literal (L.index (L.index rf 0) 1) tau ||
                truth_value_literal (L.index (L.index rf 0) 2) tau);
      assert (truth_value_clause (L.index rf 1) tau <==>
                truth_value_literal (L.index (L.index rf 1) 0) tau ||
                truth_value_literal (L.index (L.index rf 1) 1) tau);
      assert (truth_value_clause (L.index rf 2) tau <==>
                truth_value_literal (L.index (L.index rf 2) 0) tau ||
                truth_value_literal (L.index (L.index rf 2) 1) tau)


let lemma_dimplies_clauses (v1:int) (v2:int) (v:int) (tau : list bool)
    : Lemma (requires valid_variable v1 && valid_variable v2 && valid_variable v &&
                      L.length tau > v1 && L.length tau > v2 && L.length tau > v)
            (ensures variables_up_to_cnf_formula (dimplies_clauses v1 v2 v) (L.length tau) /\
                     truth_value_cnf_formula (dimplies_clauses v1 v2 v) tau <==>
                  ((truth_value_literal (pos_var_to_lit v1) tau <==> 
                  truth_value_literal (pos_var_to_lit v2) tau) <==>
                  truth_value_literal (pos_var_to_lit v) tau))
    = let rf = dimplies_clauses v1 v2 v in
      //assert (variables_up_to_cnf_formula rf (L.length tau));
      assert (truth_value_cnf_formula rf tau <==>
                truth_value_clause (L.index rf 0) tau /\
                truth_value_clause (L.index rf 1) tau /\
                truth_value_clause (L.index rf 2) tau /\
                truth_value_clause (L.index rf 3) tau );
      assert (truth_value_clause (L.index rf 0) tau <==>
                truth_value_literal (L.index (L.index rf 0) 0) tau ||
                truth_value_literal (L.index (L.index rf 0) 1) tau ||
                truth_value_literal (L.index (L.index rf 0) 2) tau);
      assert (truth_value_clause (L.index rf 1) tau <==>
                truth_value_literal (L.index (L.index rf 1) 0) tau ||
                truth_value_literal (L.index (L.index rf 1) 1) tau ||
                truth_value_literal (L.index (L.index rf 1) 2) tau);
      assert (truth_value_clause (L.index rf 2) tau <==>
                truth_value_literal (L.index (L.index rf 2) 0) tau ||
                truth_value_literal (L.index (L.index rf 2) 1) tau ||
                truth_value_literal (L.index (L.index rf 2) 2) tau);
      assert (truth_value_clause (L.index rf 3) tau <==>
                truth_value_literal (L.index (L.index rf 3) 0) tau ||
                truth_value_literal (L.index (L.index rf 3) 1) tau ||
                truth_value_literal (L.index (L.index rf 3) 2) tau)
