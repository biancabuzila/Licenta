module TseitinCore

open FStar.List.Tot
module L = FStar.List.Tot.Base
module LP = FStar.List.Tot.Properties
open Utils
open FormulaT
open CnfFormula



let valid (f:formula_t) (rf : list (list int)) (v:int) (n:nat) (start_interval:nat) (end_interval:nat)
    = n <= start_interval /\ start_interval <= end_interval /\
      variables_up_to f n /\ valid_cnf_formula rf /\ valid_variable v /\
      variable_in_interval v n start_interval end_interval /\
      variables_in_interval rf n start_interval end_interval


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
      assert (L.length r = end_interval);
      interval_append_fst tau (falses @ tau');
      assert (interval_of_list r 0 n = tau);
      same_values_append (tau @ falses) tau' [];
      assert (interval_of_list r start_interval end_interval = tau');
      r


let can_extend (tau : list bool) 
               (f:formula_t) 
               (rf : list (list int)) 
               (v:int) 
               (n:nat {L.length tau = n}) 
               (start_interval:nat) 
               (end_interval:nat {valid f rf v n start_interval end_interval})
    = exists (tau' : list bool) . (is_prefix tau tau' && L.length tau' = end_interval) ==> 
        (truth_value_cnf_formula rf tau' &&
        truth_value f tau = truth_value_literal (pos_var_to_lit v) tau')


let tseitin_can_extend (f:formula_t) (rf : list (list int)) (v:int) (n:nat) (start_interval:nat) 
                       (end_interval:nat {valid f rf v n start_interval end_interval})
    = forall (tau : list bool) . L.length tau = n ==> can_extend tau f rf v n start_interval end_interval


let tseitin_same_value (f:formula_t) (rf : list (list int)) (v:int) (n:nat) (start_interval:nat)
                       (end_interval:nat {valid f rf v n start_interval end_interval})
    = forall (tau : list bool) . L.length tau >= end_interval && truth_value_cnf_formula rf tau ==> 
      (
         variables_up_to_monotone f n (L.length tau);
         truth_value_literal (pos_var_to_lit v) tau = truth_value f tau
      )
