module LemmasForClauses.ImpliesClauses

open FStar.List.Tot
module L = FStar.List.Tot.Base
module LP = FStar.List.Tot.Properties
open FStar.Classical
open FormulaT
open CnfFormula
open TseitinCore



let implies_clauses (v1:int {valid_variable v1}) 
                    (v2:int {valid_variable v2}) 
                    (v:int {valid_variable v}) 
    : r : list (list int) {valid_cnf_formula r}
    = [[neg_var_to_lit v; neg_var_to_lit v1; pos_var_to_lit v2];
       [pos_var_to_lit v1; pos_var_to_lit v];
       [neg_var_to_lit v2; pos_var_to_lit v]]


let implies_clauses_up_to (v1:int) (v2:int) (v:int) (n:nat)
    : Lemma (requires valid_variable v1 && valid_variable v2 && valid_variable v &&
                      n > v1 && n > v2 && n > v)
            (ensures variables_up_to_cnf_formula (implies_clauses v1 v2 v) n)
    = ()

   
let lemma_implies_clauses (v1:int) (v2:int) (v:int) (tau : list bool)
    : Lemma (requires valid_variable v1 && valid_variable v2 && valid_variable v &&
                      L.length tau > v1 && L.length tau > v2 && L.length tau > v)
            (ensures variables_up_to_cnf_formula (implies_clauses v1 v2 v) (L.length tau) /\
                     truth_value_cnf_formula (implies_clauses v1 v2 v) tau <==>
                        ((truth_value_literal (pos_var_to_lit v1) tau ==> 
                        truth_value_literal (pos_var_to_lit v2) tau) <==>
                        truth_value_literal (pos_var_to_lit v) tau))
    = implies_clauses_up_to v1 v2 v (L.length tau)


let implies_clauses_in_interval (v1:int) (v2:int) (v:int) (n:nat) (start_interval:nat) (mid:nat) (end_interval:nat)
    : Lemma (requires n <= start_interval && start_interval <= mid && mid <= v &&
                      valid_variable v1 && valid_variable v2 && valid_variable v &&
                      variable_in_interval v1 n start_interval mid &&
                      variable_in_interval v2 n mid v &&
                      end_interval = v + 1)
            (ensures variables_in_interval (implies_clauses v1 v2 v) n start_interval end_interval)
    = ()


let prove_same_value_implies (f1:formula_t) (rf1 : list (list int)) (v1:int)
                             (f2:formula_t) (rf2 : list (list int)) (v2:int)
                             (n:nat) (start_interval:nat) (mid:nat) (v:int)(end_interval:nat)
                             (rf : list (list int))
    : Lemma (requires n <= start_interval /\ start_interval <= mid /\ mid <= v /\
                      valid f1 rf1 v1 n start_interval mid /\
                      tseitin_same_value f1 rf1 v1 n start_interval mid /\
                      valid f2 rf2 v2 n mid v /\
                      tseitin_same_value f2 rf2 v2 n mid v /\
                      rf = rf1 @ rf2 @ (implies_clauses v1 v2 v) /\
                      end_interval = v + 1)
            (ensures valid (Implies f1 f2) rf v n start_interval end_interval /\
                     tseitin_same_value (Implies f1 f2) rf v n start_interval end_interval)
    = LP.append_assoc rf1 rf2 (implies_clauses v1 v2 v);
      append_valid_cnf_formulas rf1 rf2;
      append_valid_cnf_formulas (rf1 @ rf2) (implies_clauses v1 v2 v);

      variables_in_interval_monotone rf1 n start_interval start_interval mid end_interval;
      variables_in_interval_monotone rf2 n mid start_interval v end_interval;

      implies_clauses_in_interval v1 v2 v n start_interval mid end_interval;
      append_variables_in_interval rf1 rf2 n start_interval end_interval;
      append_variables_in_interval (rf1 @ rf2) (implies_clauses v1 v2 v) n start_interval end_interval;

      assert (valid (Implies f1 f2) rf v n start_interval end_interval);

      let aux (tau : list bool) 
          : Lemma (requires L.length tau >= end_interval /\
                            truth_value_cnf_formula rf tau)
                  (ensures variables_up_to (Implies f1 f2) (L.length tau) &&
                           variables_up_to_literal (pos_var_to_lit v) (L.length tau) &&truth_value_literal (pos_var_to_lit v) tau = truth_value (Implies f1 f2) tau)
          = assert (variables_up_to_cnf_formula rf (L.length tau));
            variables_up_to_monotone f1 n (L.length tau);
            variables_up_to_monotone f2 n (L.length tau);
            assert (truth_value_literal (pos_var_to_lit v1) tau = truth_value f1 tau);
            assert (truth_value_literal (pos_var_to_lit v2) tau = truth_value f2 tau);
            lemma_implies_clauses v1 v2 v tau;
            assert (truth_value_literal (pos_var_to_lit v) tau = truth_value (Implies f1 f2) tau)
      in
      forall_intro (move_requires aux)


let prove_can_extend_implies (f1:formula_t) (rf1 : list (list int)) (v1:int) 
                             (f2:formula_t) (rf2 : list (list int)) (v2:int) 
                             (n:nat) (start_interval:nat) (mid:nat) (v:int) (end_interval:nat)
                             (rf :list (list int))
    : Lemma (requires n <= start_interval /\ start_interval <= mid /\ mid <= v /\
                      valid f1 rf1 v1 n start_interval mid /\
                      tseitin_can_extend f1 rf1 v1 n start_interval mid /\
                      valid f2 rf2 v2 n mid v /\
                      tseitin_can_extend f2 rf2 v2 n mid v /\
                      rf = rf1 @ rf2 @ (implies_clauses v1 v2 v) /\
                      end_interval = v + 1)
            (ensures valid (Implies f1 f2) rf v n start_interval end_interval /\
                     tseitin_can_extend (Implies f1 f2) rf v n start_interval end_interval)
    = LP.append_assoc rf1 rf2 (implies_clauses v1 v2 v);
      append_valid_cnf_formulas rf1 rf2;
      append_valid_cnf_formulas (rf1 @ rf2) (implies_clauses v1 v2 v);

      variables_in_interval_monotone rf1 n start_interval start_interval mid end_interval;
      variables_in_interval_monotone rf2 n mid start_interval v end_interval;

      implies_clauses_in_interval v1 v2 v n start_interval mid end_interval;
      append_variables_in_interval rf1 rf2 n start_interval end_interval;
      append_variables_in_interval (rf1 @ rf2) (implies_clauses v1 v2 v) n start_interval end_interval;
      
      assert (valid (Implies f1 f2) rf v n start_interval end_interval)

    //   let aux (tau : list bool) 
    //       : Lemma (requires L.length tau = n)
    //               (ensures L.length tau = n /\
    //                        can_extend tau (Implies f1 f2) rf v n start_interval end_interval)
    //       = let conditions1 (tau1 : list bool) : Tot bool =
    //             is_prefix tau tau1 &&
    //             L.length tau1 = mid &&
    //             truth_value_cnf_formula rf1 tau1 &&
    //             truth_value f1 tau = truth_value_literal (pos_var_to_lit v1) tau1
    //         in
    //         assume (exists x . conditions1 x);
    //         let tau1 = extract_value conditions1 in
    //         assert (is_prefix tau tau1);
    //         assert (L.length tau1 = mid);

    //         let conditions2 (tau2 : list bool) : Tot bool =
    //             is_prefix tau tau2 &&
    //             L.length tau2 = v &&
    //             truth_value_cnf_formula rf2 tau2 &&
    //             truth_value f2 tau = truth_value_literal (pos_var_to_lit v2) tau2
    //         in
    //         assume (exists x . conditions2 x);
    //         let tau2 = extract_value conditions2 in
    //         assert (is_prefix tau tau2);
    //         assert (L.length tau2 = v);


    //         let tau' = combine tau tau1 tau2 n start_interval mid v (truth_value (Implies f1 f2) tau) in
    //         assert (L.length tau' = v + 1);

    //         // assert (interval_of_list tau' 0 n = interval_of_list tau 0 n);
    //         assert (interval_of_list tau' start_interval mid = interval_of_list tau1 start_interval mid);
    //         assert (interval_of_list tau' mid v = interval_of_list tau2 mid v);
    //         assert (L.index tau' v = truth_value (Implies f1 f2) tau);

    //         assert (truth_value_literal (pos_var_to_lit v) tau' = truth_value (Implies f1 f2) tau);
    //         assert (truth_value_literal (neg_var_to_lit v) tau' = not (truth_value (Implies f1 f2) tau));

    //         is_prefix_then_is_interval tau tau1;
    //         transfer_truth_value rf1 tau1 tau' n start_interval mid;
    //         is_prefix_then_is_interval tau tau2;
    //         transfer_truth_value rf2 tau2 tau' n mid v;

    //         transfer_truth_value_lit (pos_var_to_lit v1) tau1 tau' n start_interval mid;
    //         // assert (truth_value_literal (pos_var_to_lit v1) tau' = truth_value f1 tau);
    //         transfer_truth_value_lit (neg_var_to_lit v1) tau1 tau' n start_interval mid;
    //         // assert (truth_value_literal (neg_var_to_lit v1) tau' = not (truth_value f1 tau));
            
    //         transfer_truth_value_lit (pos_var_to_lit v2) tau2 tau' n mid v;
    //         // assert (truth_value_literal (pos_var_to_lit v2) tau' = truth_value f2 tau);
    //         transfer_truth_value_lit (neg_var_to_lit v2) tau2 tau' n mid v;
    //         // assert (truth_value_literal (neg_var_to_lit v2) tau' = not (truth_value f1 tau));

    //         // assert (truth_value (Implies f1 f2) tau = (truth_value f1 tau ==> truth_value f2 tau));

    //         lemma_implies_clauses v1 v2 v tau';
    //         assert (can_extend tau (Implies f1 f2) rf v n start_interval end_interval)
    //   in
    //   forall_intro (move_requires aux)
