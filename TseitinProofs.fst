module TseitinProofs

open FStar.List.Tot
module L = FStar.List.Tot.Base
module LP = FStar.List.Tot.Properties
open FStar.Classical
open FStar.Ghost
open CnfFormula
open FormulaT
open Utils
open TseitinCore



let rec append_valid_cnf_formulas (f1 : list (list int)) (f2 : list (list int))
    : Lemma (requires valid_cnf_formula f1 /\ valid_cnf_formula f2)
            (ensures valid_cnf_formula (f1 @ f2))
    = if L.length f1 = 0 then ()
      else append_valid_cnf_formulas (tl f1) f2


let rec append_variables_in_interval (f1 : list (list int)) (f2 : list (list int))
                                     (n:nat) (start_interval:nat) (end_interval:nat)
    : Lemma (requires n <= start_interval /\ start_interval <= end_interval /\
                      valid_cnf_formula f1 /\ valid_cnf_formula f2 /\
                      variables_in_interval f1 n start_interval end_interval /\
                      variables_in_interval f2 n start_interval end_interval)
            (ensures valid_cnf_formula (f1 @ f2) /\ variables_in_interval (f1 @ f2) n start_interval end_interval)
    = append_valid_cnf_formulas f1 f2;
      if f1 = [] then ()
      else 
      (
          append_valid_cnf_formulas (L.tl f1) f2;
          append_variables_in_interval (tl f1) f2 n start_interval end_interval
      )


let prove_same_value_not (f1:formula_t) (rf1 : list (list int)) (v1:int) (n:nat)
                         (start_interval:nat) (end_interval:nat) (rf : list (list int)) (v:int)
    : Lemma (requires n <= start_interval /\ start_interval <= v /\
                      valid f1 rf1 v1 n start_interval v /\
                      tseitin_same_value f1 rf1 v1 n start_interval v /\
                      rf = rf1 @ (not_clauses v1 v) /\
                      end_interval = v + 1)
            (ensures valid (Not f1) rf v n start_interval end_interval /\
                     tseitin_same_value (Not f1) rf v n start_interval end_interval)
    = append_valid_cnf_formulas rf1 (not_clauses v1 v);

      variables_in_interval_monotone rf1 n start_interval v end_interval;
      assert (variables_in_interval rf1 n start_interval end_interval);

      let nc = not_clauses v1 v in
      assert (variables_in_interval_literal (L.index (L.index nc 0) 0) n start_interval end_interval);
      assert (variables_in_interval_literal (L.index (L.index nc 0) 1) n start_interval end_interval);
      assert (variables_in_interval_literal (L.index (L.index nc 1) 0) n start_interval end_interval);
      assert (variables_in_interval_literal (L.index (L.index nc 1) 1) n start_interval end_interval);
      // assert (L.index nc 0 = [L.index (L.index nc 0) 0; L.index (L.index nc 0) 1]);
      assert (L.index nc 0 = [L.index (L.index nc 0) 0; L.index (L.index nc 0) 1] &&
              variables_in_interval_literal (L.index (L.index nc 0) 0) n start_interval end_interval &&
              variables_in_interval_literal (L.index (L.index nc 0) 1) n start_interval end_interval ==>
              variables_in_interval_clause (L.index nc 0) n start_interval end_interval);
      // assert (variables_in_interval_clause (L.index nc 0) n start_interval end_interval);
      assert (L.index nc 1 = [L.index (L.index nc 1) 0; L.index (L.index nc 1) 1]);
      assert (variables_in_interval_clause (L.index nc 1) n start_interval end_interval);
      assert (variables_in_interval nc n start_interval end_interval);

      assert (variables_in_interval (not_clauses v1 v) n start_interval end_interval);

      append_variables_in_interval rf1 (not_clauses v1 v) n start_interval end_interval;
      assert (variables_in_interval rf n start_interval end_interval);
      assert (valid (Not f1) rf v n start_interval end_interval);

      let aux (tau : list bool) 
          : Lemma (requires L.length tau >= end_interval /\
                            truth_value_cnf_formula rf tau)
                  (ensures truth_value_literal (pos_var_to_lit v) tau = truth_value (Not f1) tau)
          = variables_up_to_monotone f1 n (L.length tau);
            assert (truth_value_literal (pos_var_to_lit v1) tau = truth_value f1 tau);
            lemma_not_clauses v1 v tau;
            assert (truth_value_literal (pos_var_to_lit v) tau = truth_value (Not f1) tau)
      in
      forall_intro (move_requires aux)


// let prove_same_value_or (f1:formula_t) (rf1 : list (list int)) (v1:int)
//                         (f2:formula_t) (rf2 : list (list int)) (v2:int)
//                         (n:nat) (start_interval:nat) (mid:nat) (end_interval:nat)
//                         (v:int) (rf : list (list int))
//     : Lemma (requires n <= start_interval /\ start_interval <= mid /\ mid <= v /\
//                       valid f1 rf1 v1 n start_interval mid /\
//                       tseitin_same_value f1 rf1 v1 n start_interval mid /\
//                       valid f2 rf2 v2 n mid v /\
//                       tseitin_same_value f2 rf2 v2 n mid v /\
//                       rf = rf1 @ rf2 @ (or_clauses v1 v2 v) /\
//                       end_interval = v + 1)
//             (ensures valid (Or f1 f2) rf v n start_interval end_interval /\
//                      tseitin_same_value (Or f1 f2) rf v n start_interval end_interval)
//     = LP.append_assoc rf1 rf2 (or_clauses v1 v2 v);
//       append_valid_cnf_formulas rf1 rf2;
//       append_valid_cnf_formulas (rf1 @ rf2) (or_clauses v1 v2 v);
//       // assert (variables_in_interval rf n start_interval end_interval);
//       // assert (valid (Or f1 f2) rf v n start_interval end_interval);

//       let aux (tau : list bool) 
//           : Lemma (requires L.length tau >= end_interval /\
//                             truth_value_cnf_formula rf tau)
//                   (ensures truth_value_literal (pos_var_to_lit v) tau = truth_value (Or f1 f2) tau)
//           = assert (variables_up_to_cnf_formula rf (L.length tau));
//             variables_up_to_monotone f1 n (L.length tau);
//             variables_up_to_monotone f2 n (L.length tau);
//             assert (truth_value_literal (pos_var_to_lit v1) tau = truth_value f1 tau);
//             assert (truth_value_literal (pos_var_to_lit v2) tau = truth_value f2 tau);
//             lemma_or_clauses v1 v2 v tau;
//             assert (truth_value_literal (pos_var_to_lit v) tau = truth_value (Or f1 f2) tau)
//       in
//       forall_intro (move_requires aux)


// let prove_same_value_and (f1:formula_t) (rf1 : list (list int)) (v1:int)
//                          (f2:formula_t) (rf2 : list (list int)) (v2:int)
//                          (n:nat) (start_interval:nat) (mid:nat) (end_interval:nat)
//                          (v:int) (rf : list (list int))
//     : Lemma (requires n <= start_interval /\ start_interval <= mid /\ mid <= v /\
//                       valid f1 rf1 v1 n start_interval mid /\
//                       tseitin_same_value f1 rf1 v1 n start_interval mid /\
//                       valid f2 rf2 v2 n mid v /\
//                       tseitin_same_value f2 rf2 v2 n mid v /\
//                       rf = rf1 @ rf2 @ (and_clauses v1 v2 v) /\
//                       end_interval = v + 1)
//             (ensures valid (And f1 f2) rf v n start_interval end_interval /\
//                      tseitin_same_value (And f1 f2) rf v n start_interval end_interval)
//     = LP.append_assoc rf1 rf2 (and_clauses v1 v2 v);
//       append_valid_cnf_formulas rf1 rf2;
//       append_valid_cnf_formulas (rf1 @ rf2) (and_clauses v1 v2 v);
//       // assert (variables_in_interval rf n start_interval end_interval);
//       // assert (valid (And f1 f2) rf v n start_interval end_interval);

//       let aux (tau : list bool) 
//           : Lemma (requires L.length tau >= end_interval /\
//                             truth_value_cnf_formula rf tau)
//                   (ensures truth_value_literal (pos_var_to_lit v) tau = truth_value (And f1 f2) tau)
//           = assert (variables_up_to_cnf_formula rf (L.length tau));
//             variables_up_to_monotone f1 n (L.length tau);
//             variables_up_to_monotone f2 n (L.length tau);
//             assert (truth_value_literal (pos_var_to_lit v1) tau = truth_value f1 tau);
//             assert (truth_value_literal (pos_var_to_lit v2) tau = truth_value f2 tau);
//             lemma_and_clauses v1 v2 v tau;
//             assert (truth_value_literal (pos_var_to_lit v) tau = truth_value (And f1 f2) tau)
//       in
//       forall_intro (move_requires aux)


// let prove_same_value_implies (f1:formula_t) (rf1 : list (list int)) (v1:int)
//                              (f2:formula_t) (rf2 : list (list int)) (v2:int)
//                              (n:nat) (start_interval:nat) (mid:nat) (end_interval:nat)
//                              (v:int) (rf : list (list int))
//     : Lemma (requires n <= start_interval /\ start_interval <= mid /\ mid <= v /\
//                       valid f1 rf1 v1 n start_interval mid /\
//                       tseitin_same_value f1 rf1 v1 n start_interval mid /\
//                       valid f2 rf2 v2 n mid v /\
//                       tseitin_same_value f2 rf2 v2 n mid v /\
//                       rf = rf1 @ rf2 @ (implies_clauses v1 v2 v) /\
//                       end_interval = v + 1)
//             (ensures valid (Implies f1 f2) rf v n start_interval end_interval /\
//                      tseitin_same_value (Implies f1 f2) rf v n start_interval end_interval)
//     = LP.append_assoc rf1 rf2 (implies_clauses v1 v2 v);
//       append_valid_cnf_formulas rf1 rf2;
//       append_valid_cnf_formulas (rf1 @ rf2) (implies_clauses v1 v2 v);
//       // assert (variables_in_interval rf n start_interval end_interval);
//       // assert (valid (Implies f1 f2) rf v n start_interval end_interval);

//       let aux (tau : list bool) 
//           : Lemma (requires L.length tau >= end_interval /\
//                             truth_value_cnf_formula rf tau)
//                   (ensures truth_value_literal (pos_var_to_lit v) tau = truth_value (Implies f1 f2) tau)
//           = assert (variables_up_to_cnf_formula rf (L.length tau));
//             variables_up_to_monotone f1 n (L.length tau);
//             variables_up_to_monotone f2 n (L.length tau);
//             assert (truth_value_literal (pos_var_to_lit v1) tau = truth_value f1 tau);
//             assert (truth_value_literal (pos_var_to_lit v2) tau = truth_value f2 tau);
//             lemma_and_clauses v1 v2 v tau;
//             assert (truth_value_literal (pos_var_to_lit v) tau = truth_value (Implies f1 f2) tau)
//       in
//       forall_intro (move_requires aux)


// let prove_same_value_dimplies (f1:formula_t) (rf1 : list (list int)) (v1:int)
//                               (f2:formula_t) (rf2 : list (list int)) (v2:int)
//                               (n:nat) (start_interval:nat) (mid:nat) (end_interval:nat)
//                               (v:int) (rf : list (list int))
//     : Lemma (requires n <= start_interval /\ start_interval <= mid /\ mid <= v /\
//                       valid f1 rf1 v1 n start_interval mid /\
//                       tseitin_same_value f1 rf1 v1 n start_interval mid /\
//                       valid f2 rf2 v2 n mid v /\
//                       tseitin_same_value f2 rf2 v2 n mid v /\
//                       rf = rf1 @ rf2 @ (dimplies_clauses v1 v2 v) /\
//                       end_interval = v + 1)
//             (ensures valid (DImplies f1 f2) rf v n start_interval end_interval /\
//                      tseitin_same_value (DImplies f1 f2) rf v n start_interval end_interval)
//     = LP.append_assoc rf1 rf2 (dimplies_clauses v1 v2 v);
//       append_valid_cnf_formulas rf1 rf2;
//       append_valid_cnf_formulas (rf1 @ rf2) (dimplies_clauses v1 v2 v);
//       // assert (variables_in_interval rf n start_interval end_interval);
//       // assert (valid (DImplies f1 f2) rf v n start_interval end_interval);

//       let aux (tau : list bool) 
//           : Lemma (requires L.length tau >= end_interval /\
//                             truth_value_cnf_formula rf tau)
//                   (ensures truth_value_literal (pos_var_to_lit v) tau = truth_value (DImplies f1 f2) tau)
//           = assert (variables_up_to_cnf_formula rf (L.length tau));
//             variables_up_to_monotone f1 n (L.length tau);
//             variables_up_to_monotone f2 n (L.length tau);
//             assert (truth_value_literal (pos_var_to_lit v1) tau = truth_value f1 tau);
//             assert (truth_value_literal (pos_var_to_lit v2) tau = truth_value f2 tau);
//             lemma_and_clauses v1 v2 v tau;
//             assert (truth_value_literal (pos_var_to_lit v) tau = truth_value (DImplies f1 f2) tau)
//       in
//       forall_intro (move_requires aux)
  
  

// let prove_can_extend_not (f1:formula_t) (rf1 : list (list int)) (v1:int) (n:nat)
//                          (start_interval:nat) (v:int) (end_interval:nat) (rf : list (list int))
//     : Lemma (requires n <= start_interval /\ start_interval <= v /\ v < end_interval /\
//                       valid f1 rf1 v1 n start_interval v /\
//                       tseitin_can_extend f1 rf1 v1 n start_interval v /\
//                       rf = rf1 @ (not_clauses v1 v) /\
//                       end_interval = v + 1)
//             (ensures valid (Not f1) rf v n start_interval end_interval /\
//                      tseitin_can_extend (Not f1) rf v n start_interval end_interval)
//     = assert (valid (Not f1) rf v n start_interval end_interval);
//       let aux (tau : list bool) 
//           : Lemma (requires L.length tau = n)
//                   (ensures can_extend tau (Not f1) rf v n start_interval end_interval)
//           = assert (can_extend tau f1 rf1 v1 n start_interval v);
//             assert (valid_literal (pos_var_to_lit v1));
            
//             let conditions (tau1 : list bool) =
//                 // tau <= tau1 /\
//                 L.length tau1 = v /\
//                 truth_value_cnf_formula rf1 tau1 /\
//                 truth_value f1 tau = truth_value_literal (pos_var_to_lit v1) tau1
//             in
//             let extract_from_exists : (tau1 : list bool {conditions tau1}) -> prop = fun (tau1 : list bool) -> conditions tau1 in
//             let tau1 : list bool = FStar.IndefiniteDescription.indefinite_description_ghost (list bool) extract_from_exists in

//             negate_literal v1 tau1;

//             let tau' = combine1 tau tau1 n start_interval v (truth_value (Not f1) tau) in
//             // assert (tau <= tau');
//             assert (L.length tau' = end_interval);
//             transfer_truth_value rf1 tau1 tau' n start_interval v;

//             transfer_truth_value_lit (pos_var_to_lit v1) tau1 tau' n start_interval v;
//             assert (truth_value_literal (pos_var_to_lit v1) tau' = truth_value f1 tau);
//             transfer_truth_value_lit (neg_var_to_lit v1) tau1 tau' n start_interval v;
//             assert (truth_value_literal (neg_var_to_lit v1) tau1 = not (truth_value_literal (pos_var_to_lit v1) tau1));

//             lemma_not_clauses v1 v tau';
//             assert (truth_value_cnf_formula rf tau')
//       in
//       forall_intro (move_requires aux) 


// let prove_can_extend_or (f1:formula_t) (rf1 : list (list int)) (v1:int) 
//                         (f2:formula_t) (rf2 : list (list int)) (v2:int) 
//                         (n:nat) (start_interval:nat) (mid:nat) (v:int) (end_interval:nat)
//                         (rf :list (list int))
//     : Lemma (requires n <= start_interval /\ start_interval <= mid /\ mid <= v /\
//                       valid f1 rf1 v1 n start_interval mid /\
//                       tseitin_can_extend f1 rf1 v1 n start_interval mid /\
//                       valid f2 rf2 v2 n mid v /\
//                       tseitin_can_extend f2 rf2 v2 n mid v /\
//                       rf = rf1 @ rf2 @ (or_clauses v1 v2 v) /\
//                       end_interval = v + 1)
//             (ensures valid (Or f1 f2) rf v n start_interval end_interval /\
//                      tseitin_can_extend (Or f1 f2) rf v n start_interval end_interval)
//     = assert (valid (Or f1 f2) rf v n start_interval end_interval);
//       let aux (tau : list bool)
//           : Lemma (requires L.length tau = n)
//                   (ensures can_extend tau (Or f1 f2) rf v n start_interval end_interval)
//           = let conditions (tau1 : list bool) =
//                 // tau <= tau1 /\
//                 L.length tau1 = mid /\
//                 truth_value_cnf_formula rf1 tau1 /\
//                 truth_value f1 tau = truth_value_literal (pos_var_to_lit v1) tau1
//             in
//             let extract_from_exists : (tau1 : list bool {conditions tau1}) -> prop = fun (tau1 : list bool) -> conditions tau1 in
//             let tau1 : list bool = FStar.IndefiniteDescription.indefinite_description_ghost (list bool) extract_from_exists in

//             let conditions (tau2 : list bool) =
//                 // tau <= tau2 /\
//                 L.length tau2 = v /\
//                 truth_value_cnf_formula rf2 tau2 /\
//                 truth_value f2 tau = truth_value_literal (pos_var_to_lit v2) tau2
//             in
//             let extract_from_exists : (tau2 : list bool {conditions tau2}) -> prop = fun (tau2 : list bool) -> conditions tau2 in
//             let tau2 : list bool = FStar.IndefiniteDescription.indefinite_description_ghost (list bool) extract_from_exists in

//             let tau' = combine tau tau1 tau2 n start_interval mid v (truth_value (Or f1 f2) tau) in

//             assert (interval_of_list tau' 0 n = interval_of_list tau 0 n);
//             assert (interval_of_list tau' start_interval mid = interval_of_list tau1 start_interval mid);
//             assert (interval_of_list tau' mid v = interval_of_list tau2 mid v);
//             assert (L.index tau' v = truth_value (Or f1 f2) tau);

//             assert (truth_value_literal (pos_var_to_lit v) tau' = truth_value (Or f1 f2) tau);
//             assert (truth_value_literal (neg_var_to_lit v) tau' = not (truth_value (Or f1 f2) tau));

//             transfer_truth_value rf1 tau1 tau' n start_interval mid;
//             transfer_truth_value rf2 tau2 tau' n mid v;

//             transfer_truth_value_lit (pos_var_to_lit v1) tau1 tau' n start_interval mid;
//             transfer_truth_value_lit (neg_var_to_lit v1) tau1 tau' n start_interval mid;
//             assert (truth_value_literal (pos_var_to_lit v1) tau' = truth_value f1 tau);
//             assert (truth_value_literal (neg_var_to_lit v1) tau' = not (truth_value f1 tau));

//             transfer_truth_value_lit (pos_var_to_lit v2) tau2 tau' n mid v;
//             transfer_truth_value_lit (neg_var_to_lit v2) tau2 tau' n mid v;
//             assert (truth_value_literal (pos_var_to_lit v2) tau' = truth_value f2 tau);
//             assert (truth_value_literal (neg_var_to_lit v2) tau' = not (truth_value f2 tau));

//             assert (truth_value (Or f1 f2) tau = truth_value f1 tau || truth_value f2 tau);
//             lemma_or_clauses v1 v2 v tau';
//             assert (can_extend tau (Or f1 f2) rf v n start_interval end_interval)
//       in
//       forall_intro (move_requires aux)
