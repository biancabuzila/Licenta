module Tseitin

open FStar.List.Tot
module L = FStar.List.Tot.Base
module LP = FStar.List.Tot.Properties
open FStar.Classical
open FStar.Ghost
open FormulaT
open CnfFormula
open Utils
open TseitinCore



let satisfiable (f:formula_t {valid_formula_t f})
    = exists tau . L.length tau = max_var f && truth_value f tau


let satisfiable_cnf_formula (rf : list (list int) {valid_cnf_formula rf})
    = exists tau . L.length tau = max_var_cnf_formula rf ==> truth_value_cnf_formula rf tau


let equisatisfiable (f:formula_t {valid_formula_t f})
                    (rf : list (list int) {valid_cnf_formula rf})
    = satisfiable f <==> satisfiable_cnf_formula rf


let rec tseitin_cnf (f:formula_t) (n:nat) (start_interval:nat)
    : Pure ((list (list int)) & int & nat)
           (requires variables_up_to f n && n <= start_interval)
           (ensures fun (rf, v, end_interval) -> (valid f rf v n start_interval end_interval /\
                                                  tseitin_same_value f rf v n start_interval end_interval /\
                                                  tseitin_can_extend f rf v n start_interval end_interval))
    = match f with
        | Var value ->
            let rf = [] in
            let v = value in
            let end_interval = start_interval in

            let aux (tau : list bool) : Lemma (requires L.length tau = n)
                                              (ensures can_extend tau f rf v n start_interval end_interval)
                = let tau' = tau @ (n_falses (end_interval - n)) in
                  LP.append_length tau (n_falses (end_interval - n));
                  assert (L.length tau' = end_interval)
                //   assert (can_extend tau f rf v n start_interval end_interval)
            in
            forall_intro (move_requires aux);
            assert (tseitin_can_extend f rf v n start_interval end_interval);
            assert (tseitin_same_value f rf v n start_interval end_interval);
            rf, v, end_interval
        | Not f1 ->
            let rf1, v1, v = tseitin_cnf f1 n start_interval in
            let end_interval = v + 1 in
            let rf = L.append rf1 (not_clauses v1 v) in
            // proveCanExtendNot(f1, rf1, v1, n, start, v, end, rf);
            //proveSameValueNot(f1, rf1, v1, n, start, v, end, rf);
            rf, v, end_interval
        | Or f1 f2 ->
            let rf1, v1, mid = tseitin_cnf f1 n start_interval in
            let rf2, v2, v = tseitin_cnf f2 n mid in
            let end_interval = v + 1 in
            let rf = L.append (L.append rf1 rf2) (or_clauses v1 v2 v) in
            //proveCanExtendOr(f1, rf1, v1, f2, rf2, v2, n, start, mid, v, end, rf);
            //proveSameValueOr(f1, rf1, v1, f2, rf2, v2, n, start, mid, v, end, rf);
            rf, v, end_interval
        | And f1 f2 -> 
            let rf1, v1, mid = tseitin_cnf f1 n start_interval in
            let rf2, v2, v = tseitin_cnf f2 n mid in
            let end_interval = v + 1 in
            let rf = L.append (L.append rf1 rf2) (and_clauses v1 v2 v) in
            //proveCanExtendAnd(f1, rf1, v1, f2, rf2, v2, n, start, mid, v, end, rf);
            //proveSameValueAnd(f1, rf1, v1, f2, rf2, v2, n, start, mid, v, end, rf);
            rf, v, end_interval
        | Implies f1 f2 ->
            let rf1, v1, mid = tseitin_cnf f1 n start_interval in
            let rf2, v2, v = tseitin_cnf f2 n mid in
            let end_interval = v + 1 in
            let rf = L.append (L.append rf1 rf2) (implies_clauses v1 v2 v) in
            // proveCanExtendImplies(f1, rf1, v1, f2, rf2, v2, n, start, mid, v, end, rf);
            //proveSameValueImplies(f1, rf1, v1, f2, rf2, v2, n, start, mid, v, end, rf);
            rf, v, end_interval
        | DImplies f1 f2 ->
            let rf1, v1, mid = tseitin_cnf f1 n start_interval in
            let rf2, v2, v = tseitin_cnf f2 n mid in
            let end_interval = v + 1 in
            let rf = L.append (L.append rf1 rf2) (dimplies_clauses v1 v2 v) in 
            //proveCanExtendDimplies(f1, rf1, v1, f2, rf2, v2, n, start, mid, v, end, rf);
            //proveSameValueDimplies(f1, rf1, v1, f2, rf2, v2, n, start, mid, v, end, rf);
            rf, v, end_interval


let satisfied_formula (f:formula_t) (tau : list bool)
    : Lemma (requires valid_formula_t f && variables_up_to f (L.length tau))
            (ensures satisfiable f)
    = let n : erased nat = max_var f in
      assert (variables_up_to f n);
      variables_up_to_max_var f (L.length tau);
      let tau' : erased (list bool) = interval_of_list tau 0 n in
      assignment_relevant f n tau tau'


let satisfied_cnf_formula (rf : list (list int)) (tau : list bool)
    : Lemma (requires valid_cnf_formula rf /\ 
                      variables_up_to_cnf_formula rf (L.length tau) /\
                      truth_value_cnf_formula rf tau)
            (ensures satisfiable_cnf_formula rf)
    = let n : erased nat = max_var_cnf_formula rf in
      assert (variables_up_to_cnf_formula rf n);
      variables_up_to_max_var_cnf_formula rf (L.length tau);
      assert (L.length tau >= n);
      let tau' : erased (list bool) = interval_of_list tau 0 n in
      assignment_relevant_cnf_formula rf tau tau' n


// let tseitin (f:formula_t)
//     : Pure (list (list int)) (requires valid_formula_t f)
//                              (ensures fun r -> (valid_cnf_formula r /\ equisatisfiable f r))
//     = let n = max_var f in
//       let rf, v, end_interval = tseitin_cnf f n n in
//       let r = L.append rf [[pos_var_to_lit v]] in
//       //tseitin_follows f rf v n end_interval;
//       r

