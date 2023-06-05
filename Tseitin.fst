module Tseitin

open FStar.List.Tot
module L = FStar.List.Tot.Base
module LP = FStar.List.Tot.Properties
open FStar.Classical
open FStar.Ghost
open Utils
open FormulaT
open CnfFormula
open TseitinCore
// open TseitinProofs
open LemmasForClauses



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

            let aux (tau : list bool) 
                : Lemma (requires L.length tau = n)
                        (ensures L.length tau = n /\
                                 can_extend tau f rf v n start_interval end_interval)
                = let tau' = tau @ (n_falses (end_interval - n)) in
                  LP.append_length tau (n_falses (end_interval - n));
                  assert (L.length tau' = end_interval);
                  assert (can_extend tau f rf v n start_interval end_interval)
            in
            forall_intro (move_requires aux);
            assert (tseitin_can_extend f rf v n start_interval end_interval);
            assert (tseitin_same_value f rf v n start_interval end_interval);
            rf, v, end_interval
        | Not f1 ->
            let rf1, v1, v = tseitin_cnf f1 n start_interval in
            let end_interval = v + 1 in
            let rf = rf1 @ (not_clauses v1 v) in
            prove_can_extend_not f1 rf1 v1 n start_interval v end_interval rf;
            prove_same_value_not f1 rf1 v1 n start_interval v end_interval rf;
            rf, v, end_interval
        | Or f1 f2 ->
            let rf1, v1, mid = tseitin_cnf f1 n start_interval in
            let rf2, v2, v = tseitin_cnf f2 n mid in
            let end_interval = v + 1 in
            let rf = rf1 @ rf2 @ (or_clauses v1 v2 v) in
            assert (valid f2 rf2 v2 n mid v);
            prove_can_extend_or f1 rf1 v1 f2 rf2 v2 n start_interval mid v end_interval rf;
            prove_same_value_or f1 rf1 v1 f2 rf2 v2 n start_interval mid v end_interval rf;
            rf, v, end_interval
        | And f1 f2 -> 
            let rf1, v1, mid = tseitin_cnf f1 n start_interval in
            let rf2, v2, v = tseitin_cnf f2 n mid in
            let end_interval = v + 1 in
            let rf = rf1 @ rf2 @ (and_clauses v1 v2 v) in
            prove_can_extend_and f1 rf1 v1 f2 rf2 v2 n start_interval mid v end_interval rf;
            prove_same_value_and f1 rf1 v1 f2 rf2 v2 n start_interval mid v end_interval rf;
            rf, v, end_interval
        | Implies f1 f2 ->
            let rf1, v1, mid = tseitin_cnf f1 n start_interval in
            let rf2, v2, v = tseitin_cnf f2 n mid in
            let end_interval = v + 1 in
            let rf = rf1 @ rf2 @ (implies_clauses v1 v2 v) in
            prove_can_extend_implies f1 rf1 v1 f2 rf2 v2 n start_interval mid v end_interval rf;
            prove_same_value_implies f1 rf1 v1 f2 rf2 v2 n start_interval mid v end_interval rf;
            rf, v, end_interval
        | DImplies f1 f2 ->
            let rf1, v1, mid = tseitin_cnf f1 n start_interval in
            let rf2, v2, v = tseitin_cnf f2 n mid in
            let end_interval = v + 1 in
            let rf = rf1 @ rf2 @ (dimplies_clauses v1 v2 v) in 
            prove_can_extend_dimplies f1 rf1 v1 f2 rf2 v2 n start_interval mid v end_interval rf;
            prove_same_value_dimplies f1 rf1 v1 f2 rf2 v2 n start_interval mid v end_interval rf;
            rf, v, end_interval


let satisfied_formula (f:formula_t) (tau : list bool)
    : Lemma (requires valid_formula_t f && variables_up_to f (L.length tau) && truth_value f tau)
            (ensures satisfiable f)
    = let n : erased nat = max_var f in
      assert (variables_up_to f n);
      variables_up_to_max_var f (L.length tau);
      let tau' = interval_of_list tau 0 n in
      same_values_append [] tau' [];
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
      let tau' = interval_of_list tau 0 n in
      same_values_append [] tau' [];
      assignment_relevant_cnf_formula rf tau tau' n


#set-options "--split_queries always"
let equisatisfiable_f (f:formula_t) (rf : list (list int)) (v:int) (n:nat) (end_interval:nat)
    : Lemma (requires valid f rf v n n end_interval /\
                      tseitin_same_value f rf v n n end_interval /\
                      tseitin_can_extend f rf v n n end_interval )
            (ensures satisfiable f ==> (valid_cnf_formula (rf @ [[pos_var_to_lit v]]) /\
                                        equisatisfiable f (rf @ [[pos_var_to_lit v]])))
    = append_valid_cnf_formulas rf [[pos_var_to_lit v]];
      LP.append_length rf [[pos_var_to_lit v]];
      
      let conditions (tau_short : list bool) : bool =
          L.length tau_short = max_var f &&
          truth_value f tau_short
      in
      assume (exists x . conditions x);
      let tau_short = extract_value conditions in
      
      assert (L.length tau_short = max_var f);
      variables_up_to_max_var f n;
      assert (max_var f <= n);
      let tau = tau_short @ (n_falses (n - max_var f)) in
      LP.append_length tau_short (n_falses (n - max_var f));
      assert (L.length tau = L.length tau_short + L.length (n_falses ( n - max_var f)));
      assert (L.length tau = n);
      same_values_append [] tau_short [];
      same_values_append [] tau_short (n_falses (n - max_var f));
      assignment_relevant f (max_var f) tau_short tau;
      assert (truth_value f tau);
      assert (can_extend tau f rf v n n end_interval);

      let conditions (tau' : list bool) =
          is_prefix tau tau' &&
          L.length tau' = end_interval &&
          truth_value_cnf_formula rf tau' &&
          truth_value f tau = truth_value_literal (pos_var_to_lit v) tau'
      in
      assume (exists x . conditions x);
      let tau' = extract_value conditions in

      assert (truth_value_cnf_formula rf tau');
      assert (pos_var_to_lit v = v + 1);
      assert (lit_to_var (pos_var_to_lit v) = v);
      append_variables_in_interval rf [[pos_var_to_lit v]] n n end_interval;
      assert (valid_literal (pos_var_to_lit v));
      assert (valid_clause [pos_var_to_lit v]);
      assert (valid_cnf_formula [[pos_var_to_lit v]]);
      assert (truth_value_literal (pos_var_to_lit v) tau');
      assert (variables_up_to_cnf_formula rf (L.length tau'));
      append_true_cnf_formulas rf [[pos_var_to_lit v]] tau';
      satisfied_cnf_formula (rf @ [[pos_var_to_lit v]]) tau'
#reset-options


let equisatisfiable_cnf_formula (f:formula_t) (rf : list (list int)) (v:int) (n:nat) (end_interval:nat)
    : Lemma (requires valid f rf v n n end_interval /\
                      tseitin_same_value f rf v n n end_interval /\
                      tseitin_can_extend f rf v n n end_interval)
            (ensures valid_cnf_formula (rf @ [[pos_var_to_lit v]]) /\
                     satisfiable_cnf_formula (rf @ [[pos_var_to_lit v]]) ==> equisatisfiable f (rf @ [[pos_var_to_lit v]]))
    = assert (valid_cnf_formula [[pos_var_to_lit v]]);
      append_valid_cnf_formulas rf [[pos_var_to_lit v]];
      LP.append_length rf [[pos_var_to_lit v]];
      
      let conditions (tau_short : list bool) =
          L.length tau_short = max_var_cnf_formula (rf @ [[pos_var_to_lit v]]) &&
          truth_value_cnf_formula (rf @ [[pos_var_to_lit v]]) tau_short
      in
      assume (exists x . conditions x);
      let tau_short = extract_value conditions in
      
      assert (pos_var_to_lit v = v + 1);
      assert (lit_to_var (pos_var_to_lit v) = v);
      variables_up_to_max_var_cnf_formula rf end_interval;
      variables_up_to_max_var_cnf_formula [[pos_var_to_lit v]] end_interval;
      append_cnf_formulas_variables_up_to_max_var rf [[pos_var_to_lit v]] end_interval;
      assert (variables_up_to_cnf_formula (rf @ [[pos_var_to_lit v]]) end_interval);
      variables_up_to_max_var_cnf_formula (rf @ [[pos_var_to_lit v]]) end_interval;

      assert (end_interval >= L.length tau_short);
      let tau = tau_short @ (n_falses (end_interval - (L.length tau_short))) in
      LP.append_length tau_short (n_falses (end_interval - (L.length tau_short)));
      assert (L.length tau = end_interval);
      same_values_append [] tau_short [];
      same_values_append [] tau_short (n_falses (end_interval - (L.length tau_short)));
      assignment_relevant_cnf_formula (rf @ [[pos_var_to_lit v]]) tau_short tau (L.length tau_short);

      assert (valid_cnf_formula [[pos_var_to_lit v]]);
      assert (variables_up_to_cnf_formula [[pos_var_to_lit v]] (L.length tau));
      true_parts_of_cnf_formula rf [[pos_var_to_lit v]] tau;
      assert (truth_value_cnf_formula rf tau);
      assert (truth_value_cnf_formula [[pos_var_to_lit v]] tau);

      assert (truth_value_clause [pos_var_to_lit v] tau);
      assert (variables_up_to_clause [pos_var_to_lit v] (L.length tau));
      assert (variables_up_to_literal (pos_var_to_lit v) (L.length tau));
      assert (truth_value_literal (pos_var_to_lit v) tau);
      variables_up_to_monotone f n end_interval;
      variables_up_to_max_var f end_interval;

      assert (L.length tau = end_interval);
      assert (variables_up_to f (L.length tau));
      assert (truth_value_literal (pos_var_to_lit v) tau = truth_value f tau);
      assert (truth_value f tau);
      satisfied_formula f tau


let tseitin_follows (f:formula_t) (rf : list (list int)) (v:int) (n:nat) (end_interval:nat)
    : Lemma (requires valid f rf v n n end_interval /\
                      tseitin_same_value f rf v n n end_interval /\
                      tseitin_can_extend f rf v n n end_interval)
            (ensures valid_cnf_formula (rf @ [[pos_var_to_lit v]]) /\
                     equisatisfiable f (rf @ [[pos_var_to_lit v]]))
    = append_valid_cnf_formulas rf [[pos_var_to_lit v]];
      equisatisfiable_f f rf v n end_interval;
      assert (satisfiable f ==> satisfiable_cnf_formula (rf @ [[pos_var_to_lit v]]));
      equisatisfiable_cnf_formula f rf v n end_interval;
      assert (satisfiable_cnf_formula (rf @ [[pos_var_to_lit v]]) ==> satisfiable f)


let tseitin (f:formula_t)
    : Pure (list (list int)) (requires valid_formula_t f)
                             (ensures fun r -> (valid_cnf_formula r /\ equisatisfiable f r))
    = let n = max_var f in
      let rf, v, end_interval = tseitin_cnf f n n in
      let r = rf @ [[pos_var_to_lit v]] in
      tseitin_follows f rf v n end_interval;
      r
