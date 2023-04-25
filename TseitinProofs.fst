module TseitinProofs

open CnfFormula
open FormulaT
open Utils
open TseitinCore
module L = FStar.List.Tot.Base
open FStar.Classical


let prove_same_value_not (f1:formula_t) (rf1 : list (list int)) (v1:int) (n:nat)
                         (start_interval:nat) (end_interval:nat) (rf : list (list int)) (v:int)
    : Lemma (requires n <= start_interval /\ start_interval <= v /\
                      valid f1 rf1 v1 n start_interval v /\
                      tseitin_same_value f1 rf1 v1 n start_interval v /\
                      rf = L.append rf1 (not_clauses v1 v) /\ end_interval = v + 1)
            (ensures valid (Not f1) rf v n start_interval end_interval /\
                     tseitin_same_value (Not f1) rf v n start_interval end_interval)
    = assert (valid (Not f1) rf v n start_interval end_interval);
      let aux (tau : list bool) : Lemma (requires L.length tau >= end_interval /\
                                                  truth_value_cnf_formula rf tau)
                                        (ensures truth_value_literal (pos_var_to_lit v) tau = truth_value (Not f1) tau)
          = variables_up_to_monotone f1 n (L.length tau);
            assert (truth_value_literal (pos_var_to_lit v1) tau = truth_value f1 tau);
            //lemma_not_clauses v1 v tau
            assert (truth_value_literal (pos_var_to_lit v) tau = truth_value (Not f1) tau)
      in
      forall_intro (move_requires aux)


let prove_can_extend_not (f1:formula_t) (rf1 : list (list int)) (v1:int) (n:nat)
                         (start_interval:nat) (end_interval:nat) (rf : list (list int)) (v:int)
    : Lemma (requires n <= start_interval /\ start_interval <= v /\ v < end_interval /\
                      valid f1 rf1 v1 n start_interval v /\
                      tseitin_can_extend f1 rf1 v1 n start_interval v /\
                      rf = L.append rf1 (not_clauses v1 v) /\ end_interval = v + 1)
            (ensures valid (Not f1) rf v n start_interval end_interval /\
                     tseitin_can_extend (Not f1) rf v n start_interval end_interval)
    = assert (n <= v);
      assert (valid (Not f1) rf v n start_interval end_interval);
      let aux (tau : list bool) : Lemma (requires L.length tau = n)
                                        (ensures can_extend tau (Not f1) rf v n start_interval end_interval)
          = assert (can_extend tau f1 rf1 v1 n start_interval v);
            assert (valid_literal (pos_var_to_lit v1))

// lemma proveCanExtendNot(f1 : FormulaT, rf1 : seq<seq<int>>, v1 : int,
//         n : int, start : int, v : int,
//         end : int, rf : seq<seq<int>>)
//         requires 0 <= n <= start <= v < end;
//         requires valid(f1, rf1, v1, n, start, v);
//         requires tseitinCanExtend(f1, rf1, v1, n, start, v);
//         requires rf == rf1 + notClauses(v1, v);
//         requires end == v + 1;
//         ensures valid(Not(f1), rf, v, n, start, end);
//         ensures tseitinCanExtend(Not(f1), rf, v, n, start, end);
//     {
//         assert 0 <= n <= v;
//         assert valid(Not(f1), rf, v, n, start, end);
//         forall tau : seq<bool> | |tau| == n
//             ensures canExtend(tau, Not(f1), rf, v, n, start, end);
//         {
//             assert canExtend(tau, f1, rf1, v1, n, start, v);
//             assert validLiteral(posVarToLit(v1));

//             ghost var tau1 :|
//                 tau <= tau1 &&
//                 |tau1| == v &&
//                 truthValueCnfFormula(rf1, tau1) &&
//                 truthValue(f1, tau) ==
//                 truthValueLiteral(posVarToLit(v1), tau1);

//             negateLiteral(v1, tau1);

//             ghost var tau' := combine1(tau, tau1, n, start, v,
//                 truthValue(Not(f1), tau));

//             assert tau <= tau';
//             assert |tau'| == end;
//             transferTruthValue(rf1, tau1, tau', n, start, v);

//             transferTruthValueLit(posVarToLit(v1), tau1, tau', n, start, v);
//             assert truthValueLiteral(posVarToLit(v1), tau') ==
//                 truthValue(f1, tau);
//             transferTruthValueLit(negVarToLit(v1), tau1, tau', n, start, v);
//             assert truthValueLiteral(negVarToLit(v1), tau1) ==
//                 !truthValueLiteral(posVarToLit(v1), tau1);

//             lemmaNotClauses(v1, v, tau');

//             assert truthValueCnfFormula(rf, tau');
//         }
//     }