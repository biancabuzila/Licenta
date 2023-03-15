module Cnf

open FStar.Math.Lib
open FormulaT
open Utils


let rec weight_of_ands (f:formula_t) : Tot (r:nat{r >= 2}) (decreases f)
    = match f with
        | Var value -> 2
        | Not f -> pow2 (weight_of_ands f)
        | Or f1 f2 -> (weight_of_ands f1) * (weight_of_ands f2)
        | And f1 f2 -> weight_of_ands f1 + weight_of_ands f2 + 1
        | Implies f1 f2 -> pow2 (weight_of_ands f1) * weight_of_ands f2
        | DImplies f1 f2 -> pow2 (weight_of_ands f1) * weight_of_ands f2 + pow2 (weight_of_ands f2) * weight_of_ands f1 + 1


let rec count_dimplies (f:formula_t)
    : Tot nat (decreases f)
    = match f with
        | Var value -> 0
        | Not f -> count_dimplies f
        | Or f1 f2 -> count_dimplies f1 + count_dimplies f2
        | And f1 f2 -> count_dimplies f1 + count_dimplies f2
        | Implies f1 f2 -> count_dimplies f1 + count_dimplies f2
        | DImplies f1 f2 -> 1 + pow2 (count_dimplies f1 + count_dimplies f2)


let rec count_implies (f:formula_t) : Tot nat (decreases f)
    = match f with
        | Var value -> 0
        | Not f -> count_implies f
        | Or f1 f2 -> count_implies f1 + count_implies f2
        | And f1 f2 -> count_implies f1 + count_implies f2
        | Implies f1 f2 -> 1 + count_implies f1 + count_implies f2
        | DImplies f1 f2 -> count_implies f1 + count_implies f2
    

let rec count_and_pairs (f:formula_t) (ands_above_left:nat) : Tot nat (decreases f)
    = match f with
        | Var value -> 0
        | Not f -> count_and_pairs f ands_above_left
        | Or f1 f2 -> count_and_pairs f1 ands_above_left + count_and_pairs f2 ands_above_left
        | And f1 f2 -> count_and_pairs f1 ands_above_left + count_and_pairs f2 (ands_above_left + 1) + ands_above_left
        | Implies f1 f2 -> count_and_pairs f1 ands_above_left + count_and_pairs f2 ands_above_left
        | DImplies f1 f2 -> count_and_pairs f1 ands_above_left + count_and_pairs f2 ands_above_left


let rec count_or_pairs (f:formula_t) (ors_above_left:nat) : Tot nat (decreases f)
    = match f with
        | Var value -> 0
        | Not f-> count_or_pairs f ors_above_left
        | Or f1 f2 -> count_or_pairs f1 ors_above_left + count_or_pairs f2 (ors_above_left + 1) + ors_above_left
        | And f1 f2 -> count_or_pairs f1 ors_above_left + count_or_pairs f2 ors_above_left
        | Implies f1 f2 -> count_or_pairs f1 ors_above_left + count_or_pairs f2 ors_above_left
        | DImplies f1 f2 -> count_or_pairs f1 ors_above_left + count_or_pairs f2 ors_above_left


let measure (f:formula_t) (h1:nat) (h2:nat)
    = (weight_of_ands f, count_dimplies f, count_implies f, count_or_pairs f h1, count_and_pairs f h2)
