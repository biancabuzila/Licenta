module Cnf

open FStar.Math.Lib
open FStar.Mul
module L = FStar.List.Tot.Base
open FStar.Ghost
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
    : r : list nat {L.length r = 5}
    = weight_of_ands f::(count_dimplies f::(count_implies f::(count_or_pairs f h1::[count_and_pairs f h2])))


let apply_rule_1 (f:formula_t) (ors_above_left : erased nat) (ands_above_left : erased nat)
    : Pure formula_t (requires valid_formula_t f && DImplies? f)
                     (ensures fun r -> (valid_formula_t r /\ 
                                        equivalent f r /\ 
                                        weight_of_ands r <= weight_of_ands f /\ 
                                        count_dimplies r < count_dimplies f /\
                                        smaller (measure r ors_above_left ands_above_left) (measure f ors_above_left ands_above_left)))
    = let DImplies f1 f2 = f in
      let f11 = Implies f1 f2 in
      let f12 = Implies f2 f1 in
      let r = And f11 f12 in
      assert (count_dimplies r = count_dimplies f11 + count_dimplies f12);
      assert (count_dimplies r = 2 * (count_dimplies f1 + count_dimplies f2));
      assert (count_dimplies f = 1 + pow2 (count_dimplies f1 + count_dimplies f2));
      mult2_upper (count_dimplies f1 + count_dimplies f2);
      r


let apply_rule_2 (f:formula_t) (ors_above_left : erased nat) (ands_above_left : erased nat)
    : Pure formula_t (requires valid_formula_t f && Implies? f)
                     (ensures fun r -> (valid_formula_t r /\
                                        equivalent f r /\
                                        weight_of_ands r <= weight_of_ands f /\
                                        count_dimplies r <= count_dimplies f /\
                                        count_implies r < count_implies f /\
                                        smaller (measure r ors_above_left ands_above_left) (measure f ors_above_left ands_above_left)))
    = let Implies f1 f2 = f in
      let r = Or (Not f1) f2 in
    //   assert (weight_of_ands r <= weight_of_ands f);
      r


let apply_rule_3 (f:formula_t) (ors_above_left : erased nat) (ands_above_left : erased nat)
    : Pure formula_t (requires valid_formula_t f && Or? f && And? (Or?.f2 f))
                     (ensures fun r -> (valid_formula_t r /\
                                        equivalent f r /\
                                        weight_of_ands r < weight_of_ands f /\
                                        smaller (measure r ors_above_left ands_above_left) (measure f ors_above_left ands_above_left)))
    = let Or f1 f2 = f in
      let And f21 f22 = f2 in
      And (Or f1 f21) (Or f1 f22)


let apply_rule_4 (f:formula_t) (ors_above_left : erased nat) (ands_above_left : erased nat)
    : Pure formula_t (requires valid_formula_t f && Or? f && And? (Or?.f1 f))
                     (ensures fun r -> (valid_formula_t r /\
                                        equivalent f r /\
                                        weight_of_ands r < weight_of_ands f /\
                                        smaller (measure r ors_above_left ands_above_left) (measure f ors_above_left ands_above_left)))
    = let Or f1 f2 = f in 
      let And f11 f12 = f1 in
      And (Or f11 f2) (Or f12 f2)


let rule_5_prop_aux (f:formula_t) (ors_above_left:nat)
    : Lemma (ensures count_or_pairs f ors_above_left <= count_or_pairs f (ors_above_left + 1))
    = ()


let rule_5_prop (f1:formula_t) (f2:formula_t) (f3:formula_t) (ors_above_left:nat)
    : Lemma (ensures count_or_pairs (Or (Or f1 f2) f3) ors_above_left < count_or_pairs (Or f1 (Or f2 f3)) ors_above_left)
    = assert (count_or_pairs (Or f1 (Or f2 f3)) ors_above_left = 
              count_or_pairs f1 ors_above_left + 
              count_or_pairs f2 (ors_above_left + 1) + 
              count_or_pairs f3 (ors_above_left + 2) + 
              ors_above_left + ors_above_left + 1);
      assert (count_or_pairs (Or (Or f1 f2) f3) ors_above_left =
              count_or_pairs f1 ors_above_left +
              count_or_pairs f2 (ors_above_left + 1) +
              count_or_pairs f3 (ors_above_left + 1) +
              ors_above_left + ors_above_left);
      rule_5_prop_aux f3 (ors_above_left + 1);
      assert (count_or_pairs f3 (ors_above_left + 1) <= count_or_pairs f3 (ors_above_left + 2));
      assert (count_or_pairs (Or (Or f1 f2) f3) ors_above_left < count_or_pairs (Or f1 (Or f2 f3)) ors_above_left)


let apply_rule_5 (f:formula_t) (ors_above_left : erased nat) (ands_above_left : erased nat)
    : Pure formula_t (requires valid_formula_t f && Or? f && Or? (Or?.f2 f))
                     (ensures fun r -> (valid_formula_t r /\
                                        equivalent f r /\
                                        weight_of_ands r <= weight_of_ands f /\
                                        count_dimplies r <= count_dimplies f /\
                                        count_implies r <= count_implies f /\
                                        count_or_pairs r ors_above_left < count_or_pairs f ors_above_left /\
                                        smaller (measure r ors_above_left ands_above_left) (measure f ors_above_left ands_above_left)))
    = let Or f1 f2 = f in 
      let Or f21 f22 = f2 in
      let r = Or (Or f1 f21) f22 in
      rule_5_prop f1 f21 f22 ors_above_left;
      assert (count_or_pairs r ors_above_left < count_or_pairs f ors_above_left);
      r


// let rule_6_prop_aux (f:formula_t) (ands_above_left:nat)
//     : Lemma (ensures count_and_pairs f ands_above_left <= count_and_pairs f (ands_above_left + 1))
//     = ()


// let rule_6_prop (f1:formula_t) (f2:formula_t) (f3:formula_t) (ands_above_left:nat)
//     : Lemma (ensures count_and_pairs (And (And f1 f2) f3) ands_above_left < count_and_pairs (And f1 (And f2 f3)) ands_above_left)
//     = assert (count_and_pairs (And f1 (And f2 f3)) ands_above_left = 
//               count_and_pairs f1 ands_above_left + 
//               count_and_pairs f2 (ands_above_left + 1) +
//               count_and_pairs f3 (ands_above_left + 2) +
//               ands_above_left + ands_above_left + 1);
//       assert (count_and_pairs (And (And f1 f2) f3) ands_above_left =
//               count_and_pairs f1 ands_above_left +
//               count_and_pairs f2 (ands_above_left + 1) +
//               count_and_pairs f3 (ands_above_left + 1) +
//               ands_above_left + ands_above_left);
//       rule_6_prop_aux f3 (ands_above_left + 1);
//       assert (count_and_pairs f3 (ands_above_left + 1) <= count_and_pairs f3 (ands_above_left + 2));
//       assert (count_and_pairs (And (And f1 f2) f3) ands_above_left < count_and_pairs (And f1 (And f2 f3)) ands_above_left)


// let apply_rule_6 (f:formula_t) (ors_above_left : erased nat) (ands_above_left : erased nat)
//     : Pure formula_t (requires valid_formula_t f && And? f && And? (And?.f2 f))
//                      (ensures fun r -> (valid_formula_t r /\
//                                         equivalent f r /\
//                                         weight_of_ands r <= weight_of_ands f /\
//                                         count_dimplies r <= count_dimplies f /\
//                                         count_implies r <= count_implies f /\
//                                         count_or_pairs r ors_above_left <= count_or_pairs f ors_above_left /\
//                                         count_and_pairs r ands_above_left < count_and_pairs f ands_above_left /\
//                                         smaller (measure r ors_above_left ands_above_left) (measure f ors_above_left ands_above_left)))
//     = let And f1 f2 = f in 
//       let And f21 f22 = f2 in 
//       let r = And (And f1 f21) f22 in
//       rule_6_prop f1 f21 f22 ands_above_left;
//       assert (count_and_pairs r ands_above_left < count_and_pairs f ands_above_left);
//       r


let rule_7_prop (f1:formula_t) (f2:formula_t)
    : Lemma (requires weight_of_ands f1 >= 2 && weight_of_ands f2 >= 2)
            (ensures weight_of_ands (And (Not f1) (Not f2)) < weight_of_ands (Not (Or f1 f2)))
    = assert (weight_of_ands (And (Not f1) (Not f2)) = pow2 (weight_of_ands f1) + pow2 (weight_of_ands f2) + 1);
      assert (weight_of_ands (Not (Or f1 f2)) = pow2 (weight_of_ands f1 * weight_of_ands f2));
      if weight_of_ands f1 >= weight_of_ands f2 then
        (
          sumpow_upper (weight_of_ands f1) (weight_of_ands f2);
          assert (pow2 (weight_of_ands f1) + pow2 (weight_of_ands f2) + 1 < pow2 (weight_of_ands f1 * weight_of_ands f2));
          assert (weight_of_ands (And (Not f1) (Not f2)) < weight_of_ands (Not (Or f1 f2)))
        )
      else sumpow_upper (weight_of_ands f2) (weight_of_ands f1)


let apply_rule_7 (f:formula_t) (ors_above_left : erased nat) (ands_above_left : erased nat)
    : Pure formula_t (requires valid_formula_t f && Not? f && Or? (Not?.f f))
                     (ensures fun r -> (valid_formula_t r /\
                                        equivalent f r /\
                                        weight_of_ands r < weight_of_ands f /\
                                        smaller (measure r ors_above_left ands_above_left) (measure f ors_above_left ands_above_left)))
    = let Not f1 = f in
      let Or f11 f12 = f1 in
      let r = And (Not f11) (Not f12) in
      rule_7_prop f11 f12;
      assert (weight_of_ands r < weight_of_ands f);
      r