module CnfFormula

// module LP = FStar.List.Tot.Properties
module L = FStar.List.Tot.Base
open FStar.Classical
open Utils



let valid_literal (lit:int) 
    : Tot bool 
    = if lit <= -1 || lit >= 1 then true 
      else false


let lit_to_var (lit:int {valid_literal lit}) 
    : Tot int
    = if lit <= -1 then (-lit) - 1
      else lit - 1


// let rec verify_validity (#a:Type) (f : (subterm:a -> bool)) (term : list a)
//     : Tot bool (decreases term) 
//     = match term with
//         | [] -> true
//         | L.hd::L.tl -> if f L.hd then verify_validity f L.tl
//                     else false


let valid_clause (clause : list int)
    // : Tot bool
    // = verify_validity valid_literal clause
    = forall (lit:int {L.mem lit clause}) . valid_literal lit
    // = forall lit . L.mem lit clause ==> valid_literal lit


let valid_cnf_formula (f : list (list int))
    // : Tot bool
    // = verify_validity valid_clause f
    = forall (clause : list int) . L.mem clause f ==> valid_clause clause


let valid_variable (v:int) 
    : Tot bool
    = v >= 0


let variable_in_interval (v:int {valid_variable v}) 
                         (n:nat) 
                         (start_interval:nat {n <= start_interval}) 
                         (end_interval:nat {start_interval <= end_interval})
    : Tot bool
    = (0 <= v && v < n) || (start_interval <= v && v < end_interval)


let variables_up_to_literal (lit:int {valid_literal lit})
                            (n:nat)
    : Tot bool
    = 0 <= (lit_to_var lit) && (lit_to_var lit) < n


let variables_up_to_clause (clause : list int {valid_clause clause})
                           (n:nat)
    // : Tot bool (decreases clause)
    // = match clause with
    //     | [] -> true
    //     | L.hd::L.tl -> if variables_up_to_literal L.hd n then variables_up_to_clause L.tl n
    //                 else false
    = forall lit . L.mem lit clause ==> variables_up_to_literal lit n


let variables_up_to_cnf_formula (rf : list (list int) {valid_cnf_formula rf})
                                (n:nat)
    // : Tot bool (decreases rf)
    // = match rf with
    //     | [] -> true
    //     | L.hd::L.tl -> if variables_up_to_clause L.hd n then variables_up_to_cnf_formula L.tl n
    //                 else false
    = forall clause . L.mem clause rf ==> variables_up_to_clause clause n


let variables_in_interval_literal (lit:int)
                                  (n:nat)
                                  (start_interval:nat)
                                  (end_interval:nat)
    : Pure bool (requires valid_literal lit && n <= start_interval && start_interval <= end_interval) 
                (ensures fun r -> (r ==> variables_up_to_literal lit end_interval))
    = variable_in_interval (lit_to_var lit) n start_interval end_interval 


let rec variables_in_interval_clause (clause : list int)
                                     (n:nat)
                                     (start_interval:nat)
                                     (end_interval:nat)
    : Pure bool (requires valid_clause clause /\ n <= start_interval /\ start_interval <= end_interval)
                (ensures fun r -> (r ==> (variables_up_to_clause clause end_interval /\
                                          (forall lit . L.mem lit clause ==> variables_in_interval_literal lit n start_interval end_interval))))
    = match clause with
        | [] -> true
        | hd::tl -> if variables_in_interval_literal hd n start_interval end_interval then variables_in_interval_clause tl n start_interval end_interval
                    else false
 

let rec variables_in_interval (f : list (list int))
                              (n:nat)
                              (start_interval:nat)
                              (end_interval:nat)
    : Pure bool (requires valid_cnf_formula f /\ n <= start_interval /\ start_interval <= end_interval)
                (ensures fun r -> (r ==> (variables_up_to_cnf_formula f end_interval /\
                                   (forall clause . L.mem clause f ==> variables_in_interval_clause clause n start_interval end_interval))))
    = match f with 
        | [] -> true
        | hd::tl -> if variables_in_interval_clause hd n start_interval end_interval then variables_in_interval tl n start_interval end_interval
                    else false


let pos_var_to_lit (v:int {valid_variable v}) 
    : v:int {v >= 1 && valid_literal v} 
    = v + 1 


let neg_var_to_lit (v:int {valid_variable v})
    : v:int {v <= -1 && valid_literal v}
    = (-v) - 1 


let max_var_literal (lit:int {valid_literal lit})
    : v:int {v >= 0 && lit_to_var lit < v && variables_up_to_literal lit v}
    = (lit_to_var lit) + 1


let rec max_var_clause (clause : list int)
    : Pure int (requires valid_clause clause)
               (ensures fun r -> (r >= 0 /\ (forall lit . L.mem lit clause ==> lit_to_var lit < r) /\ variables_up_to_clause clause r))
    = match clause with
        | [] -> 0
        | hd::tl ->
        let max_recursive = max_var_clause tl in
        FStar.Math.Lib.max (max_var_literal hd) max_recursive


let rec max_var_cnf_formula (rf : list (list int))
    : Pure int (requires valid_cnf_formula rf)
               (ensures fun r -> (r >= 0 /\ (forall clause . L.mem clause rf ==> variables_up_to_clause clause r) /\ variables_up_to_cnf_formula rf r))
    = match rf with
        | [] -> assert (variables_up_to_cnf_formula rf 0); 0
        | hd::tl -> 
        let result = FStar.Math.Lib.max (max_var_clause hd) (max_var_cnf_formula tl) in
        assert (variables_up_to_clause hd result /\ (forall clause . L.mem clause tl ==> variables_up_to_clause clause result) /\ variables_up_to_cnf_formula rf result);
        result


let variables_up_to_max_var_literal (lit:int) (n:nat)
    : Lemma (requires valid_literal lit && variables_up_to_literal lit n)
            (ensures n >= max_var_literal lit)
    = ()


let rec variables_up_to_max_var_clause (clause : list int) (n:nat)
    : Lemma (requires valid_clause clause /\ variables_up_to_clause clause n)
            (ensures n >= max_var_clause clause)
    = if L.length clause = 0 then ()
      else
      (
          variables_up_to_max_var_literal (L.hd clause) n;
          variables_up_to_max_var_clause (L.tl clause) n
      )


let rec variables_up_to_max_var_cnf_formula (rf : list (list int)) (n:nat)
    : Lemma (requires valid_cnf_formula rf /\ variables_up_to_cnf_formula rf n)
            (ensures n >= max_var_cnf_formula rf)
    = if L.length rf = 0 then ()
      else
      (
          variables_up_to_max_var_clause (L.hd rf) n;
          variables_up_to_max_var_cnf_formula (L.tl rf) n
      )


let truth_value_literal (lit:int {valid_literal lit})
                        (tau : list bool {variables_up_to_literal lit (L.length tau)})
    : bool
    = if lit < 0 then not (L.index tau (lit_to_var lit))
      else L.index tau (lit_to_var lit)


let truth_value_clause (clause : list int {valid_clause clause})
                       (tau : list bool {variables_up_to_clause clause (L.length tau)})
    = exists lit . L.mem lit clause && truth_value_literal lit tau


let truth_value_cnf_formula (rf : list (list int) {valid_cnf_formula rf})
                            (tau : list bool {variables_up_to_cnf_formula rf (L.length tau)})
    = forall clause . L.mem clause rf ==> truth_value_clause clause tau


// let agree (tau1 : list bool) (tau2 : list bool) (start_interval:nat) 
//           (end_interval:nat {start_interval <= end_interval && L.length tau1 >= end_interval && L.length tau2 >= end_interval}) 
//     : bool
//     = interval_of_list tau1 start_interval end_interval = interval_of_list tau2 start_interval end_interval


let negate_literal (v:int) (tau : list bool)
    : Lemma (requires valid_variable v && L.length tau > v)
            (ensures truth_value_literal (neg_var_to_lit v) tau = not (truth_value_literal (pos_var_to_lit v) tau))
    = ()


let rec same_list (l1 : list bool) (l2 : list bool) (n:nat)
    : Lemma (requires L.length l1 = n && L.length l2 = n &&
                      interval_of_list l1 0 n = interval_of_list l2 0 n)
            (ensures l1 = l2)
    = if n = 0 then ()
      else same_list (L.tl l1) (L.tl l2) (n - 1)


// let equal_values (l1 : list bool) (l2 : list bool) (a:nat) (b:nat)
//     : Lemma (requires a <= b &&
//                       L.length l1 >= b && L.length l2 >= b &&
//                       interval_of_list l1 a b = interval_of_list l2 a b)
//             (ensures forall x . a <= x && x < b ==> L.index l1 x = L.index l2 x)
//     = ()


let rec assignment_relevant_cnf_formula (rf : list (list int)) (tau : list bool) (tau' : list bool) (n:nat)
    : Lemma (requires valid_cnf_formula rf /\ variables_up_to_cnf_formula rf n /\
                      L.length tau >= n /\ L.length tau' >= n /\
                      interval_of_list tau 0 n = interval_of_list tau' 0 n)
            (ensures truth_value_cnf_formula rf tau == truth_value_cnf_formula rf tau')
            (decreases %[L.length tau; L.length tau'])
    = if L.length tau' = n then
      (
          if L.length tau = n then 
          (
              same_list tau tau' n;
              assert (tau = tau');
              ()
          )
          else
          (
              assert (L.length tau > n);
              assert (L.length (interval_of_list tau 0 (L.length tau - 1)) >= n);
              assignment_relevant_cnf_formula rf (interval_of_list tau 0 (L.length tau - 1)) tau' n
          )
      )
      else assignment_relevant_cnf_formula rf tau (interval_of_list tau' 0 (L.length tau' - 1)) n


let transfer_truth_value_lit (lit:int) (tau : list bool) (tau' : list bool)
                             (n:nat) (start_interval:nat) (end_interval:nat)
    : Lemma (requires valid_literal lit &&
                      n <= start_interval && start_interval <= end_interval &&
                      variables_in_interval_literal lit n start_interval end_interval &&
                      L.length tau >= end_interval && L.length tau' >= end_interval &&
                      interval_of_list tau 0 n = interval_of_list tau' 0 n &&
                      interval_of_list tau start_interval end_interval = interval_of_list tau' start_interval end_interval)
            (ensures truth_value_literal lit tau = truth_value_literal lit tau')
    = assert ((0 <= lit_to_var lit && lit_to_var lit < n) ||
             (start_interval <= lit_to_var lit && lit_to_var lit < end_interval));
      assert (L.index tau (lit_to_var lit) = L.index tau' (lit_to_var lit))


let transfer_truth_value_clause (clause : list int) (tau : list bool) (tau' : list bool)
                                (n:nat) (start_interval:nat) (end_interval:nat)
    : Lemma (requires valid_clause clause /\
                      n <= start_interval /\ start_interval <= end_interval /\
                      variables_in_interval_clause clause n start_interval end_interval /\
                      L.length tau >= end_interval /\ L.length tau' >= end_interval /\
                      interval_of_list tau 0 n = interval_of_list tau' 0 n /\
                      interval_of_list tau start_interval end_interval = interval_of_list tau' start_interval end_interval)
            (ensures truth_value_clause clause tau == truth_value_clause clause tau')
    = assert (forall lit . L.mem lit clause ==> (((0 <= lit_to_var lit && lit_to_var lit < n) ||
                                                (start_interval <= lit_to_var lit && lit_to_var lit < end_interval)) &&
                                               L.index tau (lit_to_var lit) = L.index tau' (lit_to_var lit)))


let transfer_truth_value (rf : list (list int)) (tau : list bool) (tau' : list bool)
                         (n:nat) (start_interval:nat) (end_interval:nat)
    : Lemma (requires valid_cnf_formula rf /\
                      n <= start_interval /\ start_interval <= end_interval /\
                      variables_in_interval rf n start_interval end_interval /\
                      L.length tau >= end_interval /\ L.length tau' >= end_interval /\
                      interval_of_list tau 0 n = interval_of_list tau' 0 n /\
                      interval_of_list tau start_interval end_interval = interval_of_list tau' start_interval end_interval)
            (ensures truth_value_cnf_formula rf tau == truth_value_cnf_formula rf tau')
    = let aux (clause : list int) 
          : Lemma (requires L.mem clause rf)
                  (ensures valid_clause clause /\
                           variables_up_to_clause clause end_interval /\
                           truth_value_clause clause tau == truth_value_clause clause tau')
          = transfer_truth_value_clause clause tau tau' n start_interval end_interval
      in
      forall_intro (move_requires aux)
