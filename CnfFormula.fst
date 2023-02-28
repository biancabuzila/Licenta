module CnfFormula

open FStar.List.Tot.Base


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
//         | hd::tl -> if f hd then verify_validity f tl
//                     else false


let valid_clause (clause : list int)
    // : Tot bool
    // = verify_validity valid_literal clause
    = forall (lit:int {mem lit clause}) . valid_literal lit


let valid_cnf_formula (f : list (list int))
    // : Tot bool
    // = verify_validity valid_clause f
    = forall (clause : list int) . mem clause f ==> valid_clause clause


let valid_variable (v:int) 
    : Tot bool
    = v >= 0


let variable_in_interval (v:int {valid_variable v}) 
                         (n:int {0 <= n}) 
                         (start_interval:int {n <= start_interval}) 
                         (end_interval:int {start_interval <= end_interval})
    : Tot bool
    = (0 <= v && v < n) || (start_interval <= v && v < end_interval)


let variables_up_to_literal (lit:int {valid_literal lit})
                            (n:int {n >= 0})
    : Tot bool
    = 0 <= (lit_to_var lit) && (lit_to_var lit) < n


let variables_up_to_clause (clause : list int {valid_clause clause})
                           (n:int {n >= 0})
    // : Tot bool (decreases clause)
    // = match clause with
    //     | [] -> true
    //     | hd::tl -> if variables_up_to_literal hd n then variables_up_to_clause tl n
    //                 else false
    = forall lit . mem lit clause ==> variables_up_to_literal lit n


let variables_up_to_cnf_formula (rf : list (list int) {valid_cnf_formula rf})
                                (n:int {n >= 0})
    // : Tot bool (decreases rf)
    // = match rf with
    //     | [] -> true
    //     | hd::tl -> if variables_up_to_clause hd n then variables_up_to_cnf_formula tl n
    //                 else false
    = forall clause . mem clause rf ==> variables_up_to_clause clause n


let variables_in_interval_literal (lit:int)
                                  (n:int)
                                  (start_interval:int)
                                  (end_interval:int)
    : Pure bool (requires valid_literal lit && 0 <= n && n <= start_interval && start_interval <= end_interval) 
                (ensures fun r -> (r ==> variables_up_to_literal lit end_interval))
    = variable_in_interval (lit_to_var lit) n start_interval end_interval 


let rec variables_in_interval_clause (clause : list int)
                                     (n:int)
                                     (start_interval:int)
                                     (end_interval:int)
    : Pure bool (requires valid_clause clause /\ 0 <= n /\ n <= start_interval /\ start_interval <= end_interval)
                (ensures fun r -> (r ==> variables_up_to_clause clause end_interval))
    = match clause with
        | [] -> true
        | hd::tl -> if variables_in_interval_literal hd n start_interval end_interval then variables_in_interval_clause tl n start_interval end_interval
                    else false
    // = forall (lit:int) . mem lit clause ==> variables_in_interval_literal lit n start_interval end_interval
 

let rec variables_in_interval (f : list (list int))
                              (n:int)
                              (start_interval:int)
                              (end_interval:int)
    : Pure bool (requires valid_cnf_formula f /\ 0 <= n /\ n <= start_interval /\ start_interval <= end_interval)
                (ensures fun r -> (r ==> variables_up_to_cnf_formula f end_interval))
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
               (ensures fun r -> (r >= 0 /\ (forall lit . mem lit clause ==> lit_to_var lit < r) /\ variables_up_to_clause clause r))
    = match clause with
        | [] -> 0
        | hd::tl ->
        let max_recursive = max_var_clause tl in
        FStar.Math.Lib.max (max_var_literal hd) max_recursive


let rec max_var_cnf_formula (rf : list (list int))
    : Pure int (requires valid_cnf_formula rf)
               (ensures fun r -> (r >= 0 /\ (forall clause . mem clause rf ==> variables_up_to_clause clause r) /\ variables_up_to_cnf_formula rf r))
    = match rf with
        | [] -> assert (variables_up_to_cnf_formula rf 0); 0
        | hd::tl -> 
        let result = FStar.Math.Lib.max (max_var_clause hd) (max_var_cnf_formula tl) in
        assert (variables_up_to_clause hd result /\ (forall clause . mem clause tl ==> variables_up_to_clause clause result) /\ variables_up_to_cnf_formula rf result);
        result


let rec my_nth (#a:Type) (l : list a) (n:int {n >= 0 && n < length l})
    : a
    = if n = 0 then hd l
      else my_nth (tl l) (n - 1)


let truth_value_literal (lit:int {valid_literal lit})
                        (tau : list bool {variables_up_to_literal lit (length tau)})
    : bool
    = if lit < 0 then not (my_nth tau (lit_to_var lit))
      else my_nth tau (lit_to_var lit)


let truth_value_clause (clause : list int {valid_clause clause})
                       (tau : list bool {variables_up_to_clause clause (length tau)})
    = exists lit . mem lit clause ==> truth_value_literal lit tau


let truth_value_cnf_formula (rf : list (list int) {valid_cnf_formula rf})
                            (tau : list bool {variables_up_to_cnf_formula rf (length tau)})
    = forall clause . mem clause rf ==> truth_value_clause clause tau





// open FStar.IO
// let _ = if (valid_literal 0) then print_string "True\n" else print_string "False\n"
// let _ = print_string (string_of_int (lit_to_var 1))