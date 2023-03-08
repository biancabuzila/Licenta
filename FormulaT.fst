module FormulaT

open Utils
module L = FStar.List.Tot.Base
open FStar.Math.Lib
open FStar.String


type formula_t =
    | Var      : value:int -> formula_t
    | Not      : f:formula_t -> formula_t
    | Or       : f1:formula_t -> f2:formula_t -> formula_t
    | And      : f1:formula_t -> f2:formula_t -> formula_t
    | Implies  : f1:formula_t -> f2:formula_t -> formula_t
    | DImplies : f1:formula_t -> f2:formula_t -> formula_t


let rec valid_formula_t (f:formula_t) 
    : Tot bool (decreases f)
    = match f with
        | Var value -> value >= 0
        | Not f -> valid_formula_t f
        | Or f1 f2 -> valid_formula_t f1 && valid_formula_t f2
        | And f1 f2 -> valid_formula_t f1 && valid_formula_t f2
        | Implies f1 f2 -> valid_formula_t f1 && valid_formula_t f2
        | DImplies f1 f2 -> valid_formula_t f1 && valid_formula_t f2


let rec variables_up_to (f:formula_t) (n:int)
    : r:bool {r ==> valid_formula_t f}
    = match f with
        | Var value -> 0 <= value && value < n
        | Not f -> variables_up_to f n
        | Or f1 f2 -> variables_up_to f1 n && variables_up_to f2 n
        | And f1 f2 -> variables_up_to f1 n && variables_up_to f2 n
        | Implies f1 f2 ->variables_up_to f1 n && variables_up_to f2 n
        | DImplies f1 f2 -> variables_up_to f1 n && variables_up_to f2 n


let rec max_var (f:formula_t)
    : Pure int (requires valid_formula_t f)
               (ensures fun r -> (r >= 0 && variables_up_to f r))
    = match f with
        | Var value -> value + 1
        | Not f -> max_var f
        | Or f1 f2 -> 
            let temp1 = max_var f1 in
            let temp2 = max_var f2 in
            let n' = max temp1 temp2 in
            n'
        | And f1 f2 -> 
            let temp1 = max_var f1 in
            let temp2 = max_var f2 in
            let n' = max temp1 temp2 in
            n'
        | Implies f1 f2 -> 
            let temp1 = max_var f1 in
            let temp2 = max_var f2 in
            let n' = max temp1 temp2 in
            n'
        | DImplies f1 f2 -> 
            let temp1 = max_var f1 in
            let temp2 = max_var f2 in
            let n' = max temp1 temp2 in
            n'


let rec truth_value (f:formula_t {valid_formula_t f}) 
                    (assignment : list bool {variables_up_to f (L.length assignment)})
    : Tot bool (decreases f)
    = match f with
        | Var value -> my_nth assignment value
        | Not f -> not (truth_value f assignment)
        | Or f1 f2 -> truth_value f1 assignment || truth_value f2 assignment
        | And f1 f2 -> truth_value f1 assignment && truth_value f2 assignment
        | Implies f1 f2 -> not (truth_value f1 assignment) || truth_value f2 assignment
        | DImplies f1 f2 -> truth_value f1 assignment = truth_value f2 assignment


let equivalent (f1:formula_t {valid_formula_t f1}) 
               (f2:formula_t {valid_formula_t f2}) 
    = forall (tau : list bool) . 
        variables_up_to f1 (L.length tau) && 
        variables_up_to f2 (L.length tau) ==> 
        truth_value f1 tau = truth_value f2 tau


let rec seq_false (n:int)
    : Pure (list bool) (requires n >= 0)
                       (ensures fun r -> L.length r = n)
                       (decreases n)
    = if n = 0 then []
      else L.append (seq_false (n - 1)) [false]


let rec pretty_print (f:formula_t) : Tot (list char)
    = match f with
        | Var value -> integer_to_char_sequence value
        | Not f -> 
            let f = pretty_print f in 
            list_of_string (concat (concat "~("  [string_of_list f]) [")"])
        | Or f1 f2 ->  
            let f1 = pretty_print f1 in
            let f2 = pretty_print f2 in
            list_of_string (concat (concat (concat (concat "(" [string_of_list f1]) [" or "]) [string_of_list f2]) [")"])
        | And f1 f2 ->
            let f1 = pretty_print f1 in
            let f2 = pretty_print f2 in
            list_of_string (concat (concat (concat (concat "(" [string_of_list f1]) [" and "]) [string_of_list f2]) [")"])
        | Implies f1 f2 ->
            let f1 = pretty_print f1 in
            let f2 = pretty_print f2 in
            list_of_string (concat (concat (concat (concat "(" [string_of_list f1]) [" -> "]) [string_of_list f2]) [")"])
        | DImplies f1 f2 ->
            let f1 = pretty_print f1 in
            let f2 = pretty_print f2 in
            list_of_string (concat (concat (concat (concat "(" [string_of_list f1]) [" <-> "]) [string_of_list f2]) [")"])
