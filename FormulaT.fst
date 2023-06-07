module FormulaT

open FStar.List.Tot
module L = FStar.List.Tot.Base
module LP = FStar.List.Tot.Properties
open FStar.Math.Lib
open FStar.String
open FStar.Classical
open Utils



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
        | Not f' -> valid_formula_t f'
        | Or f1 f2 -> valid_formula_t f1 && valid_formula_t f2
        | And f1 f2 -> valid_formula_t f1 && valid_formula_t f2
        | Implies f1 f2 -> valid_formula_t f1 && valid_formula_t f2
        | DImplies f1 f2 -> valid_formula_t f1 && valid_formula_t f2


let rec variables_up_to (f:formula_t) (n:int)
    : Tot (r:bool {r ==> valid_formula_t f})
    = match f with
        | Var value -> 0 <= value && value < n
        | Not f' -> variables_up_to f' n
        | Or f1 f2 -> variables_up_to f1 n && variables_up_to f2 n
        | And f1 f2 -> variables_up_to f1 n && variables_up_to f2 n
        | Implies f1 f2 -> variables_up_to f1 n && variables_up_to f2 n
        | DImplies f1 f2 -> variables_up_to f1 n && variables_up_to f2 n


let rec variables_up_to_monotone (f:formula_t) (n:int) (n':int)
    : Lemma (requires variables_up_to f n && n <= n')
            (ensures variables_up_to f n')
    = match f with
        | Var value -> ()
        | Not f' -> variables_up_to_monotone f' n n'
        | Or f1 f2 -> variables_up_to_monotone f1 n n'; variables_up_to_monotone f2 n n'
        | And f1 f2 -> variables_up_to_monotone f1 n n'; variables_up_to_monotone f2 n n'
        | Implies f1 f2 -> variables_up_to_monotone f1 n n'; variables_up_to_monotone f2 n n'
        | DImplies f1 f2 -> variables_up_to_monotone f1 n n'; variables_up_to_monotone f2 n n'


let rec max_var (f:formula_t)
    : Pure int (requires valid_formula_t f)
               (ensures fun r -> (r >= 0 && variables_up_to f r))
    = match f with
        | Var value -> value + 1
        | Not f' -> 
            let temp = max_var f' in
            let n' = temp in
            variables_up_to_monotone f' temp n';
            n'
        | Or f1 f2 -> 
            let temp1 = max_var f1 in
            let temp2 = max_var f2 in
            let n' = max temp1 temp2 in
            variables_up_to_monotone f1 temp1 n';
            variables_up_to_monotone f2 temp2 n';
            n'
        | And f1 f2 -> 
            let temp1 = max_var f1 in
            let temp2 = max_var f2 in
            let n' = max temp1 temp2 in
            variables_up_to_monotone f1 temp1 n';
            variables_up_to_monotone f2 temp2 n';
            n'
        | Implies f1 f2 -> 
            let temp1 = max_var f1 in
            let temp2 = max_var f2 in
            let n' = max temp1 temp2 in
            variables_up_to_monotone f1 temp1 n';
            variables_up_to_monotone f2 temp2 n';
            n'
        | DImplies f1 f2 -> 
            let temp1 = max_var f1 in
            let temp2 = max_var f2 in
            let n' = max temp1 temp2 in
            variables_up_to_monotone f1 temp1 n';
            variables_up_to_monotone f2 temp2 n';
            n'


let rec variables_up_to_max_var (f:formula_t) (n:nat)
    : Lemma (requires variables_up_to f n)
            (ensures valid_formula_t f && n >= max_var f)
    = match f with
        | Var value -> ()
        | Not f' -> variables_up_to_max_var f' n
        | Or f1 f2 -> variables_up_to_max_var f1 n; variables_up_to_max_var f2 n
        | And f1 f2 -> variables_up_to_max_var f1 n; variables_up_to_max_var f2 n
        | Implies f1 f2 -> variables_up_to_max_var f1 n; variables_up_to_max_var f2 n
        | DImplies f1 f2 -> variables_up_to_max_var f1 n; variables_up_to_max_var f2 n


let rec truth_value (f:formula_t {valid_formula_t f}) 
                    (assignment : list bool {variables_up_to f (L.length assignment)})
    : Tot bool (decreases f)
    = match f with
        | Var value -> L.index assignment value
        | Not f' -> not (truth_value f' assignment)
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


let rec seq_false (n:nat)
    : Pure (list bool) (requires True)
                       (ensures fun r -> L.length r = n)
    = if n = 0 then []
      else false::(seq_false (n - 1))


let rec assignment_relevant (f:formula_t) (n:nat) (tau1 : list bool) (tau2 : list bool)
    : Lemma (requires valid_formula_t f && variables_up_to f n && 
                      L.length tau1 >= n && L.length tau2 >= n &&
                      interval_of_list tau1 0 n = interval_of_list tau2 0 n)
            (ensures (variables_up_to_monotone f n (L.length tau1);
                      variables_up_to_monotone f n (L.length tau2);
                      truth_value f tau1 = truth_value f tau2))
    = match f with
        | Var value -> ()
        | Not f' ->
            variables_up_to_monotone f' n (L.length tau1);
            variables_up_to_monotone f' n (L.length tau2);
            assignment_relevant f' n tau1 tau2;
            assert (truth_value f' tau1 = truth_value f' tau2)
        | Or f1 f2 ->
            variables_up_to_monotone f1 n (L.length tau1);
            variables_up_to_monotone f1 n (L.length tau2);
            variables_up_to_monotone f2 n (L.length tau1);
            variables_up_to_monotone f2 n (L.length tau2);
            assignment_relevant f1 n tau1 tau2;
            assignment_relevant f2 n tau1 tau2;
            assert (truth_value f1 tau1 = truth_value f1 tau2);
            assert (truth_value f2 tau1 = truth_value f2 tau2)
        | And f1 f2 ->
            variables_up_to_monotone f1 n (L.length tau1);
            variables_up_to_monotone f1 n (L.length tau2);
            variables_up_to_monotone f2 n (L.length tau1);
            variables_up_to_monotone f2 n (L.length tau2);
            assignment_relevant f1 n tau1 tau2;
            assignment_relevant f2 n tau1 tau2;
            assert (truth_value f1 tau1 = truth_value f1 tau2);
            assert (truth_value f2 tau1 = truth_value f2 tau2)
        | Implies f1 f2 ->
            variables_up_to_monotone f1 n (L.length tau1);
            variables_up_to_monotone f1 n (L.length tau2);
            variables_up_to_monotone f2 n (L.length tau1);
            variables_up_to_monotone f2 n (L.length tau2);
            assignment_relevant f1 n tau1 tau2;
            assignment_relevant f2 n tau1 tau2;
            assert (truth_value f1 tau1 = truth_value f1 tau2);
            assert (truth_value f2 tau1 = truth_value f2 tau2)
        | DImplies f1 f2 ->
            variables_up_to_monotone f1 n (L.length tau1);
            variables_up_to_monotone f1 n (L.length tau2);
            variables_up_to_monotone f2 n (L.length tau1);
            variables_up_to_monotone f2 n (L.length tau2);
            assignment_relevant f1 n tau1 tau2;
            assignment_relevant f2 n tau1 tau2;
            assert (truth_value f1 tau1 = truth_value f1 tau2);
            assert (truth_value f2 tau1 = truth_value f2 tau2)


let equivalent_trans (f1:formula_t) (f2:formula_t) (f3:formula_t)
    : Lemma (requires valid_formula_t f1 /\ valid_formula_t f2 /\ valid_formula_t f3 /\
                      equivalent f1 f2 /\ equivalent f2 f3)
            (ensures equivalent f1 f3)
    = let aux (tau : list bool) 
          : Lemma (requires variables_up_to f1 (L.length tau) && 
                            variables_up_to f3 (L.length tau))
                  (ensures variables_up_to f1 (L.length tau) && 
                           variables_up_to f3 (L.length tau) &&
                           truth_value f1 tau = truth_value f3 tau)
          = let temp = seq_false (max_var f2) in 
            
            LP.append_length tau temp;
            variables_up_to_monotone f2 (L.length temp) (L.length (L.append tau temp));

            same_values_append [] tau [];
            same_values_append [] tau temp;

            assignment_relevant f1 (L.length tau) tau (L.append tau temp); 
            variables_up_to_monotone f1 (L.length tau) (L.length (L.append tau temp));

            assignment_relevant f3 (L.length tau) tau (L.append tau temp);
            variables_up_to_monotone f3 (L.length tau) (L.length (L.append tau temp));
            assert (truth_value f1 tau = truth_value f3 tau)
      in
      forall_intro (move_requires aux)


let rec pretty_print (f:formula_t) : Tot string 
    = match f with
        | Var value -> string_of_int value
        | Not f' -> 
            let f' = pretty_print f' in 
            concat "" ["~("; f'; ")"]
        | Or f1 f2 ->  
            let f1 = pretty_print f1 in
            let f2 = pretty_print f2 in
            concat "" ["("; f1; " or "; f2; ")"]
        | And f1 f2 ->
            let f1 = pretty_print f1 in
            let f2 = pretty_print f2 in
            concat "" ["("; f1; " and "; f2; ")"]
        | Implies f1 f2 ->
            let f1 = pretty_print f1 in
            let f2 = pretty_print f2 in
            concat "" ["("; f1; " -> "; f2; ")"]
        | DImplies f1 f2 ->
            let f1 = pretty_print f1 in
            let f2 = pretty_print f2 in
            concat "" ["("; f1; " <-> "; f2; ")"]
