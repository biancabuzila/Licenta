module Main

open FStar.List.Tot.Base
open FStar.String
open FStar.IO
open Utils
open FormulaT


let rec list_int_to_list_string (a:list int) : list string
   = match a with
      | [] -> []
      | hd::tl -> string_of_int hd :: (list_int_to_list_string tl)

 let main = //let f0 = Var 0 in
//            let f1 = Var 1 in
//            let f2 = Var 2 in
//            let f3 = Var 3 in 
         //   let var_for_rule_0 = DImplies f0 f1 in
         //   let var_for_rule_1 = Implies f0 f1 in
         //   let var_for_rule_2 = Or f0 (And f1 f2) in
         //   let var_for_rule_3 = Or (And f1 f2) (DImplies f0 f1) in
         //   let var_for_rule_5 = Or f0 (Or f1 f2) in
         //   let var_for_rule_6 = And f0 (And f1 f2) in
         //   let var_for_rule_7 = Not (And f0 f1) in
         //   let var_for_rule_8 = Not (Or f0 f1) in
         //   let var_for_rule_9 = Not (Not f0) in
         //   let test_formula = DImplies (Or f1 f2) f0 in
         //   let out1 = FStar.Printf.sprintf "%s\n" (pretty_print test_formula) in
            //   print_string out1;
            //   print_string (pretty_print var_for_rule_3)
         //   let start_interval = 4 in
         //   let end_interval = 6 in
           let l1 = [1;2;3;4;5] in
           let interv = interval_of_list l1 0 0 in
           print_string (concat "" (list_int_to_list_string interv))

