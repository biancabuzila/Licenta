module Main

open FStar.List.Tot.Base
open FStar.String
open FStar.IO
open FormulaT
open Cnf
open Tseitin



let rec print_clause (clause : list int) : string
   = match clause with
      | [] -> ""
      | hd::tl -> 
           let r = print_clause tl in
           if r = "" then string_of_int hd
           else
           (
              if hd < 0 then 
                 let aux = concat "" ["~("; string_of_int (-hd); ")"] in
                 concat " or " [aux; r]
              else concat " or " [string_of_int hd; r]
           )


let rec print_cnf_formula (f : list (list int)) : string
   = match f with
      | [] -> ""
      | hd::tl ->
           let r = print_cnf_formula tl in
           if r = "" then concat "" ["("; print_clause hd; ")"]
           else concat " and " [concat "" ["("; print_clause hd; ")"]; r]


let main = let f0 = Var 0 in
           let f1 = Var 1 in
           let f2 = Var 2 in
           let f3 = Var 3 in 

           let var_for_rule_0 = DImplies f0 f1 in
           let var_for_rule_1 = Implies f0 f1 in
           let var_for_rule_2 = Or f0 (And f1 f2) in
           let var_for_rule_3 = Or (And f1 f2) (DImplies f0 f1) in
           let var_for_rule_5 = Or f0 (Or f1 f2) in
           let var_for_rule_6 = And f0 (And f1 f2) in
           let var_for_rule_7 = Not (And f0 f1) in
           let var_for_rule_8 = Not (Or f0 f1) in
           let var_for_rule_9 = Not (Not f0) in
           let test_formula = DImplies (Or f1 f2) f0 in

           let out1 = FStar.Printf.sprintf "Formula: %s\n\n" (pretty_print test_formula) in
           print_string out1;

           let cnf = convert_to_cnf test_formula in
           let out2 = FStar.Printf.sprintf "Algoritm clasic:\n%s\n\n" (pretty_print cnf) in
           print_string out2;

           let tseitin_f = tseitin test_formula in
           let out3 = FStar.Printf.sprintf "Tseitin:\n%s\n\n" (print_cnf_formula tseitin_f) in
           print_string out3
