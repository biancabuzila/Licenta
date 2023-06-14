module Main

open FStar.List.Tot.Base
open FStar.IO
open FormulaT
open Cnf
open Tseitin



let main = let f0 = Var 0 in
           let f1 = Var 1 in
           let f2 = Var 2 in

           let test_formula = Or (And f1 f2) (Not (DImplies f0 f1)) in

           let out1 = FStar.Printf.sprintf "Formula: %s\n\n" (pretty_print test_formula) in
           print_string out1;

           let cnf = convert_to_cnf test_formula in
           let out2 = FStar.Printf.sprintf "Algoritm clasic:\n%s\n\n" (pretty_print cnf) in
           print_string out2;

           let tseitin_f = tseitin test_formula in
           let out3 = FStar.Printf.sprintf "Tseitin:\n%s\n\n" (print_cnf_formula tseitin_f) in
           print_string out3
