module Main

open FormulaT
open FStar.String
open FStar.IO


let main = let f0 = Var 0 in
                print_string (string_of_list (pretty_print f0))
