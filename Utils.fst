module Utils

module L = FStar.List.Tot.Base


let rec my_nth (#a:Type) (l : list a) (n:int {n >= 0 && n < L.length l}) : a
    = if n = 0 then L.hd l
      else my_nth (L.tl l) (n - 1)


let integer_to_char_sequence (x:int) : list FStar.String.char
    = FStar.String.list_of_string (string_of_int x)


// let rec n_falses (n:int)
//     : Pure (list bool) (requires n >= 0)
//                        (ensures fun r -> L.length r = n)
//     = if n = 0 then []
//       else L.append (n_falses (n - 1)) [false]