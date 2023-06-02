module Utils

open FStar.List.Tot
module L = FStar.List.Tot.Base
open FStar.Mul
open FStar.Ghost



let integer_to_char_sequence (x:int) : list FStar.String.char
    = FStar.String.list_of_string (string_of_int x)


let rec n_falses (n:nat)
    : Pure (list bool) (requires True)
                       (ensures fun r -> L.length r = n)
    = if n = 0 then []
      else false::(n_falses (n - 1))


let smaller (a : list nat) (b : list nat {L.length a = L.length b && L.length a = 5})
    : bool
    = L.hd a < L.hd b ||
      (L.hd a <= L.hd b && L.index a 1 < L.index b 1) ||
      (L.hd a <= L.hd b && L.index a 1 <= L.index b 1 && L.index a 2 < L.index b 2) ||
      (L.hd a <= L.hd b && L.index a 1 <= L.index b 1 && L.index a 2 <= L.index b 2 && L.index a 3 < L.index b 3) ||
      (L.hd a <= L.hd b && L.index a 1 <= L.index b 1 && L.index a 2 <= L.index b 2 && L.index a 3 <= L.index b 3 && L.index a 4 < L.index b 4)


let rec mult2_upper (x:int)
    : Lemma (requires x >= 0)
            (ensures 2 * x < 1 + pow2 x)
    = if x = 0 then ()
      else mult2_upper (x - 1)


let rec pow_monotone (a:int) (b:int)
    : Lemma (requires a >= 0 && b >= a)
            (ensures pow2 a <= pow2 b)
    = if a = 0 then ()
      else pow_monotone (a - 1) (b - 1)


let rec pow_monotone_strict (a:int) (b:int)
    : Lemma (requires a >= 0 && b > a)
            (ensures pow2 a < pow2 b)
    = if a = 0 then ()
      else pow_monotone_strict (a - 1) (b - 1)


let rec multpow_powsum (a:int) (b:int)
    : Lemma (requires a >= 1 && b >= 1)
            (ensures pow2 a * pow2 b = pow2 (a + b))
    = if b > 2 then multpow_powsum a (b - 1)
      else assert (pow2 a * pow2 2 = pow2 (a + 2))


let sumpow_upper (a:int) (b:int)
    : Lemma (requires a >= 1 && b >= 2 && a >= b)
            (ensures pow2 a + pow2 b + 1 < pow2 (a * b))
    = pow_monotone (a * 2) (a * b);
      assert (pow2 (a * 2) <= pow2 (a * b));
      assert (pow2 (a + a) <= pow2 (a * 2));
      multpow_powsum a a;
      assert (pow2 a * pow2 a <= pow2 (a + a));
      assert (4 <= pow2 a);
      assert (4 * pow2 a <= pow2 a * pow2 a);
      assert (pow2 a + pow2 a + pow2 a + pow2 a <= 4 * pow2 a);
      pow_monotone b a;
      assert (pow2 b <= pow2 a);
      assert (pow2 a + pow2 b + 1 < pow2 a + pow2 a + pow2 a + pow2 a)


let rec pow_increases (a:int)
    : Lemma (requires a >= 1)
            (ensures a < pow2 a)
    = if a = 1 then ()
      else pow_increases (a - 1)
  

let less_than_mult_right (a:int) (b:int) (c:int)
    : Lemma (requires a >= 1 && b >= 1 && c >= 1 && c < b)
            (ensures a * c < a * b)
    = ()


let rec interval_of_list (#a:Type) (l : list a) (start_interval:nat) (end_interval:nat)
    : Pure (list a) (requires start_interval <= end_interval && end_interval <= L.length l)
                    (ensures fun r -> L.length r = end_interval - start_interval /\
                                       (forall (i:nat) . start_interval <= i && i < end_interval ==> L.index l i == L.index r (i - start_interval)))
//     = fst (L.splitAt (end_interval - start_interval) (snd (L.splitAt start_interval l)))
    = if start_interval = 0 then 
        if end_interval = 0 then []
        else (L.hd l)::interval_of_list (L.tl l) 0 (end_interval - 1)
      else interval_of_list (L.tl l) (start_interval - 1) (end_interval - 1)


let rec same_values_append (l1 : list bool) (l2 : list bool) (l3 : list bool)
    : Lemma (ensures interval_of_list (l1 @ l2 @ l3) (L.length l1) (L.length l1 + L.length l2) = l2)
    = if L.length l1 = 0 then
          if L.length l2 = 0 then ()
          else same_values_append [] (L.tl l2) l3
      else same_values_append (L.tl l1) l2 l3


let rec is_prefix (l1 : list bool) (l2 : list bool)
    : Tot bool
    = if L.length l2 < L.length l1 then false
      else match l1 with
        | [] -> true
        | hd::tl -> if hd = (L.hd l2) then is_prefix tl (L.tl l2)
                    else false


// let rec without_last (#a:Type) (l : list a {L.length l >= 1})
//     : r : list a {L.length r = L.length l - 1}
//     = match l with
//         | [el] -> []
//         | hd::tl -> hd::without_last tl


let rec is_prefix_then_is_interval (l1 : list bool) (l2 : list bool)
    : Lemma (requires is_prefix l1 l2)
            (ensures interval_of_list l2 0 (L.length l1) = l1)
    = match l1 with
        | [] -> ()
        | hd::tl ->
            assert (hd = L.hd l1);
            is_prefix_then_is_interval tl (L.tl l2)


let indefinite_description_tot_bool (a:Type) (p : (a -> bool) {exists x. p x})
  : Tot (w : a {p w})
  = admit()


// let indefinite_description_ghost_bool (a:Type) (p : (a -> bool) {exists x. p x})
//   : GTot (x : a {p x})
//   = let w = indefinite_description_tot_bool a p in
//     let x = Ghost.reveal w in
//     x


let extract_value (p : ((list bool) -> bool) {exists x . p x}) : (list bool) =
    let value : (list bool) = indefinite_description_tot_bool (list bool) p in
    value 