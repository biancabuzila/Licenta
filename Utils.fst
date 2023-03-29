module Utils

module L = FStar.List.Tot.Base
open FStar.Mul


let rec my_nth (#a:Type) (l : list a) (n:int {n >= 0 && n < L.length l}) : a
    = if n = 0 then L.hd l
      else my_nth (L.tl l) (n - 1)


let integer_to_char_sequence (x:int) : list FStar.String.char
    = FStar.String.list_of_string (string_of_int x)


let rec n_falses (n:int)
    : Pure (list bool) (requires n >= 0)
                       (ensures fun r -> L.length r = n)
    = if n = 0 then []
      else false::(n_falses (n - 1))


let smaller (a : list nat) (b : list nat {L.length a = L.length b && L.length a = 5})
    : bool
    = L.hd a < L.hd b ||
      (L.hd a <= L.hd b && my_nth a 1 < my_nth b 1) ||
      (L.hd a <= L.hd b && my_nth a 1 <= my_nth b 1 && my_nth a 2 < my_nth b 2) ||
      (L.hd a <= L.hd b && my_nth a 1 <= my_nth b 1 && my_nth a 2 <= my_nth b 2 &&  my_nth a 3 < my_nth b 3) ||
      (L.hd a <= L.hd b && my_nth a 1 <= my_nth b 1 && my_nth a 2 <= my_nth b 2 &&  my_nth a 3 <= my_nth b 3 && my_nth a 4 < my_nth b 4)


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
