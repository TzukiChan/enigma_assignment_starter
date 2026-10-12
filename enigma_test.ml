open OUnit2
open Enigma

(* wirings used across the tests *)
let identity = "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
let swap_ab = "BACDEFGHIJKLMNOPQRSTUVWXYZ"
let rotor_I = "EKMFLGDQVZNTOWYHXUSPAIBRCJ"
let rotor_III = "BDFHJLCPRTXVZNYEIWGAKMUSQO"
let refl_B = "YRUHQSLDPXNGOKMIEBFZCWVJAT"
let refl_C = "FVPJIAOYEDRZXWGCTKUQSBNMHL"

let index_test name input expected =
  name >:: fun _ ->
    assert_equal expected (index input)

let map_r_to_l_test name wiring top_letter input_pos expected =
  name >:: fun _ ->
    assert_equal expected
      (map_r_to_l wiring top_letter input_pos)
      ~printer:string_of_int

let map_l_to_r_test name wiring top_letter input_pos expected =
  name >:: fun _ ->
    assert_equal expected
      (map_l_to_r wiring top_letter input_pos)
      ~printer:string_of_int

let map_refl_test name wiring input_pos expected =
  name >:: fun _ ->
    assert_equal expected (map_refl wiring input_pos) ~printer:string_of_int

let index_tests = [
  index_test "index of A is 0" 'A' 0;
  index_test "index of Z is 25" 'Z' 25;
  index_test "index of B is 1" 'B' 1;
  index_test "index of M is 12" 'M' 12;
  index_test "index of N is 13" 'N' 13;
]

let map_r_to_l_tests = [
  map_r_to_l_test "identity wiring at A maps 0 to 0" identity 'A' 0 0;
  map_r_to_l_test "identity wiring at C still maps 5 to 5" identity 'C' 5 5;
  map_r_to_l_test "swap_ab at A maps 0 to 1" swap_ab 'A' 0 1;
  map_r_to_l_test "swap_ab at B maps 0 to 25" swap_ab 'B' 0 25;
  map_r_to_l_test "swap_ab at C maps 24 to 25" swap_ab 'C' 24 25;
  map_r_to_l_test "rotor I at A maps 0 to 4" rotor_I 'A' 0 4;
  map_r_to_l_test "rotor I at B maps 0 to 9" rotor_I 'B' 0 9;
  map_r_to_l_test "rotor III at O maps 14 to 17" rotor_III 'O' 14 17;
  map_r_to_l_test "rotor I at Z maps 25 to 3" rotor_I 'Z' 25 3;
]

let map_l_to_r_tests = [
  map_l_to_r_test "identity wiring at A maps 0 to 0" identity 'A' 0 0;
  map_l_to_r_test "identity wiring at K maps 7 to 7" identity 'K' 7 7;
  map_l_to_r_test "rotor I at A maps 0 to 20" rotor_I 'A' 0 20;
  map_l_to_r_test "rotor I at F maps 10 to 14" rotor_I 'F' 10 14;
  map_l_to_r_test "swap_ab at A maps 1 to 0" swap_ab 'A' 1 0;
  map_l_to_r_test "swap_ab at B maps 0 to 25" swap_ab 'B' 0 25;
  (* these two just undo the r_to_l cases above *)
  map_l_to_r_test "rotor III at O maps 17 back to 14" rotor_III 'O' 17 14;
  map_l_to_r_test "rotor I at Z maps 3 back to 25" rotor_I 'Z' 3 25;
]

let map_refl_tests = [
  map_refl_test "identity reflector maps 0 to 0" identity 0 0;
  map_refl_test "identity reflector maps 1 to 1" identity 1 1;
  map_refl_test "identity reflector maps 25 to 25" identity 25 25;
  map_refl_test "reflector B maps 0 to 24" refl_B 0 24;
  map_refl_test "reflector B maps 24 back to 0" refl_B 24 0;
  map_refl_test "reflector B maps 5 to 18" refl_B 5 18;
  map_refl_test "reflector C maps 0 to 5" refl_C 0 5;
  map_refl_test "reflector C maps 25 to 11" refl_C 25 11;
]

let suite =
  "Enigma test suite" >::: List.flatten [
    index_tests;
    map_r_to_l_tests;
    map_l_to_r_tests;
    map_refl_tests;
  ]

let () = run_test_tt_main suite
