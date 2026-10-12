open OUnit2
open Enigma

(* wirings used across the tests *)
let identity = "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
let swap_ab = "BACDEFGHIJKLMNOPQRSTUVWXYZ"
let rotor_I = "EKMFLGDQVZNTOWYHXUSPAIBRCJ"
let rotor_III = "BDFHJLCPRTXVZNYEIWGAKMUSQO"

let index_test name input expected =
  name >:: fun _ ->
    assert_equal expected (index input)

let map_r_to_l_test name wiring top_letter input_pos expected =
  name >:: fun _ ->
    assert_equal expected
      (map_r_to_l wiring top_letter input_pos)
      ~printer:string_of_int

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

let suite =
  "Enigma test suite" >::: List.flatten [
    index_tests;
    map_r_to_l_tests;
  ]

let () = run_test_tt_main suite
