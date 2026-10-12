open OUnit2
open Enigma

(* wirings used across the tests *)
let identity = "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
let swap_ab = "BACDEFGHIJKLMNOPQRSTUVWXYZ"
let rotor_I = "EKMFLGDQVZNTOWYHXUSPAIBRCJ"
let rotor_II = "AJDKSIRUXBLHWTMCQGZNPYFVOE"
let rotor_III = "BDFHJLCPRTXVZNYEIWGAKMUSQO"
let refl_B = "YRUHQSLDPXNGOKMIEBFZCWVJAT"
let refl_C = "FVPJIAOYEDRZXWGCTKUQSBNMHL"

let rot_I = { wiring = rotor_I; turnover = 'Q' }
let rot_II = { wiring = rotor_II; turnover = 'E' }
let rot_III = { wiring = rotor_III; turnover = 'V' }

(** [chars_of s] is the list of characters in [s], in order. *)
let chars_of s = List.init (String.length s) (String.get s)

(** [make_config refl rotors tops plugboard] is a machine with reflector
    [refl] and [rotors] (left to right), where the i-th rotor starts with
    the i-th letter of [tops] on top.
    Requires: [rotors] and [tops] have the same length. *)
let make_config refl rotors tops plugboard =
  let oriented =
    List.map2
      (fun rotor top_letter -> { rotor; top_letter })
      rotors (chars_of tops)
  in
  { refl; rotors = oriented; plugboard }

(* no rotors, no plugs, identity reflector, should do nothing at all *)
let do_nothing_machine = make_config identity [] "" []

(* the I-II-III / reflector B setup from the handout *)
let historical_aaa = make_config refl_B [ rot_I; rot_II; rot_III ] "AAA" []

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

let map_plug_test name plugs c expected =
  name >:: fun _ ->
    assert_equal expected (map_plug plugs c) ~printer:(String.make 1)

let cipher_char_test name config c expected =
  name >:: fun _ ->
    assert_equal expected (cipher_char config c) ~printer:(String.make 1)

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

let plugs_az_xy = [ ('A', 'Z'); ('X', 'Y') ]

let map_plug_tests = [
  map_plug_test "empty plugboard leaves M unchanged" [] 'M' 'M';
  map_plug_test "plugboard AZ maps A to Z" [ ('A', 'Z') ] 'A' 'Z';
  map_plug_test "plugboard AZ maps Z to A" [ ('A', 'Z') ] 'Z' 'A';
  map_plug_test "plugboard AZ XY maps X to Y" plugs_az_xy 'X' 'Y';
  map_plug_test "plugboard AZ XY maps Y to X" plugs_az_xy 'Y' 'X';
  map_plug_test "plugboard AZ XY still maps A to Z" plugs_az_xy 'A' 'Z';
  map_plug_test "plugboard AZ XY leaves B unchanged" plugs_az_xy 'B' 'B';
  (* order of pairs / letters inside a pair shouldn't matter *)
  map_plug_test "plugboard YX ZA maps A to Z" [ ('Y', 'X'); ('Z', 'A') ] 'A' 'Z';
  map_plug_test "plugboard AB CD EF maps F to E"
    [ ('A', 'B'); ('C', 'D'); ('E', 'F') ] 'F' 'E';
]

let cipher_char_tests = [
  cipher_char_test "empty machine maps A to A" do_nothing_machine 'A' 'A';
  cipher_char_test "empty machine maps Z to Z" do_nothing_machine 'Z' 'Z';
  cipher_char_test "I-II-III at AAA maps G to P" historical_aaa 'G' 'P';
  cipher_char_test "I-II-III at AAA maps P back to G" historical_aaa 'P' 'G';
  cipher_char_test "I-II-III at AAA maps A to U" historical_aaa 'A' 'U';
  cipher_char_test "I-II-III at AAA maps Z to H" historical_aaa 'Z' 'H';
  cipher_char_test "I-II-III at AAA maps M to R" historical_aaa 'M' 'R';
  cipher_char_test "plugboard AZ on I-II-III at AAA maps A to H"
    { historical_aaa with plugboard = [ ('A', 'Z') ] } 'A' 'H';
  ("I-II-III at AAA maps the whole alphabet" >:: fun _ ->
     assert_equal "UEJOBTPZWCNSRKDGVMLFAQIYXH"
       (String.map (cipher_char historical_aaa) identity)
       ~printer:Fun.id);
  ("cipher_char does not move the rotors" >:: fun _ ->
     (* same letter twice in a row should give the same answer *)
     let first = cipher_char historical_aaa 'G' in
     let second = cipher_char historical_aaa 'G' in
     assert_equal first second ~printer:(String.make 1));
]

let suite =
  "Enigma test suite" >::: List.flatten [
    index_tests;
    map_r_to_l_tests;
    map_l_to_r_tests;
    map_refl_tests;
    map_plug_tests;
    cipher_char_tests;
  ]

let () = run_test_tt_main suite
