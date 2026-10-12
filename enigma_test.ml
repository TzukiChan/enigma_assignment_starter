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

(* full cipher test setup from section 33 *)
let fun_az = make_config refl_B [ rot_I; rot_II; rot_III ] "FUN" [ ('A', 'Z') ]

let index_test name input expected =
  name >:: fun _ ->
    assert_equal expected (index input) ~printer:string_of_int

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

(** [tops_of config] is the top letters of [config]'s rotors read left to
    right, e.g. ["KDO"]. *)
let tops_of config =
  config.rotors
  |> List.map (fun { top_letter; _ } -> String.make 1 top_letter)
  |> String.concat ""

let step_test name config expected_tops =
  name >:: fun _ ->
    assert_equal expected_tops (tops_of (step config)) ~printer:Fun.id

(** [tops_after_steps config n] is the top letters of [config] followed by
    the top letters after each of the next [n] steps.
    Requires: [n >= 0]. *)
let rec tops_after_steps config n =
  if n = 0 then [ tops_of config ]
  else tops_of config :: tops_after_steps (step config) (n - 1)

let step_sequence_test name config expected =
  name >:: fun _ ->
    assert_equal expected
      (tops_after_steps config (List.length expected - 1))
      ~printer:(String.concat " ")

let cipher_test name config input expected =
  name >:: fun _ ->
    assert_equal expected (cipher config input) ~printer:Fun.id

(** [round_trip_test name config plaintext] checks the reflector symmetry:
    ciphering the ciphertext again from the same starting [config] gives
    back [plaintext]. *)
let round_trip_test name config plaintext =
  name >:: fun _ ->
    let ciphertext = cipher config plaintext in
    assert_equal plaintext (cipher config ciphertext) ~printer:Fun.id

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
  map_plug_test "plugboard YX ZA maps A to Z"
    [ ('Y', 'X'); ('Z', 'A') ] 'A' 'Z';
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

let step_tests = [
  (* rule 1 *)
  step_test "rightmost rotor steps every character" historical_aaa "AAB";
  step_test "single rotor wraps from Z to A"
    (make_config refl_B [ rot_I ] "Z" []) "A";
  step_test "single rotor sitting on its turnover only moves itself"
    (make_config refl_B [ rot_I ] "Q" []) "R";
  step_test "step with no rotors does nothing" do_nothing_machine "";
  ("step keeps reflector and plugboard the same" >:: fun _ ->
     let before = { historical_aaa with plugboard = plugs_az_xy } in
     let after = step before in
     assert_equal before.refl after.refl;
     assert_equal before.plugboard after.plugboard);
  (* rule 2 *)
  step_test "rightmost rotor at V turnover steps the middle rotor"
    (make_config refl_B [ rot_I; rot_II; rot_III ] "AAV" []) "ABW";
  step_test "middle rotor at E turnover steps itself and the left one"
    (make_config refl_B [ rot_I; rot_II; rot_III ] "AEA" []) "BFB";
  step_test "leftmost rotor at its turnover does not step by itself"
    (make_config refl_B [ rot_I; rot_II; rot_III ] "QAA" []) "QAB";
  step_test "two rotors, right one at Q steps the left one"
    (make_config refl_B [ rot_II; rot_I ] "AQ" []) "BR";
  step_test "four rotors, turnover carries through the middle"
    (make_config refl_B [ rot_III; rot_II; rot_I; rot_III ] "AAQV" [])
    "ABRW";
  (* rule 3 *)
  step_test "middle rotor only steps once even with two reasons to"
    (make_config refl_B [ rot_I; rot_II; rot_III ] "AEV" []) "BFW";
  step_sequence_test "III-II-I from KDO matches handout"
    (make_config refl_B [ rot_III; rot_II; rot_I ] "KDO" [])
    [ "KDO"; "KDP"; "KDQ"; "KER"; "LFS"; "LFT"; "LFU" ];
  step_sequence_test "III-II-I from VDP matches handout"
    (make_config refl_B [ rot_III; rot_II; rot_I ] "VDP" [])
    [ "VDP"; "VDQ"; "VER"; "WFS"; "WFT" ];
]

let cipher_tests = [
  cipher_test "empty message stays empty" historical_aaa "" "";
  cipher_test "empty machine leaves HELLO alone" do_nothing_machine "HELLO"
    "HELLO";
  cipher_test "I-II-III at FUN with AZ plug turns YNGXQ into OCAML" fun_az
    "YNGXQ" "OCAML";
  cipher_test "I-II-III at AAA turns AAAAA into BDZGO" historical_aaa "AAAAA"
    "BDZGO";
  ("cipher steps before the first letter, not after" >:: fun _ ->
     let expected = String.make 1 (cipher_char (step historical_aaa) 'G') in
     assert_equal expected (cipher historical_aaa "G") ~printer:Fun.id);
]

(* bigger setup for whole-machine tests: other order, reflector C, lots of
   plugs, and a start that crosses the double step pretty fast *)
let busy_machine =
  make_config refl_C [ rot_III; rot_II; rot_I ] "KDO"
    [ ('A', 'B'); ('C', 'D'); ('E', 'F'); ('G', 'H'); ('I', 'J');
      ('K', 'L'); ('M', 'N'); ('O', 'P'); ('Q', 'R'); ('S', 'T');
      ('U', 'V'); ('W', 'X'); ('Y', 'Z') ]

let whole_machine_tests = [
  round_trip_test "HELLO round trips on I-II-III at AAA" historical_aaa
    "HELLO";
  round_trip_test "HELLO round trips on FUN with AZ plug" fun_az "HELLO";
  round_trip_test "long message round trips on the busy machine"
    busy_machine "THEQUICKBROWNFOXJUMPSOVERTHELAZYDOGTHEQUICKBROWNFOX";
  round_trip_test "single rotor machine round trips"
    (make_config refl_B [ rot_II ] "D" [ ('H', 'Q') ]) "ATTACKATDAWN";
  ("no letter ever comes out as itself" >:: fun _ ->
     let output = cipher historical_aaa (String.make 200 'E') in
     assert_bool "found an E in the output" (not (String.contains output 'E')));
  ("ciphertext is as long as the plaintext" >:: fun _ ->
     assert_equal 26 (String.length (cipher busy_machine identity))
       ~printer:string_of_int);
  ("cipher leaves the original config untouched" >:: fun _ ->
     let _ = cipher historical_aaa "SOMELONGERMESSAGE" in
     assert_equal "AAA" (tops_of historical_aaa) ~printer:Fun.id);
]

let suite =
  "Enigma test suite" >::: List.flatten [
    index_tests;
    map_r_to_l_tests;
    map_l_to_r_tests;
    map_refl_tests;
    map_plug_tests;
    cipher_char_tests;
    step_tests;
    cipher_tests;
    whole_machine_tests;
  ]

let () = run_test_tt_main suite
