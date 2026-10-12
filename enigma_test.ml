open OUnit2
open Enigma

let index_test name input expected =
  name >:: fun _ ->
    assert_equal expected (index input)

let suite =
  "Enigma test suite" >::: [
    index_test "index of A is 0" 'A' 0;
  ]

let () = run_test_tt_main suite
