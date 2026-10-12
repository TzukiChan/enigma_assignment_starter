type rotor = {
  wiring : string;
  turnover : char;
}

type oriented_rotor = {
  rotor : rotor;
  top_letter : char;
}

type config = {
  refl : string;
  rotors : oriented_rotor list;
  plugboard : (char * char) list;
}

let index c = Char.code c - Char.code 'A'

(** [wrap n] is [n] modulo 26, but always in [0] through [25].
    OCaml's [mod] gives a negative result when [n] is negative, which
    breaks the rotor math, so we fix it up here. *)
let wrap n = ((n mod 26) + 26) mod 26

let map_r_to_l wiring top_letter input_pos =
  let offset = index top_letter in
  (* which contact on the rotor actually lines up with input_pos *)
  let contact = wrap (input_pos + offset) in
  let out_contact = index wiring.[contact] in
  (* go back to the machine's coordinates *)
  wrap (out_contact - offset)

(** [letter_of_index i] is the uppercase letter at position [i] of the
    alphabet, basically the opposite of [index].
    Requires: [i] is in [0] through [25]. *)
let letter_of_index i = Char.chr (i + Char.code 'A')

let map_l_to_r wiring top_letter input_pos =
  let offset = index top_letter in
  let contact = wrap (input_pos + offset) in
  (* inverse wiring: find which right contact is wired to this letter *)
  let out_contact = String.index wiring (letter_of_index contact) in
  wrap (out_contact - offset)

let map_refl _wiring _input_pos =
  failwith "Unimplemented"

let map_plug _plugs _c =
  failwith "Unimplemented"

let cipher_char _config _c =
  failwith "Unimplemented"

let step _config =
  failwith "Unimplemented"

let cipher _config _s =
  failwith "Unimplemented"

let hours_worked = 0
