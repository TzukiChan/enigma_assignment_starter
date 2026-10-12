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

(* reflector never rotates, so it's just a rotor stuck at A *)
let map_refl wiring input_pos = map_r_to_l wiring 'A' input_pos

let rec map_plug plugs c =
  match plugs with
  | [] -> c
  | (a, b) :: rest ->
      if c = a then b
      else if c = b then a
      else map_plug rest c

(** [map_rotors_r_to_l rotors input_pos] is where the signal comes out on
    the far left after entering the rightmost rotor of [rotors] at
    [input_pos]. [rotors] is ordered left to right like in [config].
    Requires: [input_pos] is in [0] through [25]. *)
let rec map_rotors_r_to_l rotors input_pos =
  match rotors with
  | [] -> input_pos
  | { rotor; top_letter } :: rest ->
      (* rest is everything to the right, and the signal hits those first *)
      map_rotors_r_to_l rest input_pos
      |> map_r_to_l rotor.wiring top_letter

(** [map_rotors_l_to_r rotors input_pos] is the return trip: the signal
    enters the leftmost rotor of [rotors] at [input_pos] and this is where
    it leaves the rightmost one.
    Requires: [input_pos] is in [0] through [25]. *)
let rec map_rotors_l_to_r rotors input_pos =
  match rotors with
  | [] -> input_pos
  | { rotor; top_letter } :: rest ->
      map_l_to_r rotor.wiring top_letter input_pos
      |> map_rotors_l_to_r rest

let cipher_char config c =
  c
  |> map_plug config.plugboard
  |> index
  |> map_rotors_r_to_l config.rotors
  |> map_refl config.refl
  |> map_rotors_l_to_r config.rotors
  |> letter_of_index
  |> map_plug config.plugboard

(** [next_letter c] is the letter after [c], wrapping ['Z'] around
    to ['A'].
    Requires: [c] is in ['A'] through ['Z']. *)
let next_letter c = letter_of_index (wrap (index c + 1))

(** [rotate orot] is [orot] turned forward by one position. *)
let rotate orot = { orot with top_letter = next_letter orot.top_letter }

(** [at_turnover orot] is whether [orot] is currently showing its own
    turnover letter. *)
let at_turnover orot = orot.top_letter = orot.rotor.turnover

(** [step_rotors is_leftmost rotors] is [rotors] (left to right) after one
    stepping event. [is_leftmost] tells whether the head of [rotors] is the
    leftmost rotor of the whole machine, since that one never gets pushed
    by its own notch. *)
let rec step_rotors is_leftmost rotors =
  match rotors with
  | [] -> []
  | [ rightmost ] -> [ rotate rightmost ]
  | current :: (right_neighbor :: _ as rest) ->
      (* decide everything from the old positions, and each rotor only
         gets one chance to move here so nothing steps twice *)
      let should_step =
        at_turnover right_neighbor
        || ((not is_leftmost) && at_turnover current)
      in
      let current = if should_step then rotate current else current in
      current :: step_rotors false rest

let step config = { config with rotors = step_rotors true config.rotors }

let cipher _config _s =
  failwith "Unimplemented"

let hours_worked = 0
