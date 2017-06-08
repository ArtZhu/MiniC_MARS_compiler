(*
 * file: label.ml
 * author: Bob Muller
 * date: Feb. 20, 2009
*)
type t = string

let counter = ref 0

let fromString (x:string) : t = x

let fresh() =
  let freshNumber = !counter
  in
    (
      counter := !counter + 1;
      "l" ^ (string_of_int freshNumber)
    )

let format x = x
