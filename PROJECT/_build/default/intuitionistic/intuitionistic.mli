open Sintax
type type_of_element_in_domain = char
type domain = type_of_element_in_domain list
type sequence_of_integers = int  list


type r = sequence_of_integers list 


type predicate = 
  | PREDICATE of int * (type_of_element_in_domain list -> bool)




type structure = Structure of { 
  domain : domain; (* <-> constant symbols of the language of the structure *)
  predicates_of_domain : (char * predicate) list; 
}

type frame = Frame of {
  r : r;  
  c : sequence_of_integers -> structure;  
}

(*val structure_to_latex : structure -> string*)
val r_to_latex : sequence_of_integers list -> string
val sequence_of_integers_to_latex : sequence_of_integers -> string
val frame_to_latex : frame -> string
val structure_to_latex : structure  -> string
val leq_sequence_of_integers : sequence_of_integers -> sequence_of_integers -> bool
val examples_intuituinistic : unit -> string
val sentence_is_forced_in_structure : sentence -> structure -> bool
