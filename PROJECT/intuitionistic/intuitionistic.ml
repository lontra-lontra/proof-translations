open Sintax

type sequence_of_integers = int  list

let sequence_of_integers_to_latex (seq : sequence_of_integers) : string =
  let elements = List.map string_of_int seq in
  "\\langle " ^ (String.concat ", " elements) ^ " \\rangle"

  let rec is_prefix p q =
  match p, q with
  | [], _ -> true 
  | x::xs, y::ys when x = y -> is_prefix xs ys
  | _ -> false

let leq_sequence_of_integers (p : sequence_of_integers) (q :sequence_of_integers ) : bool =
  is_prefix p q

type r = sequence_of_integers list 


let r_to_latex (r : r) : string =
  let seqs = List.map sequence_of_integers_to_latex r in
  "\\{" ^ (String.concat ", " seqs) ^ "\\}"

type type_of_element_in_domain = char


type domain = type_of_element_in_domain list

let domain_example : domain = ['a'; 'b'; 'c']

let domain_to_latex (domain : domain) : string =
  "\\{" ^ (String.concat ", " (List.map (Printf.sprintf "'%c'") domain)) ^ "\\}"

type predicate = 
  | PREDICATE of int * (type_of_element_in_domain list -> bool)


let rec all_tuples n domain =
  if n = 0 then [[]]
  else
    List.concat (
      List.map (fun x ->
        List.map (fun tl -> x :: tl) (all_tuples (n - 1) domain)
      ) domain
    )

let tuple_to_latex tuple =
  "(" ^ (String.concat ", " (List.map (String.make 1) tuple)) ^ ")"

let predicate_over_domain_to_latex (dom : domain) (pred : predicate) : string =
  match pred with
  | PREDICATE (arity, f) ->
      let tuples = all_tuples arity dom in
      let results = List.map (fun tup ->
        let result = f tup in
        tuple_to_latex tup ^ " \\Rightarrow " ^ (if result then "\\text{true}" else "\\text{false}")
      ) tuples in
      String.concat " \\\\\n" results


(*here we define a structure directly with a respective language, defining a language would do nothing and be too metalinguistic*)
type structure = Structure of { 
  domain : domain; (* <-> constant symbols of the language of the structure *)
  predicates_of_domain : (char * predicate) list; 
}

let rec sentence_is_forced_in_structure (sentence: sentence) (structure : structure) : bool =
  match structure with
  | Structure {predicates_of_domain; _} ->
    match sentence with
    | ATOMIC s ->
        let predicate_is_there = (List.exists (fun (name, pred) ->
          let name_first_char = String.get s 0 in 
          name_first_char = name &&
          (
            match pred with
            | PREDICATE (0, _) -> true 
            | PREDICATE (_, _) -> false
          ) 
        ) predicates_of_domain ) in 
        if predicate_is_there then

          List.exists (fun (name, pred) ->
            let name_first_char = String.get s 0 in 
            name_first_char = name &&
            (
              match pred with
              | PREDICATE (0, f) -> f []
              | PREDICATE (_, _) -> false
            ) 
          ) predicates_of_domain
            else 
            failwith "Predicate not found or not a 0-arity predicate in structure"
    | NEG s -> not (sentence_is_forced_in_structure s structure)
    | AND (s1, s2) ->
        sentence_is_forced_in_structure s1 structure && sentence_is_forced_in_structure s2 structure
    | OR (s1, s2) ->
        sentence_is_forced_in_structure s1 structure || sentence_is_forced_in_structure s2 structure
    | IMPLIES (s1, s2) ->
        not (sentence_is_forced_in_structure s1 structure) || sentence_is_forced_in_structure s2 structure           


let all_atomic_sentences_that_are_true_in_structure (structure : structure) : sentence list =
  let Structure { predicates_of_domain; _ } = structure in
  List.filter (fun (_, pred) ->
    match pred with
    | PREDICATE (0, f) -> f [] (* Check if the predicate is true for the empty tuple *)
    | _ -> false
  ) predicates_of_domain
  |> List.map (fun (name, _) -> ATOMIC (String.make 1 name))



let structure_to_latex: structure -> string = function
  | Structure { domain; predicates_of_domain } ->
      let domain_latex = domain_to_latex domain in
      let predicates_latex = 
        String.concat ", " (List.map (fun (name, pred) ->
          Printf.sprintf "%c: \n %s" name (predicate_over_domain_to_latex domain pred)
        ) predicates_of_domain) in
      "\\text{Structure} \\{ " ^ domain_latex ^ ", " ^ predicates_latex ^ " \\}"

type frame = Frame of {
  r : r;  
  c : sequence_of_integers -> structure;  
}


let cardinal_minus a b =
  List.filter (fun x -> not (List.exists (fun y -> sentence_to_string x = sentence_to_string y) b)) a


let all_atomic_sentences_that_are_true_in_Cp_and_are_not_true_in_Cq (frame : frame ) (p : sequence_of_integers) (q : sequence_of_integers) : sentence list  =
    Printf.printf "Checking if all atomic sentences that are true in C(%s) are true in C(%s)\n" (sequence_of_integers_to_latex p) (sequence_of_integers_to_latex q);
  let Frame { c; _ } = frame in
  let structure_p = c p in
  let structure_q = c q in
  let atomic_sentences_true_in_p = all_atomic_sentences_that_are_true_in_structure structure_p in
  let atomic_sentences_true_in_q = all_atomic_sentences_that_are_true_in_structure structure_q in
  cardinal_minus atomic_sentences_true_in_p atomic_sentences_true_in_q
  

  
let all_atomic_sentences_that_are_true_in_Cp_are_true_in_Cq (frame : frame ) (p : sequence_of_integers) (q : sequence_of_integers) : bool =
  all_atomic_sentences_that_are_true_in_Cp_and_are_not_true_in_Cq frame p q = []




let frame_to_latex (Frame { r; c }) : string =
  let r_latex = r_to_latex r in
  let c_latex = 
    "\\text{c: } \\{ " ^ 
    (String.concat ", " (List.map (fun seq -> Printf.sprintf "\\langle %s \\rangle \\mapsto %s" (sequence_of_integers_to_latex seq) (structure_to_latex (c seq))) r)) ^
    " \\}" in
  "\\text{Frame} \\{ " ^ r_latex ^ "\\, " ^ c_latex ^ " \\}"




let counterexamples (frame : frame) : sequence_of_integers*sequence_of_integers =
  flush stdout;
  let Frame { r; _ } = frame in
  let pairs = List.flatten (
    List.map (fun p ->
      List.map (fun q -> (p, q)) r
    ) r
  ) in
  match List.find_opt (fun (p, q) ->
    if leq_sequence_of_integers p q 
      then  (
      flush stdout;
      (not (all_atomic_sentences_that_are_true_in_Cp_are_true_in_Cq frame p q)) && (leq_sequence_of_integers p q)
      )
      else 
        false 
  ) pairs with
  | Some (p, q) ->
      p,q 
  | None -> [], []



let frame_is_valid (frame : frame) : bool =
  flush stdout;
  let Frame { r; _ } = frame in
  let pairs = List.flatten (
    List.map (fun p ->
      List.map (fun q -> (p, q)) r
    ) r
  ) in
  match List.find_opt (fun (p, q) ->
    if leq_sequence_of_integers p q 
      then  (
      flush stdout;
      (not (all_atomic_sentences_that_are_true_in_Cp_are_true_in_Cq frame p q)) && (leq_sequence_of_integers p q)
      )
      else 
        false 
  ) pairs with
  | Some (p, q) ->
      Printf.printf "Counterexample found: p = %s, q = %s\n"
        (sequence_of_integers_to_latex p)
        (sequence_of_integers_to_latex q);
      let diff = all_atomic_sentences_that_are_true_in_Cp_and_are_not_true_in_Cq frame p q in
      Printf.printf "Atomic sentences true in C(%s) and not in C(%s):\n%s\n"
        (sequence_of_integers_to_latex p)
        (sequence_of_integers_to_latex q)
        (String.concat ", " (List.map sentence_to_string diff));
      flush stdout;
      false
  | None -> true
let r_example : r = [
  [0];
  [0;1];
  [0;1;2];
  [0;1;2;3]
]


let example_structure : structure = Structure {
  domain = domain_example;
  predicates_of_domain = [
    ('P', PREDICATE (0, fun _ -> false));
    ('Q', PREDICATE (0, fun _ -> false))
  ]
}

let example_structure_2 : structure = Structure {
  domain = domain_example;
  predicates_of_domain = [
    ('P', PREDICATE (0, fun _ -> false));
    ('Q', PREDICATE (0, fun _ -> true))
  ]
}

let example_structure_3 : structure = Structure {
  domain = domain_example;
  predicates_of_domain = [
    ('M', PREDICATE (2, function
      | [a; b] -> a = 'a' && b = 'b'
      | _ -> false));
    ('L', PREDICATE (0, fun _ -> true))
  ]

  
}


let frame_example : frame = Frame {
  r = r_example;
  c = (fun seq -> 
    match List.rev seq with
    | last::_ -> if last = 0 then example_structure else (if last = 1 then example_structure_2 else example_structure_3)
    (*if the last element is divisible by 3, return example_structure, if it is 1, return example_structure_2, otherwise return example_structure_3*)
    | [] -> example_structure
  )
}



let f_example_structure : structure = Structure {
  domain = domain_example;
  predicates_of_domain = [
  ]
}

let f_example_structure_2 : structure = Structure {
  domain = domain_example;
  predicates_of_domain = [
    ('P', PREDICATE (0, fun _ -> false))
  ]
}

let f_example_structure_3 : structure = Structure {
  domain = domain_example;
  predicates_of_domain = [
    ('P', PREDICATE (0, fun _ -> false));
    ('Q', PREDICATE (0, fun _ -> true))
  ]  
}

let f_example_structure_4 : structure = Structure {
  domain = domain_example;
  predicates_of_domain = [
    ('P', PREDICATE (0, fun _ -> true));
    ('Q', PREDICATE (0, fun _ -> true))
  ]

  
}

let frame_validity_example : frame = Frame {
  r = r_example;
  c = (fun seq -> 
    match List.rev seq with
    | last::_ -> if last = 0 then f_example_structure else (if last = 1 then f_example_structure_2 else (if last = 2 then f_example_structure_3 else f_example_structure_4))
    (*if the last element is divisible by 3, return example_structure, if it is 1, return example_structure_2, otherwise return example_structure_3*)
    | [] -> example_structure
  )
}




let examples_intuituinistic () =
  let s1 = Printf.sprintf "leq-sequence-of-integers $%s$ $\\leq$ $%s$: %b\n"
    (sequence_of_integers_to_latex [1;2])
    (sequence_of_integers_to_latex [1;2;3])
    (leq_sequence_of_integers [1;2] [1;2;3])
  in
  let s2 = Printf.sprintf "\\\\\n frame-to-latex: $%s$\n" (frame_to_latex frame_example)
  in
  let s3 = ( Printf.sprintf "\\ Is frame example valid? %b\n" (frame_is_valid frame_example) )
  in
  let s4 =
    match counterexamples frame_example with
    | ([], []) -> "\\ No counterexamples found.\n"
    | (p, q) ->
        Printf.sprintf "\\ Counterexample: p = %s, q = %s\n"
          (sequence_of_integers_to_latex p)
          (sequence_of_integers_to_latex q)
  in
  let s5 = Printf.sprintf "\\\\\n frame-to-latex: $%s$\n" (frame_to_latex frame_validity_example)
  in
  let s6 = ( Printf.sprintf "Is frame example valid? %b\n" (frame_is_valid frame_validity_example) )
  in
    let s7 =
    match counterexamples frame_validity_example with
    | ([], []) -> "\\ No counterexamples found.\n"
    | (po, qo) ->
        Printf.sprintf "\\ Counterexample: $p = %s, q = %s$\n"
          (sequence_of_integers_to_latex po)
          (sequence_of_integers_to_latex qo)
  in
  s1 ^ s2 ^ s3 ^ s4 ^ s5^ s6^ s7
