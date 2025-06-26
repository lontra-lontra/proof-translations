open Intuitionistic
open Sintax

(* Define the type for signed sentences *)
type signed_sentence =
  | F of sequence_of_integers*sentence
  | T of sequence_of_integers*sentence
type signed_sentence_list = signed_sentence list

let signed_sentence_to_latex (ss : signed_sentence) : string =
  match ss with
  | F (seq, s) ->
      Printf.sprintf "F_{%s}(%s)" (sequence_of_integers_to_latex seq) (sentence_to_latex s)
  | T (seq, s) ->
      Printf.sprintf "T_{%s}(%s)" (sequence_of_integers_to_latex seq) (sentence_to_latex s)

let signed_sentence_list_to_latex (ss_list : signed_sentence_list) : string =
  
  "[" ^ String.concat ", " (List.map signed_sentence_to_latex ss_list) ^ "]"

(* Define the type for sequences of integers *)
let all_sequences_of_integers (list : signed_sentence_list) : sequence_of_integers list =
  List.map (function
    | F (seq, _) -> seq
    | T (seq, _) -> seq) list

let all_not_smaller_than_sequences (sequences : sequence_of_integers list ) (p : sequence_of_integers) : sequence_of_integers list =
  List.filter (fun seq -> not (leq_sequence_of_integers seq p )) sequences

let all_greater_than_sequences (sequences : sequence_of_integers list ) (p : sequence_of_integers) : sequence_of_integers list =
  List.filter (fun seq ->  (leq_sequence_of_integers p seq )) sequences


let lowest_sequence (list : sequence_of_integers list) : sequence_of_integers =
  match list with
  | [] -> failwith "smallest_sequence: empty list"
  | h :: t ->
      List.fold_left (fun acc seq ->
        if leq_sequence_of_integers acc seq then acc else seq) h t

let greatest_sequences (list : sequence_of_integers list) : sequence_of_integers list =
  List.filter (fun p ->
    not (List.exists (fun q -> leq_sequence_of_integers p q && p <> q) list)
  ) list

let longest_sequences (list : sequence_of_integers list) : sequence_of_integers list =
  let max_length = List.fold_left (fun acc seq ->
    max acc (List.length seq)) 0 list in
  List.filter (fun seq -> List.length seq = max_length) list

(* Inference function *)
let cardinal_minus a b =
  List.filter (fun x -> not (List.exists (fun y -> signed_sentence_to_latex x = signed_sentence_to_latex y) b)) a

let all_p_in_l_such_that_p_sentence_is_not_in_signed_sentence_list (l : signed_sentence_list) (sigma: signed_sentence): sequence_of_integers list =
  
  List.filter (fun p -> 
      let p_sigma = match sigma with
    | T (_, sentence) -> T (p, sentence)
    | F (_, sentence) -> F (p, sentence)
      in
      not (List.exists (fun ss -> ss = p_sigma) l)) (all_sequences_of_integers l)

    
(*
  let p_sigma = match sigma with
    | T (_, sentence) -> T (p, sentence)
    | F (_, sentence) -> F (p, sentence)
  in
  if List.exists (fun ss -> ss = p_sigma) l then
    []
  else
    [p_sigma]
  *)

let inference_function  (l : signed_sentence_list) (sigma : signed_sentence) : signed_sentence_list list  =
    if not (List.exists (fun ss -> ss = sigma) l) then [l] else
    let l_minous_sigma = cardinal_minus l [sigma] in
      let p = (match sigma with
        | F (p, _) -> p
        | T (p, _ ) -> p )in
        (*Printf.printf "\\\\p = $%s$\n" (sequence_of_integers_to_latex p);*)
        let not_new = (
        let not_repeated = (all_p_in_l_such_that_p_sentence_is_not_in_signed_sentence_list l sigma) in
        (*Printf.printf "\\\\not repeated = $%s$\n" (String.concat ", " (List.map sequence_of_integers_to_latex not_repeated));*)
        let greater_then_p_and_not_repeated = all_greater_than_sequences not_repeated p in
        (*Printf.printf "\\\\greater then p and not repeated = $%s$\n" (String.concat ", " (List.map sequence_of_integers_to_latex greater_then_p_and_not_repeated));*)
        match greater_then_p_and_not_repeated with
        | [] -> p
        | x -> lowest_sequence (x)) 
      in 
      let longer_than_p = all_greater_than_sequences (all_sequences_of_integers l) p in
      let greatest = greatest_sequences longer_than_p in
      let greatest_and_longests = longest_sequences greatest in
      let one_of_greatest_and_longests = 
        match greatest_and_longests with
        | [] -> failwith "No greatest and longest sequence found"
        | h :: _ -> h in
      let new_p =
        one_of_greatest_and_longests @ [0] 
      in (
      match sigma with
      | T (_, ATOMIC _) ->  [l_minous_sigma@ [sigma]] 
      | F (_, ATOMIC _) ->  [l_minous_sigma@ [sigma]] 
      | T (_, NEG s) -> [l_minous_sigma@ [sigma] @ [F (not_new, s)]]
      | F (_, NEG s) -> [l_minous_sigma@ [sigma] @ [T (new_p, s)]]
      | T (_, AND (s1, s2)) -> [l_minous_sigma@ [sigma] @ [T (p, s1); T (p, s2)]]
      | F (_, AND (s1, s2)) -> [l_minous_sigma@ [sigma] @ [F (p,s1)]; l_minous_sigma@ [sigma] @ [F (p,s2)]]
      | T (_, OR (s1, s2)) -> [l_minous_sigma@ [sigma] @ [T (p, s1)]; l_minous_sigma@ [sigma] @ [T (p, s2)]]
      | F (_, OR (s1, s2)) -> [l_minous_sigma@ [sigma] @ [F (p, s1); F (p, s2)]]
      | T (_, IMPLIES (s1, s2)) -> [l_minous_sigma@ [sigma] @ [F (not_new, s1)];l_minous_sigma@ [sigma] @ [T (not_new, s2)]]
      | F (_, IMPLIES (s1, s2)) -> [l_minous_sigma@ [sigma] @ [T (p, s1)]; l_minous_sigma@ [sigma] @ [F (p, s2)]])




(* Example usage *) 
let examples_intuituinistic_tableaux () = 
  let ss_list = [
    T ([], ATOMIC "a"); 
    T ([0], ATOMIC "b"); 
    T ([1], ATOMIC "c");
    F ([0;0], ATOMIC "d");
    T ([0;0;0], ATOMIC "a"); 
    T ([0;0;0;0], ATOMIC "b") 
  ] in
  let s1 = " Signed sentence list : $" ^ (signed_sentence_list_to_latex ss_list) ^ "$\n" in

  let seqs = all_sequences_of_integers ss_list in
  let s2 = "\\\\ All sequences of integers: $[" ^
    (String.concat "; " (List.map sequence_of_integers_to_latex seqs)) ^ "]$\n" in

  let p = [0] in
  let greater_seqs = all_not_smaller_than_sequences seqs p in
  let s3 = "\\\\ Sequences on $" ^
    (String.concat "; " (List.map sequence_of_integers_to_latex seqs)) ^
    "$ bigger then $" ^ (sequence_of_integers_to_latex p) ^ "$: $[" ^
    (String.concat "; " (List.map sequence_of_integers_to_latex greater_seqs)) ^ "]$\n" in

  let smallest = lowest_sequence greater_seqs in
  let s4 = "\\\\ Smallest sequence on $" ^
    (String.concat "; " (List.map sequence_of_integers_to_latex greater_seqs)) ^
    "$ bigger then $" ^ (sequence_of_integers_to_latex p) ^ "$: $" ^
    (sequence_of_integers_to_latex smallest) ^ "$\n" in

  let biggest = greatest_sequences seqs in
  let s5 = "\\\\ Biggest sequences: of $[" ^
    (String.concat "; " (List.map sequence_of_integers_to_latex seqs)) ^
    "]$ =  $[" ^
    (String.concat "; " (List.map sequence_of_integers_to_latex biggest)) ^ "]$\n" in

  let smart_example = [
    [T ([0], ATOMIC "A"); 
     F ([1;0;0], NEG (ATOMIC "A"));
     F ([0;0;0;0], NEG (ATOMIC "A"));
     T ([], IMPLIES (ATOMIC "A", ATOMIC "B"));
     F ([], IMPLIES (ATOMIC "A", ATOMIC "B"))];
  ] in 
  let sigma1 = F ([1;0;0], NEG (ATOMIC "A")) in
  let s6 = "\\\\f (\n" ^
    "\\\\ $" ^ (signed_sentence_to_latex sigma1) ^ "$, \n" ^
    "\\\\ $" ^ (signed_sentence_list_to_latex (List.hd smart_example)) ^ "$) \n" in

  let result1 = inference_function (List.hd smart_example) sigma1 in
  let s7 = "= " ^
    (String.concat ""
      (List.mapi (fun i res ->
        "\\\\ " ^ string_of_int (i+1) ^ ": $" ^ (signed_sentence_list_to_latex res) ^ "$\n"
      ) result1)
    ) in

  let sigma2 = F ([], IMPLIES (ATOMIC "A", ATOMIC "B")) in
  let s8 = "\\\\f (\n" ^
    "\\\\ $" ^ (signed_sentence_to_latex sigma2) ^ "$, \n" ^
    "\\\\ $" ^ (signed_sentence_list_to_latex (List.hd smart_example)) ^ "$) \n" in

  let result2 = inference_function (List.hd smart_example) sigma2 in
  let s9 = "= " ^
    (String.concat ""
      (List.mapi (fun i res ->
        "\\\\ " ^ string_of_int (i+1) ^ ": $" ^ (signed_sentence_list_to_latex res) ^ "$\n"
      ) result2)
    ) in

  s1 ^ s2 ^ s3 ^ s4 ^ s5 ^ s6 ^ s7 ^ s8 ^ s9


  