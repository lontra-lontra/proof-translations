(*opam exec -- dune build; opam exec ---dune exec hello*)

open Sintax
(* PART I : Verifying sequent proofs*)
type sequent =
  | SEQ of sentence list * sentence list

type justification = 
  | AXIOM_RULE of sentence 
  | NEG_L_RULE of sequent_proof * sentence
  | NEG_R_RULE of sequent_proof * sentence
  | AND_L_RULE of sequent_proof * sentence
  | AND_R_RULE of (sequent_proof * sequent_proof) * sentence
  | IMPLIES_L_RULE of (sequent_proof * sequent_proof) * sentence
  | IMPLIES_R_RULE of sequent_proof * sentence

and sequent_proof = 
    | PROOF of sequent * justification

let sequent_to_string sequent =
  match sequent with
    |SEQ (left, right) -> Printf.sprintf "%s > %s" (sequence_of_sentences_to_string left) (sequence_of_sentences_to_string right)




let sequent_to_latex sequent =
  match sequent with
    |SEQ (left, right) -> Printf.sprintf "%s $\\vdash$ %s" (sequence_of_sentences_to_latex left) (sequence_of_sentences_to_latex right)


let justification_to_string justification = 
  match justification with
    | AXIOM_RULE s -> Printf.sprintf "Axiom: %s" (sentence_to_string s)
    | NEG_L_RULE (_, s) -> Printf.sprintf "Negation Left: on %s"  (sentence_to_string s)
    | NEG_R_RULE (_, s) -> Printf.sprintf "Negation Right: on %s" (sentence_to_string s)
    | AND_L_RULE (_, s) -> Printf.sprintf "And Left: on %s" (sentence_to_string s)
    | AND_R_RULE (_, s) -> Printf.sprintf "And Right: on %s" (sentence_to_string s)
    | IMPLIES_L_RULE ((_, _), s) -> Printf.sprintf "Implies Left: on %s" (sentence_to_string s)
    | IMPLIES_R_RULE (_, s) -> Printf.sprintf "Implies Right: on %s" (sentence_to_string s)
      

let justification_to_latex justification = 
  match justification with
    | AXIOM_RULE s -> Printf.sprintf "Ax %s" (sentence_to_latex s)
    | NEG_L_RULE (_, s) -> Printf.sprintf "$\\neg$L %s"  (sentence_to_latex s)
    | NEG_R_RULE (_, s) -> Printf.sprintf "$\\neg$R %s" (sentence_to_latex s)
    | AND_L_RULE (_, s) -> Printf.sprintf "$\\land$L %s" (sentence_to_latex s)
    | AND_R_RULE (_, s) -> Printf.sprintf "$\\land$R %s" (sentence_to_latex s)
    | IMPLIES_L_RULE ((_, _), s) -> Printf.sprintf "$\\rightarrow$L %s" (sentence_to_latex s)
    | IMPLIES_R_RULE (_, s) -> Printf.sprintf "$\\rightarrow$R %s" (sentence_to_latex s)
      




    

let rec sequent_proof_to_middle_latex proof =
  match proof with
  | PROOF (sequent, justification) ->
      let subproofs , bussproofstype=
        match justification with
        | AXIOM_RULE _ -> [], "\\AxiomC{}\\UnaryInfC"
        | NEG_L_RULE (subproof, _) | NEG_R_RULE (subproof, _) ->
            [sequent_proof_to_middle_latex subproof], "\\UnaryInfC"
        | AND_L_RULE (subproof, _) ->
            [sequent_proof_to_middle_latex subproof],  "\\UnaryInfC"
        | AND_R_RULE ((subproof1, subproof2), _) ->
            [sequent_proof_to_middle_latex subproof1; sequent_proof_to_middle_latex subproof2], "\\BinaryInfC"
          | IMPLIES_L_RULE ((subproof1, subproof2), _) ->
              [sequent_proof_to_middle_latex subproof1; sequent_proof_to_middle_latex subproof2], "\\BinaryInfC"
          | IMPLIES_R_RULE (subproof, _) ->
              [sequent_proof_to_middle_latex subproof], "\\UnaryInfC"
      in
      let subproofs_str = String.concat "\n" subproofs in
      Printf.sprintf "%s\n\\RightLabel{\\scriptsize{%s}}\n%s{%s}" 
        
        subproofs_str
        (justification_to_latex justification)
        bussproofstype
        (sequent_to_latex sequent)


let sequent_proof_to_latex proof = 
  let middle = sequent_proof_to_middle_latex proof in 
  Printf.sprintf "
\\begin{prooftree}
%s\n 
\\end{prooftree}
" middle

(*TODO find a smater way *)
let cardinal_minus a b =
  List.filter (fun x -> not (List.exists (fun y -> sentence_to_string x = sentence_to_string y) b)) a

let vectorwise f list1 list2 =
  if List.length list1 <> List.length list2 then
    failwith "Lists must have the same length"
  else
    List.map2 f list1 list2

let true_in_all bool_vector =
  List.fold_left (&&) true bool_vector

let cardinal_equal a b =
  let result = cardinal_minus a b = [] && cardinal_minus b a = [] in
  result

let cardinal_contains a b =
  let result = cardinal_minus b a = [] in
  result

let cardinal_union sequent_lists =
    List.fold_left (List.fold_left (fun acc sequent ->
      if List.exists (fun existing -> sentence_to_string existing = sentence_to_string sequent) acc then acc
      else sequent :: acc)) []
      sequent_lists

let union_lists l1 l2 =
  let rec add_unique acc = function
    | [] -> acc
    | x::xs -> if List.mem x acc then add_unique acc xs else add_unique (x::acc) xs
  in
  add_unique l1 l2


let check_pattern_between_sequents(sa : sequent) (sb : sequent) (necessary_elements: sentence list list) =
  match (sa, sb) with
  | (SEQ (left_side_a, right_side_a ), SEQ (left_side_b, right_side_b)) ->
      if (true_in_all ( vectorwise  cardinal_contains ([left_side_a;right_side_a;left_side_b;right_side_b]) necessary_elements )) then
      

      let expected_sequent = [
          cardinal_union  [left_side_a ; (List.nth necessary_elements 2)] ;
          cardinal_union [right_side_a ; (List.nth necessary_elements 3)];
          cardinal_union [left_side_b ; (List.nth necessary_elements 0)];
          cardinal_union [right_side_b ; (List.nth necessary_elements 1)]
      ] in
      if (cardinal_equal (List.nth expected_sequent 0)  (List.nth expected_sequent 2) ) 
      && (cardinal_equal (List.nth expected_sequent 1)  (List.nth expected_sequent 3) ) 

        then
          true
        else begin 
          Printf.printf "{\n";
          Printf.printf "GIVEN SEQUENTS:\n\n\n";

          Printf.printf "%s\n" (sequent_to_string sa);
          Printf.printf "------------------------------------------------\n";
          Printf.printf "%s\n" (sequent_to_string sb);
          
          Printf.printf "EXPECTED ELEMENTS:\n\n\n";
          Printf.printf "{%s}  > "  ( sequence_of_sentences_to_string (List.nth necessary_elements 0 )) ;
          Printf.printf "{%s} \n "  ( sequence_of_sentences_to_string (List.nth necessary_elements 1 )) ;
          Printf.printf "------------------------------------------------\n";
          Printf.printf "{%s}  > "  ( sequence_of_sentences_to_string (List.nth necessary_elements 2 ))  ;
          Printf.printf "{%s} \ \n "  ( sequence_of_sentences_to_string (List.nth necessary_elements 3 ))  ;

          (Printf.printf "EXPECTED sequent :\n\n\n";
          Printf.printf "{%s}  > "  ( sequence_of_sentences_to_string (List.nth expected_sequent 0 )) ;
          Printf.printf "{%s} \n "  ( sequence_of_sentences_to_string (List.nth expected_sequent 1)) ;
          Printf.printf "------------------------------------------------\n";
          Printf.printf "{%s}  > "  ( sequence_of_sentences_to_string (List.nth expected_sequent 2 ))  ;
          Printf.printf "{%s} \ \n "  ( sequence_of_sentences_to_string (List.nth expected_sequent 3))  ; 
          Printf.printf "}\n";
);
          false
        end else begin

          Printf.printf "{\n";

          Printf.printf "GIVEN SEQUENTS:\n\n\n";

          Printf.printf "%s\n" (sequent_to_string sa);
          Printf.printf "------------------------------------------------\n";
          Printf.printf "%s\n" (sequent_to_string sb);



          Printf.printf "EXPECTED ELEMENTS:\n\n\n";
          Printf.printf "{%s}  > "  ( sequence_of_sentences_to_string (List.nth necessary_elements 0 )) ;
          Printf.printf "{%s} \n "  ( sequence_of_sentences_to_string (List.nth necessary_elements 1 )) ;
          Printf.printf "------------------------------------------------\n";
          Printf.printf "{%s}  > "  ( sequence_of_sentences_to_string (List.nth necessary_elements 2 ))  ;
          Printf.printf "{%s} \ \n "  ( sequence_of_sentences_to_string (List.nth necessary_elements 3 ))  ;
          Printf.printf "}\n";
        false
        end


let rec verify_proof (sequent_proof : sequent_proof) : bool =
  Printf.printf "Verifying proof: %s\n" (match sequent_proof with PROOF (s, _) -> sequent_to_string s);
  match sequent_proof with

  | PROOF (SEQ (left_side, right_side), AXIOM_RULE a) ->
      if List.mem a left_side && List.mem a right_side then
        true
      else begin 
        Printf.printf "Axiom rule failed: %s\n" (sequent_to_string (SEQ (left_side, right_side)));
        false
      end
      
  | PROOF (sequent, NEG_R_RULE (PROOF (premisse, justification), NEG a)) ->
        if check_pattern_between_sequents premisse sequent 
          [
          [a]     ;    [];     (*is in sequent  *)
          []         ; [NEG a] (*is in premise  *)
        ] 
        then 
          verify_proof (PROOF (premisse, justification))
        else 
          false

  | PROOF (sequent, NEG_L_RULE (PROOF (premisse, justification), NEG a)) ->
    if check_pattern_between_sequents premisse sequent 
      [
      []     ;    [a];     (*is in sequent  *)
      [NEG a]         ; [] (*is in premise  *)
    ] 
    then 
      verify_proof (PROOF (premisse, justification))
    else 
      false

  | PROOF (sequent, AND_L_RULE (PROOF (premisse, justification), AND (a, b))) ->
    if check_pattern_between_sequents (premisse) (sequent) 
      [
      [a;b]     ;    [];     (*is in sequent  *)
      [AND (a, b)]         ; [] (*is in premise  *)
    ] 
    then 
      verify_proof (PROOF (premisse, justification))
    else 
      false
  | PROOF (sequent, AND_R_RULE ((PROOF (premisse1, justification1), PROOF (premisse2, justification2)), AND (a, b))) ->
    if (check_pattern_between_sequents premisse1 sequent 
      [
      []     ;    [b];     (*is in sequent  *)
      []         ; [AND (a, b)] (*is in premise  *)
    ] 
    && check_pattern_between_sequents premisse2 sequent 
      [
      []     ;    [a];     (*is in sequent  *)
      []         ; [AND (a, b)] (*is in premise  *)
    ]) 
    || (check_pattern_between_sequents premisse1 sequent 
      [
      []     ;    [a];     (*is in sequent  *)
      []         ; [AND (a, b)] (*is in premise  *)
    ] 
    && check_pattern_between_sequents premisse2 sequent 
      [
      [a]     ;    [b];     (*is in sequent  *)
      [IMPLIES (a, b)]         ; [] (*is in premise  *)
    ])
    then 
      verify_proof (PROOF (premisse1, justification1)) && verify_proof (PROOF (premisse2, justification2))
    else 
      false
    | PROOF (sequent, IMPLIES_R_RULE (PROOF (premisse, justification), IMPLIES (a, b))) ->
      if check_pattern_between_sequents (premisse) (sequent) 
        [
        [a]     ;    [b];     (*is in sequent  *)
        []         ; [IMPLIES (a, b)] (*is in premise  *)
      ] 
      then 
        verify_proof (PROOF (premisse, justification))
      else 
        false
    | PROOF (sequent, IMPLIES_L_RULE ((PROOF (premisse1, justification1), PROOF (premisse2, justification2)), IMPLIES (a, b))) ->
      if (check_pattern_between_sequents premisse1 sequent 
        [
        []     ;    [a];     (*is in sequent  *)
        []         ; [IMPLIES (a, b)] (*is in premise  *)
      ] 
      && check_pattern_between_sequents premisse2 sequent 
        [
        [b]     ;    [];     (*is in sequent  *)
        []         ; [IMPLIES (a, b)] (*is in premise  *)
      ]) 
      || (check_pattern_between_sequents premisse1 sequent 
        [
        [b]     ;    [];     (*is in sequent  *)
        []         ; [IMPLIES (a, b)] (*is in premise  *)
      ] 
      && check_pattern_between_sequents premisse2 sequent 
        [
        []     ;    [a];     (*is in sequent  *)
        []         ; [IMPLIES (a, b)] (*is in premise  *)
      ])
      then 
        verify_proof (PROOF (premisse1, justification1)) && verify_proof (PROOF (premisse2, justification2))
      else 
        false
        
  | _ -> 
      failwith "Invalid proof structure"




(* PART II : Defining tableux proofs*)

type signed_sentence =
  | T of sentence
  | F of sentence

let signed_sentence_to_string expr =
    match expr with
    | T s -> Printf.sprintf "T(%s)" (sentence_to_string s)
    | F s -> Printf.sprintf "F(%s)" (sentence_to_string s)

let signed_sentence_to_latex expr =
      match expr with
      | T s -> Printf.sprintf "T(%s)" (sentence_to_latex s)
      | F s -> Printf.sprintf "F(%s)" (sentence_to_latex s)

let cardinal_in a b =
    List.exists (fun x -> signed_sentence_to_string a = signed_sentence_to_string x) b


let signed_sentence_list_to_string signed_sentences =
  String.concat ", " (List.map (function
    | T s -> Printf.sprintf "T(%s)" (sentence_to_string s)
    | F s -> Printf.sprintf "F(%s)" (sentence_to_string s)
  ) signed_sentences)

  let signed_sentence_list_to_latex signed_sentences =
    let len = List.length signed_sentences in
    if len <= 3 then
      String.concat ", " (List.map signed_sentence_to_latex signed_sentences)
    else
      let first = signed_sentence_to_latex (List.nth signed_sentences 0) in
      let second = signed_sentence_to_latex (List.nth signed_sentences 1) in
      let before_last = signed_sentence_to_latex (List.nth signed_sentences (len - 2)) in
      let last = signed_sentence_to_latex (List.nth signed_sentences (len - 1)) in
      String.concat ", " [first; second; " $\\dots$ "; before_last; last]
  
  


type proof_tree =
  | CONTRADICTION of signed_sentence list
  | F_NEG of signed_sentence list * proof_tree
  | T_NEG of signed_sentence list * proof_tree
  | F_AND of signed_sentence list * proof_tree * proof_tree
  | T_AND of signed_sentence list * proof_tree 
  | F_IMPLIES of signed_sentence list * proof_tree 
  | T_IMPLIES of signed_sentence list * proof_tree *proof_tree


(*TODO find more elegant way *)
(*TODO remove useless strings*)
let get_proof_tree_signed_sentence_list_and_proof_tree_list tree =
  match tree with
  | CONTRADICTION signed_sentence_list -> "CONTRADICTION", signed_sentence_list ,  []
  | F_NEG (signed_sentence_list, proof_tree) -> "F_NEG", signed_sentence_list,[proof_tree]
  | T_NEG (signed_sentence_list, proof_tree) -> "T_NEG", signed_sentence_list,[proof_tree]
  | F_AND (signed_sentence_list, proof_tree1, proof_tree2) -> "F_AND", signed_sentence_list,[proof_tree1; proof_tree2]
  | T_AND (signed_sentence_list, proof_tree) -> "T_AND", signed_sentence_list,[proof_tree]
  | F_IMPLIES (signed_sentence_list, proof_tree) -> "F_IMPLIES", signed_sentence_list, [proof_tree]
  | T_IMPLIES (signed_sentence_list, proof_tree1, proof_tree2) -> "T_IMPLIES", signed_sentence_list,[proof_tree1; proof_tree2]
  

let rec proof_tree_to_string ?(depth=0) tree =
  let operation, signed_sentence_list, proof_tree_list = get_proof_tree_signed_sentence_list_and_proof_tree_list tree in
  let indent = String.make depth ' ' in
  match proof_tree_list with
  | [one] -> 
      Printf.sprintf "%s%s[%s] -> [\n%s\n%s]" 
        indent 
        operation 
        (signed_sentence_list_to_string signed_sentence_list) 
        (proof_tree_to_string ~depth:(depth + 2) one)
        indent
  | [one; two] -> 
      Printf.sprintf "%s%s[%s] -> [\n%s,\n%s\n%s]" 
        indent 
        operation 
        (signed_sentence_list_to_string signed_sentence_list)
        (proof_tree_to_string ~depth:(depth + 2) one)
        (proof_tree_to_string ~depth:(depth + 2) two)
        indent
  | [] ->
      Printf.sprintf "%s%s[%s]" 
        indent 
        operation 
        (signed_sentence_list_to_string signed_sentence_list)
  | _ -> failwith "Invalid proof tree structure"


  let rec proof_tree_to_middle_latex tree =
    let _, signed_sentence_list, proof_tree_list = get_proof_tree_signed_sentence_list_and_proof_tree_list tree in
    let signed_sentences_latex = signed_sentence_list_to_latex signed_sentence_list in
    match proof_tree_list with
    | [one] ->
        Printf.sprintf "%s\n\\UnaryInfC{%s}" 
          (proof_tree_to_middle_latex one)
          (signed_sentences_latex)
    | [one; two] ->
        Printf.sprintf "%s\n%s\n\\BinaryInfC{%s}"
          (proof_tree_to_middle_latex one)
          (proof_tree_to_middle_latex two)
          (signed_sentences_latex)
    | [] ->
        Printf.sprintf "\\AxiomC{%s}" (signed_sentences_latex)
    | _ -> failwith "Invalid proof tree structure"
  
  let proof_tree_to_latex tree =
    let middle = proof_tree_to_middle_latex tree in
    Printf.sprintf "
  \\begin{prooftree}
  \\rootAtTop
  %s
  \\end{prooftree}
  " middle
  
  
  

  
let rec is_contradiction signed_sentence_list = 

  match signed_sentence_list with
  | T sentence :: rest ->  
    if List.exists (function F s -> sentence_to_string s = sentence_to_string sentence | _ -> false) rest then
      true
    else
      is_contradiction rest
  | F sentence :: rest ->  
    if List.exists (function T s -> sentence_to_string s = sentence_to_string sentence | _ -> false) rest then
      true
    else
      is_contradiction rest
  | [] -> false
    
let find_contradictions signed_sentence_list =
  let rec aux acc remaining =
  match remaining with
  | T sentence :: rest ->  
    if List.exists (function F s -> sentence_to_string s = sentence_to_string sentence | _ -> false) rest then
    (T sentence :: F sentence :: acc)
    else
    aux acc rest
  | F sentence :: rest ->  
    if List.exists (function T s -> sentence_to_string s = sentence_to_string sentence | _ -> false) rest then
    (F sentence :: T sentence :: acc)
    else
    aux acc rest
  | [] -> acc
  in
  aux [] signed_sentence_list
    

let rec develop_signed_sentence_list_n_times signed_sentence_list n =  
  if n = 0 then begin
    Printf.printf "not found!";
    CONTRADICTION []
  end else
    if is_contradiction signed_sentence_list then
      CONTRADICTION signed_sentence_list
      else
      match signed_sentence_list with
      | T (NEG sentence) :: rest -> 
          let circulated = [F sentence] @ rest @ [T (NEG sentence)] in 
          T_NEG(signed_sentence_list, develop_signed_sentence_list_n_times circulated (n - 1))

      | F (NEG sentence) :: rest -> 
          let circulated = [T sentence] @ rest @ [F (NEG sentence)] in 
          F_NEG(signed_sentence_list, develop_signed_sentence_list_n_times  circulated (n - 1))

      | T (AND (sentence1, sentence2)) :: rest -> 
          let circulated = [T sentence1; T sentence2] @ rest @ [T (AND (sentence1, sentence2))] in 
          T_AND(signed_sentence_list, develop_signed_sentence_list_n_times  circulated (n - 1))

      | F (AND (sentence1, sentence2)) :: rest -> 
          let circulated1 = [F sentence1] @ rest @ [F (AND (sentence1, sentence2))] in 
          let circulated2 = [F sentence2] @ rest @ [F (AND (sentence1, sentence2))] in 
        F_AND(signed_sentence_list, develop_signed_sentence_list_n_times  circulated1 (n - 1), develop_signed_sentence_list_n_times  circulated2 (n - 1))

      | T (IMPLIES (sentence1, sentence2)) :: rest -> 
          let circulated1 = [F sentence1] @ rest @ [T (IMPLIES (sentence1, sentence2))] in 
          let circulated2 = [T sentence2] @ rest @ [T (IMPLIES (sentence1, sentence2))] in 
        T_IMPLIES(signed_sentence_list, develop_signed_sentence_list_n_times  circulated1 (n - 1), develop_signed_sentence_list_n_times  circulated2 (n - 1))

      | F (IMPLIES (sentence1, sentence2)) :: rest -> 
          let circulated = [T sentence1; F sentence2] @ rest @ [F (IMPLIES (sentence1, sentence2))] in 
          F_IMPLIES(signed_sentence_list, develop_signed_sentence_list_n_times  circulated (n - 1))

      | T (ATOMIC(sentence)) :: rest -> develop_signed_sentence_list_n_times ( rest@ [T (ATOMIC(sentence))] ) (n - 1)
      | F (ATOMIC(sentence)) :: rest -> develop_signed_sentence_list_n_times (rest @  [F (ATOMIC(sentence))]) (n - 1)
      | [] -> CONTRADICTION []
      

  
  
  
  
  let rec signed_sentence_list_to_sequent signed_sentence_list =
    let result = 
    match signed_sentence_list with
    | T sentence :: rest -> let SEQ(left,right) = signed_sentence_list_to_sequent(rest) in
    SEQ(sentence :: left, right)
    | F sentence :: rest -> let SEQ(left,right) = signed_sentence_list_to_sequent(rest) in
    SEQ(left , sentence :: right)
    | [] -> SEQ([],[])
  in
  result 


let find_rule_sentence tree =
  let maybe_signed_sentence =
    match tree with 
    | CONTRADICTION signed_sentence_list -> 
        Some (List.hd (find_contradictions signed_sentence_list))

    | T_NEG (signed_sentence_list, proof_tree) -> 
        let _, new_signed_sentence_list, _ = 
          get_proof_tree_signed_sentence_list_and_proof_tree_list proof_tree 
        in 
        
        List.find_opt (function 
          | T (NEG sentence) -> cardinal_in (F sentence) new_signed_sentence_list
          | _ -> false) signed_sentence_list 

    | F_NEG (signed_sentence_list, proof_tree) -> 
        let _, new_signed_sentence_list, _ = 
          get_proof_tree_signed_sentence_list_and_proof_tree_list proof_tree 
        in 
        List.find_opt (function 
          | F (NEG sentence) -> (cardinal_in (T sentence) new_signed_sentence_list ) && not (cardinal_in (T sentence) signed_sentence_list)
          | _ -> false) signed_sentence_list 

    | T_AND (signed_sentence_list, proof_tree) -> 
        let _, new_signed_sentence_list, _ = 
          get_proof_tree_signed_sentence_list_and_proof_tree_list proof_tree 
        in 
        List.find_opt (function 
          | T (AND (s1, s2)) -> 
              cardinal_in (T s1) new_signed_sentence_list && 
              cardinal_in (T s2) new_signed_sentence_list
          | _ -> false) signed_sentence_list 

    | F_AND (signed_sentence_list, proof_tree1, proof_tree2) ->
        let _, ss_list1, _ = get_proof_tree_signed_sentence_list_and_proof_tree_list proof_tree1 in
        let _, ss_list2, _ = get_proof_tree_signed_sentence_list_and_proof_tree_list proof_tree2 in
        List.find_opt (function 
          | F (AND (s1, s2)) -> 
              (cardinal_in (F s1) ss_list1 && cardinal_in (F s2) ss_list2) ||
              (cardinal_in (F s2) ss_list1 && cardinal_in (F s1) ss_list2)
        | _ -> false) signed_sentence_list 


    | T_IMPLIES (signed_sentence_list, proof_tree1, proof_tree2) ->
      let _, ss_list1, _ = get_proof_tree_signed_sentence_list_and_proof_tree_list proof_tree1 in
      let _, ss_list2, _ = get_proof_tree_signed_sentence_list_and_proof_tree_list proof_tree2 in
      List.find_opt (function 
        | T (IMPLIES (s1, s2)) -> 
            (cardinal_in (F s1) ss_list1 && cardinal_in (T s2) ss_list2) ||
            (cardinal_in (T s2) ss_list1 && cardinal_in (F s1) ss_list2)
      | _ -> false) signed_sentence_list 


    | F_IMPLIES (signed_sentence_list, proof_tree) ->
      let _, new_signed_sentence_list, _ =
        get_proof_tree_signed_sentence_list_and_proof_tree_list proof_tree
      in
      List.find_opt (function
        | F (IMPLIES (s1, s2)) ->
          cardinal_in (T s1) new_signed_sentence_list &&
          cardinal_in (F s2) new_signed_sentence_list
        | _ -> false) signed_sentence_list
  in
  match maybe_signed_sentence with
  | Some (T sentence) -> sentence
  | Some (F sentence) -> sentence
  | None -> 
      let operation, signed_sentence_list, proof_tree_list = get_proof_tree_signed_sentence_list_and_proof_tree_list tree in
      Printf.printf "Operation: %s\n" operation;
      Printf.printf "Signed Sentence List: %s\n" (signed_sentence_list_to_string signed_sentence_list);
      List.iter (fun subtree -> 
    Printf.printf "Subtree:\n%s\n" (proof_tree_to_latex subtree)
      ) proof_tree_list;
      failwith "No matching rule sentence found in proof tree"
    
    
    

  

  let rec proof_tree_to_sequent_proof tree =  
    match tree with 
    | CONTRADICTION signed_sentence_list -> PROOF(signed_sentence_list_to_sequent signed_sentence_list, AXIOM_RULE (find_rule_sentence tree))
    | T_NEG (signed_sentence_list,  proof_tree) -> 
      PROOF  ( signed_sentence_list_to_sequent signed_sentence_list , NEG_L_RULE (proof_tree_to_sequent_proof proof_tree, (find_rule_sentence tree)))
    | F_NEG (signed_sentence_list,  proof_tree) -> 
      PROOF  ( signed_sentence_list_to_sequent signed_sentence_list , NEG_R_RULE (proof_tree_to_sequent_proof proof_tree, (find_rule_sentence tree)))
    | F_AND (signed_sentence_list,  proof_tree1, proof_tree2) -> 
      PROOF  ( signed_sentence_list_to_sequent signed_sentence_list , AND_R_RULE ( (proof_tree_to_sequent_proof proof_tree1, proof_tree_to_sequent_proof proof_tree2), (find_rule_sentence tree)))
    | T_AND (signed_sentence_list, proof_tree) -> 
      PROOF (signed_sentence_list_to_sequent signed_sentence_list, AND_L_RULE (proof_tree_to_sequent_proof proof_tree, (find_rule_sentence tree)))
    | F_IMPLIES (signed_sentence_list, proof_tree) ->
    PROOF (signed_sentence_list_to_sequent signed_sentence_list, IMPLIES_R_RULE (proof_tree_to_sequent_proof proof_tree, find_rule_sentence tree))
   | T_IMPLIES (signed_sentence_list,proof_tree1, proof_tree2) ->
    PROOF (signed_sentence_list_to_sequent signed_sentence_list, IMPLIES_L_RULE ((proof_tree_to_sequent_proof proof_tree1, proof_tree_to_sequent_proof proof_tree2), find_rule_sentence tree))


  let accumulate_proof_tree tree =
    let rec aux accumulated = function
      | CONTRADICTION(sentences) ->
          let new_sentences = union_lists accumulated sentences in
          CONTRADICTION(new_sentences)
      | F_NEG(sentences, subtree) ->
          let new_sentences = union_lists accumulated sentences in
          F_NEG(new_sentences, aux new_sentences subtree)
      | T_NEG(sentences, subtree) ->
          let new_sentences = union_lists accumulated sentences in
          T_NEG(new_sentences, aux new_sentences subtree)
      | F_AND(sentences, left, right) ->
          let new_sentences = union_lists accumulated sentences in
          F_AND(new_sentences, aux new_sentences left, aux new_sentences right)
      | T_AND(sentences, subtree) ->
          let new_sentences = union_lists accumulated sentences in
      T_AND(new_sentences, aux new_sentences subtree)
      | T_IMPLIES(sentences, left, right) ->
          let new_sentences = union_lists accumulated sentences in
          T_IMPLIES(new_sentences, aux new_sentences left, aux new_sentences right)
      | F_IMPLIES(sentences, subtree) ->
          let new_sentences = union_lists accumulated sentences in
          F_IMPLIES(new_sentences, aux new_sentences subtree)
    in
    aux [] tree


    




let () =




  (* Step 1: Axiom: b ⊢ b *)
  let a = ATOMIC "a" in
  let b = ATOMIC "b" in
  let s00100 = SEQ ([NEG (NEG a);b;NEG b], [b]) in
  let p00100 = PROOF (s00100, AXIOM_RULE b) in

  let s0010 = SEQ ([NEG (NEG a);b;NEG b], []) in
  let p0010 = PROOF (s0010, NEG_L_RULE (p00100, NEG b)) in
  
  (* Step 2: NEG_R_RULE to prove ⊢ ¬b *)
  let s001 = SEQ ([NEG (NEG a);(NEG b)], [NEG b]) in
  let p001 = PROOF (s001, NEG_R_RULE (p0010, NEG b)) in
  
  (* Step 3: Axiom: a ⊢ a *)
  let s00000 = SEQ ([NEG (NEG a);NEG b; a], [a; (NEG a)]) in
  let p00000 = PROOF (s00000, AXIOM_RULE a) in

  (* Step 3: Axiom: a ⊢ a *)
  let s0000 = SEQ ([NEG (NEG a);NEG b], [a; (NEG a)]) in
  let p0000 = PROOF (s0000, NEG_R_RULE (p00000, NEG a)) in
  
  (* Step 4: NEG_L_RULE to go from [¬¬a] ⊢ a *)
  let s000 = SEQ ([NEG (NEG a);NEG b], [a]) in
  let p000 = PROOF (s000, NEG_L_RULE (p0000, NEG (NEG a))) in
  
  (* Step 5: AND_R_RULE: from ⊢ ¬b and [¬¬a] ⊢ a to [¬¬a] ⊢ ¬b ∧ a *)
  let s00 = SEQ ([NEG (NEG a);(NEG b)], [AND (NEG b, a)]) in
  let p00 = PROOF (s00, AND_R_RULE ((p000, p001), AND (NEG b, a))) in
  
  (* Step 6: AND_L_RULE: from [¬¬a ∧ ¬b] ⊢ [¬b ∧ a] to [¬¬a; ¬b] ⊢ [¬b ∧ a] *)
  let s0 = SEQ ([AND (NEG (NEG a), NEG b)], [AND (NEG b, a)]) in
  let p0 = PROOF (s0, AND_L_RULE (p00, AND (NEG (NEG a), NEG b))) in
  

  (* Print and verify *)
  Printf.printf "example of a sequent proof:\n%s\n" (sequent_proof_to_latex p0);
  Printf.printf "checking if its valid: %b\n" (verify_proof p0 ); 



     
  let example_proof_tree =
    let a = ATOMIC "a" in
    let b = ATOMIC "b" in
    F_AND ([F (AND ((NEG (AND (a, NEG a))), (NEG (AND (b, NEG b)))))],
        F_NEG([F (NEG (AND (a, NEG a)))],
          T_AND ([T (AND (a, NEG a))],
            T_NEG ([T a; T (NEG a)],
              CONTRADICTION ([T a; F a])
            ) 
          )
        ),
        F_NEG([F (NEG (AND (b, NEG b)))],
          T_AND ([T (AND (b, NEG b))],
            T_NEG ([T b; T (NEG b)],
              CONTRADICTION ([T b; F b])
            ) 
          )
        )
      )
  in
  Printf.printf "Example example of proof_tree:\n%s\n"
  (proof_tree_to_latex example_proof_tree);

    let example_proof_tree_acc = accumulate_proof_tree example_proof_tree in
        Printf.printf "example of proof_tree 'Accumulated' :\n%s\n"
          (proof_tree_to_latex example_proof_tree_acc);

    let translated_sequent_proof = proof_tree_to_sequent_proof example_proof_tree_acc in
    Printf.printf "example of proof_tree Accumulated then Translated:\n%s\n"
    (sequent_proof_to_latex translated_sequent_proof);
    Printf.printf "checking if its valid: %b\n" (verify_proof translated_sequent_proof);

    let auto_p = develop_signed_sentence_list_n_times [F (NEG(AND(a, NEG(a))))] 30 in 
      Printf.printf "Auto:\n%s\n"
    (proof_tree_to_latex auto_p);

    let auto_sequent_proof = proof_tree_to_sequent_proof (accumulate_proof_tree auto_p) in
    Printf.printf "Auto translated to sequent proof:\n%s\n" (sequent_proof_to_latex auto_sequent_proof);
    Printf.printf "Auto proof is valid: %b\n" (verify_proof auto_sequent_proof);


    let rec loop () =
      Printf.printf "Enter a string to parse (or type 'x' to quit): ";
      let input = read_line () in
      if input = "x" then
      Printf.printf "Exiting...\n"
      else
      let parsed_sentence = parse_as_sentence input in
      Printf.printf "Parsed sentence: %s\n" (sentence_to_string parsed_sentence);
      Printf.printf "Signed sentence: %s\n" (signed_sentence_to_string (F (parsed_sentence)));

      let tree = develop_signed_sentence_list_n_times [(F (parsed_sentence))] 8 in 
      Printf.printf "Proof tree:\n%s\n"
    (proof_tree_to_latex tree);

      let sequent_proof = proof_tree_to_sequent_proof ( tree) in
      Printf.printf "Translated to sequent proof:\n%s\n" (sequent_proof_to_latex sequent_proof);
      Printf.printf "Proof is valid: %b\n" (verify_proof sequent_proof);
      (* n(n(nx^x)>(nx^x))*) 
      loop ()
    in
    loop ()