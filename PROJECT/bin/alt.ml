(* TODO discuss this
type t_justification = 
  | CONTRADICTION_rule of signed_sentence list
  | F_NEG_rule of  alt_proof_tree 
  | T_NEG_rule of  alt_proof_tree 
  | F_AND_rule of  alt_proof_tree * alt_proof_tree
  | T_AND_rule of  alt_proof_tree 

and alt_proof_tree =
   signed_sentence list * t_justification


  let rec convert_proof_tree (pt : proof_tree) : alt_proof_tree =
    match pt with
    | CONTRADICTION signed_sentence_list ->
        (signed_sentence_list, CONTRADICTION_rule signed_sentence_list)
  
    | F_NEG (signed_sentence_list, subtree) ->
        let converted_subtree = convert_proof_tree subtree in
        (signed_sentence_list, F_NEG_rule converted_subtree)
  
    | T_NEG (signed_sentence_list, subtree) ->
        let converted_subtree = convert_proof_tree subtree in
        (signed_sentence_list, T_NEG_rule converted_subtree)
  
    | F_AND (signed_sentence_list, left, right) ->
        let converted_left = convert_proof_tree left in
        let converted_right = convert_proof_tree right in
        (signed_sentence_list, F_AND_rule (converted_left, converted_right))
  
    | T_AND (signed_sentence_list, subtree) ->
        let converted_subtree = convert_proof_tree subtree in
        (signed_sentence_list, T_AND_rule converted_subtree)
  





  let rec alt_proof_tree_to_string ?(depth=0) (signed_sentence_list, justification : alt_proof_tree) : string =
    let indent = String.make depth ' ' in
    let ss_str = signed_sentence_list_to_string signed_sentence_list in
    match justification with
    | CONTRADICTION_rule _ ->
        Printf.sprintf "%sCONTRADICTION[%s]" indent ss_str
  
    | F_NEG_rule subtree ->
        Printf.sprintf "%sF_NEG[%s] -> [\n%s\n%s]"
          indent ss_str
          (alt_proof_tree_to_string ~depth:(depth + 2) subtree)
          indent
  
    | T_NEG_rule subtree ->
        Printf.sprintf "%sT_NEG[%s] -> [\n%s\n%s]"
          indent ss_str
          (alt_proof_tree_to_string ~depth:(depth + 2) subtree)
          indent
  
    | F_AND_rule (left, right) ->
        Printf.sprintf "%sF_AND[%s] -> [\n%s,\n%s\n%s]"
          indent ss_str
          (alt_proof_tree_to_string ~depth:(depth + 2) left)
          (alt_proof_tree_to_string ~depth:(depth + 2) right)
          indent
  
    | T_AND_rule subtree ->
        Printf.sprintf "%sT_AND[%s] -> [\n%s\n%s]"
          indent ss_str
          (alt_proof_tree_to_string ~depth:(depth + 2) subtree)
          indent
  



    let accumulate_alt_proof_tree tree =
      let rec aux accumulated (signed_sentence_list, justification) =
        let new_signed_sentence_list = union_lists accumulated signed_sentence_list in
        match justification with
        | CONTRADICTION_rule _ ->
            (new_signed_sentence_list, CONTRADICTION_rule new_signed_sentence_list)
    
        | F_NEG_rule subtree ->
            let updated_subtree = aux new_signed_sentence_list subtree in
            (new_signed_sentence_list, F_NEG_rule updated_subtree)
    
        | T_NEG_rule subtree ->
            let updated_subtree = aux new_signed_sentence_list subtree in
            (new_signed_sentence_list, T_NEG_rule updated_subtree)
    
        | F_AND_rule (left, right) ->
            let updated_left = aux new_signed_sentence_list left in
            let updated_right = aux new_signed_sentence_list right in
            (new_signed_sentence_list, F_AND_rule (updated_left, updated_right))
    
        | T_AND_rule subtree ->
            let updated_subtree = aux new_signed_sentence_list subtree in
            (new_signed_sentence_list, T_AND_rule updated_subtree)
      in
      aux [] tree



*)