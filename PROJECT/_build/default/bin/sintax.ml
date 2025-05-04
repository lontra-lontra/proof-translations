type sentence = 
  | ATOMIC of string
  | NEG of sentence
  | AND of sentence * sentence
  | IMPLIES of sentence*sentence

let priority op =
  if op = ">" then 3
  else if op = "," then 2
  else if op = "^" then 1
  else if op = "n" then 0
  else failwith "Unknown operator"






let sentence_priority_is_bigger sentence_a sentence_b= 
  match sentence_a, sentence_b with 
  | ATOMIC _ ,ATOMIC _ -> false
              | ATOMIC _, NEG _ -> false
                    | ATOMIC _, AND _ -> false
                            | ATOMIC _, IMPLIES _ -> false
  | NEG _, ATOMIC _ -> true
              | NEG _, NEG _ -> false
                    | NEG _, AND _ -> false
                            |   NEG _, IMPLIES _ -> true
  | AND _, ATOMIC _ -> true
              | AND _, NEG _ -> true
                    | AND _, AND _ -> true
                            |   AND _, IMPLIES _ -> false
  | IMPLIES _, ATOMIC _ -> true
              | IMPLIES _, NEG _ -> true
                    | IMPLIES _, AND _ -> true
                            |   IMPLIES _, IMPLIES _ -> true
  

(*n(na^a)^n(b^nb)*)
let find_operator phrase =
    let rec aux i depth operator_location =
      if i >= String.length phrase then
        if operator_location = -1 && phrase.[0] = '(' && phrase.[String.length phrase - 1] = ')' then
          0
        else
          operator_location
      else
        let c = phrase.[i] in
        match c with
        | '(' -> aux (i + 1) (depth + 1) operator_location
        | ')' -> aux (i + 1) (depth - 1) operator_location
        | '^' | 'n' | '>' | ',' when depth = 0 ->
            let new_operator_location = 
              if operator_location = -1 || priority (String.make 1 c) > priority (String.make 1 phrase.[operator_location]) 
              then i
              else operator_location
            in
            aux (i + 1) depth new_operator_location
        | _ -> aux (i + 1) depth operator_location
    in
    aux 0 0 (-1)


let find_subphrases phrase =
let operator_location = find_operator phrase in

match phrase.[operator_location] with
| 'n' -> [String.sub phrase (operator_location + 1) (String.length phrase - operator_location - 1)]
| '(' -> [String.sub phrase (1) (String.length phrase - 2)]
| '^'| '>' -> 
  [
    String.sub phrase 0 operator_location;
    String.sub phrase (operator_location + 1) (String.length phrase - operator_location - 1)
  ]
| ',' ->
  let rec aux_comma acc start i depth =
  if i >= String.length phrase then
    if start < i then List.rev (String.sub phrase start (i - start) :: acc)
    else List.rev acc
  else
    let c = phrase.[i] in (* ai []*)
    match c with
    | '(' -> aux_comma acc start (i + 1) (depth + 1)
    | ')' -> aux_comma acc start (i + 1) (depth - 1)
    | ',' when depth = 0 ->
      aux_comma (String.sub phrase start (i - start) :: acc) (i + 1) (i + 1) depth
    | _ -> aux_comma acc start (i + 1) depth
  in
  aux_comma [] 0 0 0
| _ -> ["_"]



let rec parse_as_sentence phrase = 
  if String.length phrase = 0 then
    ATOMIC ""
  else 
    let operator_location = find_operator phrase in
    if operator_location = -1 then
        ATOMIC phrase
    else
      let operator = String.make 1 phrase.[operator_location] in
      let subphrases = find_subphrases phrase in
      match operator with
      | "^" -> AND (parse_as_sentence (List.nth subphrases 0), parse_as_sentence (List.nth subphrases 1))
      | "n" -> NEG (parse_as_sentence (List.nth subphrases 0))
      | "(" -> parse_as_sentence (List.nth subphrases 0)
      | ">" -> IMPLIES (parse_as_sentence (List.nth subphrases 0), parse_as_sentence (List.nth subphrases 1))
      | _ -> ATOMIC operator



let rec sentence_to_string expr =
  match expr with
  | ATOMIC s -> s
  | NEG s -> Printf.sprintf "n(%s)" (sentence_to_string s)
  | AND (s1, s2) -> Printf.sprintf "(%s)^(%s)" (sentence_to_string s1) (sentence_to_string s2)
  | IMPLIES (s1, s2) -> Printf.sprintf "(%s)>(%s)" (sentence_to_string s1) (sentence_to_string s2)



let sequence_of_sentences_to_string sentences =
  String.concat "," (List.map sentence_to_string sentences)



  

  let rec smart_midle_of_sentence_to_latex ?upper_sentence expr =
    let upper_sentence = match upper_sentence with
      | Some u -> u
      | None -> expr
    in
    let str = match expr with
      | ATOMIC s -> s
      | NEG s -> Printf.sprintf "\\neg %s"
                   (smart_midle_of_sentence_to_latex ~upper_sentence:expr s)
      | AND (s1, s2) -> Printf.sprintf "%s \\land %s"
                          (smart_midle_of_sentence_to_latex ~upper_sentence:expr s1)
                          (smart_midle_of_sentence_to_latex ~upper_sentence:expr s2)
      | IMPLIES (s1, s2) -> Printf.sprintf "%s \\rightarrow %s"
                              (smart_midle_of_sentence_to_latex ~upper_sentence:expr s1)
                              (smart_midle_of_sentence_to_latex ~upper_sentence:expr s2)
    in
    if sentence_priority_is_bigger expr upper_sentence then
      "(" ^ str ^ ")"
    else
      str
  
      

let sentence_to_latex expr = 
  "$"^smart_midle_of_sentence_to_latex expr^"$"

  let sequence_of_sentences_to_latex sentences =
    let len = List.length sentences in
    if len <= 3 then
      String.concat ", " (List.map sentence_to_latex sentences)
    else
      let first = sentence_to_latex (List.nth sentences 0) in
      let last = sentence_to_latex (List.nth sentences (len - 1)) in
      String.concat ", " [first; "\\dots"; last]
  