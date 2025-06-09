(*
dune build 
./_build/default/main/main.exe
*)

open Intuitionistic
open Intuitionistic_tableau

let add_header_and_footer content =
  let latex_header = "\\documentclass{article}\n\\usepackage{amsmath}\n\\begin{document}\n\\scriptsize{" in
  let latex_footer = "}\\end{document}" in
  latex_header ^ content ^ latex_footer
let compile_latex filename =
  let cmd = Printf.sprintf "latexmk -pdf -output-directory=outputs %s -f" filename in
  let exit_code = Sys.command cmd in
  if exit_code = 0 then
    Printf.printf "PDF generated successfully from %s.\n" filename
  else
    Printf.printf "latexmk failed with exit code %d for %s\n" exit_code filename

let save_to_file_and_compile_latex filename middle_content =
  let content = add_header_and_footer middle_content in
  let oc = open_out("outputs/"^filename) in
  output_string oc content;
  close_out oc;
  Printf.printf "Saved to %s\n" filename;
  compile_latex filename


let () =     
  if true then (
  let content = examples_int_tableaux () in 
  Printf.printf "%s" content;
  save_to_file_and_compile_latex "examples.tex" content

  )  
  else 
  let s = (examples_definitions ()) in 
  print_endline (s);
  let latex_header = "\\documentclass{article}\n\\usepackage{amsmath}\n\\begin{document}\n" in
  let latex_footer = "\\end{document}" in
  let full_content = latex_header ^ s ^ latex_footer in
  let oc = open_out "outputs/definitions_1_2.tex" in
  output_string oc full_content;
  close_out oc;
  print_endline "Saved to output.tex";

    let cmd = "latexmk -pdf -output-directory=outputs outputs/definitions_1_2.tex -f" in
    let exit_code = Sys.command cmd in
    if exit_code = 0 then
      print_endline "PDF generated successfully."
    else
      Printf.printf "latexmk failed with exit code %d\n" exit_code





(*

open Sintax
let example_structure_3 : structure = Structure {
  domain = ['a'; 'b'; 'c'];
  predicates_of_domain = [
    ('M', PREDICATE (2, function
      | [a; b] -> a = 'a' && b = 'b'
      | _ -> false));
    ('L', PREDICATE (0, fun _ -> true))
  ]
}
let rec loop () =
      Printf.printf "Enter a string to parse (or type 'x' to quit): ";
      let s = (examples_definitions ()) in Printf.printf "Definitions:\n%s\n" s;
      let input = read_line () in
      if input = "x" then
        Printf.printf "Exiting...\n"
      else (
        let parsed_sentence = parse_as_sentence input in
        Printf.printf "Parsed sentence: %s\n" (sentence_to_latex parsed_sentence);
        Printf.printf "Signed sentence: %s\n" (signed_sentence_to_latex (F (parsed_sentence)));
        if 1=1 then
          Printf.printf "%b\n" ( sentence_is_forced_in_structure parsed_sentence  example_structure_3);
        
        loop ()
        
      )
*)




(*


open Cmain
 
open Sintax
let world_1 : world = [1; 2; 3] in
    let world_2 : world = [1; 2; 3; 4] in

    Printf.printf "World 1: %s\n" (String.concat ", " (List.map string_of_int world_1));
    Printf.printf "World 2: %s\n" (String.concat ", " (List.map string_of_int world_2));
    Printf.printf "Is world 1 a prefix of world 2? %b\n" (world_leq world_1 world_2);
    Printf.printf "Is world 2 a prefix of world 1? %b\n" (world_leq world_2 world_1);



    let  i_phrase  = I_S (world_1, T (AND (ATOMIC "y", ATOMIC "x"))) in    
      Printf.printf "Intuitionistic signed sentence: %s\n" (intuitionistic_signed_sentence_to_latex (i_phrase));

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
    *)