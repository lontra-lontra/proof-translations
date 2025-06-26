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
 let example =1 in     
  if (example==1) then (
  let content = examples_intuituinistic_tableaux () in 
  Printf.printf "%s" content;
  save_to_file_and_compile_latex "examples_i.tex" content
  )else
  if (example==0) then (
  let content = examples_intuituinistic() in 
  Printf.printf "%s" content;
  save_to_file_and_compile_latex "examples_ii.tex" content
  )