open Lang
open LangTest

open List
open String



open CategoryKleisli
open CategoryOps
open Datatypes
open FMapAList
open Function
open ITreeDefinition
open Interp
open List0
open List1
open MapDefault
open Maps
open Monad
open Nat
open Recursion
open RelDec
open String0
open Subevent
open Sum
open Traversable
open Sflib



let cl2s = fun cl -> String.concat "" (List.map (String.make 1) cl)

let print_val = let rec go v =
  match v with
  | Vnat n -> print_string ((string_of_int n) ^ " ")
  | Vptr cts -> print_string "[" ; List.iter go cts ; print_string "]" in
fun v -> go v ; print_endline " "

let handle_Event = fun e k -> match e with
  | NB -> failwith "NB OCCURED"
  | UB -> failwith "UB OCCURED"
  (* | Syscall (['p'], [v]) -> print_val v ; k (Obj.magic ()) *)
  | Syscall ('p'::[], v::[]) -> print_val v ; k (Obj.magic ())
  | Syscall (cl, vs) -> print_endline (cl2s cl) ;
(* print_val (List.nth vs 0) ; *)
(* print_int (length cl) ; *)
(* print_int (length vs) ; *)
                        failwith "UNSUPPORTED SYSCALL"
  | _ -> failwith "NO MATCH"

let rec run t =
  match observe t with
  | RetF r -> r
  | TauF t -> run t
  | VisF (e, k) -> handle_Event e (fun x -> run (k x))

let main = run (eval_stmt load_store_applied)
