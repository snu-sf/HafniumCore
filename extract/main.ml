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

let shuffle: 'a list -> 'a list = fun xs ->
  let xis = List.map (fun x -> (Random.bits (), x)) xs in
  let yis = List.sort (fun x0 x1 -> Stdlib.compare (fst x0) (fst x1)) xis in
  List.map snd yis

let cl2s = fun cl -> String.concat "" (List.map (String.make 1) cl)

let print_val = let rec go v =
  match v with
  | Vnat n -> print_string ((string_of_int n) ^ " ")
  | Vptr cts -> print_string "[" ; List.iter go cts ; print_string "]" in
fun v -> go v ; print_endline " "

let handle_Event = fun e k ->
  match e with
  | ENB -> failwith "NB OCCURED"
  | EUB -> failwith "UB OCCURED"
  (* | Syscall (['p'], [v]) -> print_val v ; k (Obj.magic ()) *)
  | ESyscall ('p'::[], v::[]) -> print_val v ; k (Obj.magic ())
  | ESyscall ('g'::[], []) -> let x = read_int() in k (Obj.magic (Vnat x))
  | ESyscall (cl, vs) -> print_endline (cl2s cl) ;
(* print_val (List.nth vs 0) ; *)
(* print_int (length cl) ; *)
(* print_int (length vs) ; *)
                        failwith "UNSUPPORTED SYSCALL"
  | EYield -> print_endline "yielding" ; k (Obj.magic ())
  | _ -> failwith "NO MATCH"

let rec run t =
  match observe t with
  | RetF r -> r
  | TauF t -> run t
  | VisF (e, k) -> handle_Event e (fun x -> run (k x))









(* let rr_match h rr = function
 * | [] -> triggerUB h
 * | t :: ts ->
 *   (match observe t with
 *    | RetF _ -> lazy (Coq_go (TauF (rr ts)))
 *    | TauF u -> lazy (Coq_go (TauF (rr (u :: ts))))
 *    | VisF (o, k) ->
 *      lazy (Coq_go (VisF (o, (fun x -> rr (shuffle ((k x) :: ts)))))))
 * 
 * (\** val round_robin :
 *     (__ coq_Event, 'a1) coq_IFun -> ('a1, 'a2) itree list -> ('a1, 'a2) itree **\)
 * 
 * let rec round_robin h q =
 *   rr_match h (round_robin h) q
 * 
 * (\** val run_till_event_aux :
 *     ((__ coq_Event, 'a1) itree -> (__ coq_Event, 'a1) itree) -> (__
 *     coq_Event, 'a1) itree -> (__ coq_Event, 'a1) itree **\)
 * 
 * let run_till_event_aux rr q =
 *   match observe q with
 *   | RetF _ -> q
 *   | TauF u -> lazy (Coq_go (TauF (rr u)))
 *   | VisF (o, k) -> handle_Event o k
 * 
 * (\** val run_till_event :
 *     (__ coq_Event, 'a1) itree -> (__ coq_Event, 'a1) itree **\)
 * 
 * let rec run_till_event q =
 *   run_till_event_aux run_till_event q *)


let rec my_rr q =
  (my_rr_match (fun _ -> shuffle) (fun _ _ _ -> handle_Event)
     (fun q -> match q with
               | [] -> []
               | _ :: _ -> my_rr q)) q

(* let rec my_rr q =
 *   let q = my_rr_once q in
 *   let q = List.filter (fun i -> match observe i with RetF _ -> false | _ -> true) q in
 *   match q with
 *   | [] -> ()
 *   | _ :: _ -> my_rr q *)

let main =
  Random.self_init();
  print_endline "" ;
  run (eval_program LoadStore.program) ;
  print_endline "-----------------------------------" ;
  run (eval_program Rec.program) ;
  print_endline "-----------------------------------" ;
  run (eval_program MutRec.program) ;
  print_endline "-----------------------------------" ;
  run (eval_program Move.program) ;
  print_endline "-----------------------------------" ;
  run (eval_program CoqCode.program) ;
  print_endline "-----------------------------------" ;
  run (eval_program Control.program) ;
  print_endline "-----------------------------------" ;
  run (round_robin (fun _ -> shuffle) (List.map eval_program Concur.programs)) ;
  (* print_endline "-----------------------------------" ;
   * my_rr (List.map eval_program Concur.programs) ; *)
  ()
