
let handle_Event e k = match e with
  | NB -> failwith "NB OCCURED" ; k (Obj.magic ())
  | UB -> failwith "UB OCCURED" ; k (Obj.magic ())

let rec run t =
  match observe t with
  | RetF r -> r
  | TauF t -> run t
  | VisF (e, k) -> handle_Event e (fun x -> run (k x))

let main = run (eval_imp load_store_applied)
