
let rec run t =
  match observe t with
  | RetF r -> r
  | TauF t -> run t
  | VisF (e, k) -> failwith "EVENT OCCURED"

let main = run (eval_imp load_store_applied)
