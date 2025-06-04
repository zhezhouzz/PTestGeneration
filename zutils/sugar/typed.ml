type ('a, 'b) typed = { ty : 'a; x : 'b } [@@deriving sexp, show, eq, ord]

let _get_ty x = x.ty
let _get_x x = x.x
let ( #: ) x ty = { x; ty }

let ( #-> ) : 't 'a 'b. ('t, 'a) typed -> ('a -> 'b) -> ('t, 'b) typed =
 fun { x; ty } f -> (f x)#:ty

let ( #=> ) : 't 's 'a. ('t, 'a) typed -> ('t -> 's) -> ('s, 'a) typed =
 fun { x; ty } f -> x#:(f ty)

let ( #: ) x ty = { x; ty }
let ( #+ ) x ty = { x = x.x; ty }
let typed_from_pair (x, ty) = x#:ty
let typed_to_pair { x; ty } = (x, ty)
let fv_typed_id_to_id f e = List.map (fun x -> x.x) @@ f e
let subst_f_to_instance subst x lit e = subst x (fun _ -> lit) e
let find_in_args name l = List.find_opt (fun x -> String.equal name x.x) l

(** override show *)
let layout_typed f g { x; ty } = Printf.sprintf "%s: %s" (f x) (g ty)

let layout_typed_var g { x; ty } = Printf.sprintf "%s: %s" x (g ty)

let layout_typed_vars ?(line_length = 200) splitter g ctx =
  match ctx with
  | [] -> "∅"
  | l -> SugarAux.bound_split_by line_length splitter (layout_typed_var g) l

let show_typed (f : 'a -> string) (g : 'b -> string) { x; ty } =
  Printf.sprintf "(%s: %s)" (f x) (g ty)

let eq_typed f p1 p2 = equal_typed (fun _ _ -> true) f p1 p2
let typed_eq = eq_typed
