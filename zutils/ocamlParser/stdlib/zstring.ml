open String
let starts_with ~prefix s =
  let len_s = length s
  and len_pre = length prefix in
  let rec aux i =
    if i = len_pre then true
    else if unsafe_get s i <> unsafe_get prefix i then false
    else aux (i + 1)
  in len_s >= len_pre && aux 0
