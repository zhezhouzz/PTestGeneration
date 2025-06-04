module IntSet = Set.Make (struct
  let compare = compare

  type t = int
end)

module StrSet = Set.Make (struct
  let compare = String.compare

  type t = string
end)
