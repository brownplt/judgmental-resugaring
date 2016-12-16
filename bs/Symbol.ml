module type Symbol = sig
  type t
  val ord: t -> int
  val show: t -> string
end

module Make (S: Symbol) =
  struct
    include S;;
    let equal x y = S.ord x == S.ord y;;
    let hash x = S.ord x;;
  end
