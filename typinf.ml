type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type bool =
  | True
  | False

type nat =
  | O
  | S of nat

type 'a option =
  | Some of 'a
  | None

type ('a, 'b) prod =
  | Pair of 'a * 'b

(** val fst : ('a1, 'a2) prod -> 'a1 **)

let fst = function
  | Pair (x, y) -> x

(** val snd : ('a1, 'a2) prod -> 'a2 **)

let snd = function
  | Pair (x, y) -> y

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)

(** val proj1_sig : 'a1 -> 'a1 **)

let proj1_sig e =
  e

type sumbool =
  | Left
  | Right

type 'a sumor =
  | Inleft of 'a
  | Inright

(** val plus : nat -> nat -> nat **)

let rec plus n m =
  match n with
    | O -> m
    | S p -> S (plus p m)

(** val minus : nat -> nat -> nat **)

let rec minus n m =
  match n with
    | O -> O
    | S k -> (match m with
                | O -> S k
                | S l -> minus k l)

type 'a list =
  | Nil
  | Cons of 'a * 'a list

(** val length : 'a1 list -> nat **)

let rec length = function
  | Nil -> O
  | Cons (a, m) -> S (length m)

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
    | Nil -> m
    | Cons (a, l1) -> Cons (a, (app l1 m))

(** val nth : nat -> 'a1 list -> 'a1 -> 'a1 **)

let rec nth n l default =
  match n with
    | O -> (match l with
              | Nil -> default
              | Cons (x, l') -> x)
    | S m ->
        (match l with
           | Nil -> default
           | Cons (x, t0) -> nth m t0 default)

(** val rev : 'a1 list -> 'a1 list **)

let rec rev = function
  | Nil -> Nil
  | Cons (x, l') -> app (rev l') (Cons (x, Nil))

(** val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1 **)

let rec fold_left f l a0 =
  match l with
    | Nil -> a0
    | Cons (b, t0) -> fold_left f t0 (f a0 b)

(** val split : ('a1, 'a2) prod list -> ('a1 list, 'a2 list) prod **)

let rec split = function
  | Nil -> Pair (Nil, Nil)
  | Cons (p, tl) ->
      let Pair (x, y) = p in
      let Pair (g, d) = split tl in Pair ((Cons (x, g)), (Cons (y, d)))

(** val combine : 'a1 list -> 'a2 list -> ('a1, 'a2) prod list **)

let rec combine l l' =
  match l with
    | Nil -> Nil
    | Cons (x, tl) ->
        (match l' with
           | Nil -> Nil
           | Cons (y, tl') -> Cons ((Pair (x, y)), (combine tl tl')))

(** val seq : nat -> nat -> nat list **)

let rec seq start = function
  | O -> Nil
  | S len0 -> Cons (start, (seq (S start) len0))

(** val eq_nat_dec : nat -> nat -> sumbool **)

let rec eq_nat_dec n m =
  match n with
    | O -> (match m with
              | O -> Left
              | S m0 -> Right)
    | S n0 -> (match m with
                 | O -> Right
                 | S m0 -> eq_nat_dec n0 m0)

(** val lt_eq_lt_dec : nat -> nat -> sumbool sumor **)

let rec lt_eq_lt_dec n m =
  match n with
    | O -> (match m with
              | O -> Inleft Right
              | S n0 -> Inleft Left)
    | S n0 -> (match m with
                 | O -> Inright
                 | S m0 -> lt_eq_lt_dec n0 m0)

(** val le_lt_dec : nat -> nat -> sumbool **)

let rec le_lt_dec n m =
  match n with
    | O -> Left
    | S n0 -> (match m with
                 | O -> Right
                 | S m0 -> le_lt_dec n0 m0)

type 'x compare =
  | LT
  | EQ
  | GT

module type OrderedType = 
 sig 
  type t 
  
  val compare : t -> t -> t compare
 end

module OrderedTypeFacts = 
 functor (O:OrderedType) ->
 struct 
  (** val eq_dec : O.t -> O.t -> sumbool **)
  
  let eq_dec x y =
    match O.compare x y with
      | LT -> Right
      | EQ -> Left
      | GT -> Right
  
  (** val lt_dec : O.t -> O.t -> sumbool **)
  
  let lt_dec x y =
    match O.compare x y with
      | LT -> Left
      | EQ -> Right
      | GT -> Right
  
  (** val eqb : O.t -> O.t -> bool **)
  
  let eqb x y =
    match eq_dec x y with
      | Left -> True
      | Right -> False
 end

module type UsualOrderedType = 
 sig 
  type t 
  
  val compare : t -> t -> t compare
 end

module Nat_as_OT = 
 struct 
  type t = nat
  
  (** val compare : t -> t -> nat compare **)
  
  let compare x y =
    match lt_eq_lt_dec x y with
      | Inleft s -> (match s with
                       | Left -> LT
                       | Right -> EQ)
      | Inright -> GT
 end

(** val max : nat -> nat -> nat **)

let rec max n m =
  match n with
    | O -> m
    | S n' -> (match m with
                 | O -> n
                 | S m' -> S (max n' m'))

module Raw = 
 functor (X:OrderedType) ->
 struct 
  module E = X
  
  module MX = OrderedTypeFacts(X)
  
  type elt = X.t
  
  type t = elt list
  
  (** val empty : t **)
  
  let empty =
    Nil
  
  (** val is_empty : t -> bool **)
  
  let is_empty = function
    | Nil -> True
    | Cons (x, x0) -> False
  
  (** val mem : elt -> t -> bool **)
  
  let rec mem x = function
    | Nil -> False
    | Cons (y, l) ->
        (match X.compare x y with
           | LT -> False
           | EQ -> True
           | GT -> mem x l)
  
  (** val add : elt -> t -> t **)
  
  let rec add x s = match s with
    | Nil -> Cons (x, Nil)
    | Cons (y, l) ->
        (match X.compare x y with
           | LT -> Cons (x, s)
           | EQ -> s
           | GT -> Cons (y, (add x l)))
  
  (** val singleton : elt -> t **)
  
  let singleton x =
    Cons (x, Nil)
  
  (** val remove : elt -> t -> t **)
  
  let rec remove x s = match s with
    | Nil -> Nil
    | Cons (y, l) ->
        (match X.compare x y with
           | LT -> s
           | EQ -> l
           | GT -> Cons (y, (remove x l)))
  
  (** val union : t -> t -> t **)
  
  let rec union s x =
    match s with
      | Nil -> x
      | Cons (x0, l) ->
          let rec union_aux s' = match s' with
            | Nil -> s
            | Cons (x', l') ->
                (match X.compare x0 x' with
                   | LT -> Cons (x0, (union l s'))
                   | EQ -> Cons (x0, (union l l'))
                   | GT -> Cons (x', (union_aux l')))
          in union_aux x
  
  (** val inter : t -> t -> t **)
  
  let rec inter s x =
    match s with
      | Nil -> Nil
      | Cons (x0, l) ->
          let rec inter_aux s' = match s' with
            | Nil -> Nil
            | Cons (x', l') ->
                (match X.compare x0 x' with
                   | LT -> inter l s'
                   | EQ -> Cons (x0, (inter l l'))
                   | GT -> inter_aux l')
          in inter_aux x
  
  (** val diff : t -> t -> t **)
  
  let rec diff s x =
    match s with
      | Nil -> Nil
      | Cons (x0, l) ->
          let rec diff_aux s' = match s' with
            | Nil -> s
            | Cons (x', l') ->
                (match X.compare x0 x' with
                   | LT -> Cons (x0, (diff l s'))
                   | EQ -> diff l l'
                   | GT -> diff_aux l')
          in diff_aux x
  
  (** val equal : t -> t -> bool **)
  
  let rec equal s s' =
    match s with
      | Nil -> (match s' with
                  | Nil -> True
                  | Cons (e, l) -> False)
      | Cons (x, l) ->
          (match s' with
             | Nil -> False
             | Cons (x', l') ->
                 (match X.compare x x' with
                    | LT -> False
                    | EQ -> equal l l'
                    | GT -> False))
  
  (** val subset : t -> t -> bool **)
  
  let rec subset s s' =
    match s with
      | Nil -> True
      | Cons (x, l) ->
          (match s' with
             | Nil -> False
             | Cons (x', l') ->
                 (match X.compare x x' with
                    | LT -> False
                    | EQ -> subset l l'
                    | GT -> subset s l'))
  
  (** val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1 **)
  
  let rec fold f s i =
    match s with
      | Nil -> i
      | Cons (x, l) -> fold f l (f x i)
  
  (** val filter : (elt -> bool) -> t -> t **)
  
  let rec filter f = function
    | Nil -> Nil
    | Cons (x, l) ->
        (match f x with
           | True -> Cons (x, (filter f l))
           | False -> filter f l)
  
  (** val for_all : (elt -> bool) -> t -> bool **)
  
  let rec for_all f = function
    | Nil -> True
    | Cons (x, l) ->
        (match f x with
           | True -> for_all f l
           | False -> False)
  
  (** val exists_ : (elt -> bool) -> t -> bool **)
  
  let rec exists_ f = function
    | Nil -> False
    | Cons (x, l) -> (match f x with
                        | True -> True
                        | False -> exists_ f l)
  
  (** val partition : (elt -> bool) -> t -> (t, t) prod **)
  
  let rec partition f = function
    | Nil -> Pair (Nil, Nil)
    | Cons (x, l) ->
        let Pair (s1, s2) = partition f l in
        (match f x with
           | True -> Pair ((Cons (x, s1)), s2)
           | False -> Pair (s1, (Cons (x, s2))))
  
  (** val cardinal : t -> nat **)
  
  let cardinal s =
    length s
  
  (** val elements : t -> elt list **)
  
  let elements x =
    x
  
  (** val min_elt : t -> elt option **)
  
  let min_elt = function
    | Nil -> None
    | Cons (x, l) -> Some x
  
  (** val max_elt : t -> elt option **)
  
  let rec max_elt = function
    | Nil -> None
    | Cons (x, l) ->
        (match l with
           | Nil -> Some x
           | Cons (e, l0) -> max_elt l)
  
  (** val choose : t -> elt option **)
  
  let choose s =
    min_elt s
  
  (** val compare : t -> t -> t compare **)
  
  let rec compare l s' =
    match l with
      | Nil -> (match s' with
                  | Nil -> EQ
                  | Cons (e, l0) -> LT)
      | Cons (a, l0) ->
          (match s' with
             | Nil -> GT
             | Cons (a', l') ->
                 (match X.compare a a' with
                    | LT -> LT
                    | EQ ->
                        (match compare l0 l' with
                           | LT -> LT
                           | EQ -> EQ
                           | GT -> GT)
                    | GT -> GT))
 end

module MakeRaw = 
 functor (X:UsualOrderedType) ->
 struct 
  module Raw = Raw(X)
  
  module E = X
  
  module OTFacts = OrderedTypeFacts(E)
  
  type slist =
    Raw.t
    (* singleton inductive, whose constructor was Build_slist *)
  
  (** val slist_rect : (Raw.t -> __ -> 'a1) -> slist -> 'a1 **)
  
  let slist_rect f s =
    f s __
  
  (** val slist_rec : (Raw.t -> __ -> 'a1) -> slist -> 'a1 **)
  
  let slist_rec f s =
    f s __
  
  (** val this : slist -> Raw.t **)
  
  let this s =
    s
  
  (** val coq_Build_slist' : Raw.t -> slist **)
  
  let coq_Build_slist' xs =
    xs
  
  type t = slist
  
  type elt = E.t
  
  (** val mem : elt -> t -> bool **)
  
  let mem x s =
    Raw.mem x (this s)
  
  (** val add : elt -> t -> t **)
  
  let add x s =
    coq_Build_slist' (Raw.add x (this s))
  
  (** val remove : elt -> t -> t **)
  
  let remove x s =
    coq_Build_slist' (Raw.remove x (this s))
  
  (** val singleton : elt -> t **)
  
  let singleton x =
    coq_Build_slist' (Raw.singleton x)
  
  (** val union : t -> t -> t **)
  
  let union s s' =
    coq_Build_slist' (Raw.union (this s) (this s'))
  
  (** val inter : t -> t -> t **)
  
  let inter s s' =
    coq_Build_slist' (Raw.inter (this s) (this s'))
  
  (** val diff : t -> t -> t **)
  
  let diff s s' =
    coq_Build_slist' (Raw.diff (this s) (this s'))
  
  (** val equal : t -> t -> bool **)
  
  let equal s s' =
    Raw.equal (this s) (this s')
  
  (** val subset : t -> t -> bool **)
  
  let subset s s' =
    Raw.subset (this s) (this s')
  
  (** val empty : t **)
  
  let empty =
    coq_Build_slist' Raw.empty
  
  (** val is_empty : t -> bool **)
  
  let is_empty s =
    Raw.is_empty (this s)
  
  (** val elements : t -> elt list **)
  
  let elements s =
    Raw.elements (this s)
  
  (** val min_elt : t -> elt option **)
  
  let min_elt s =
    Raw.min_elt (this s)
  
  (** val max_elt : t -> elt option **)
  
  let max_elt s =
    Raw.max_elt (this s)
  
  (** val choose : t -> elt option **)
  
  let choose s =
    Raw.choose (this s)
  
  (** val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1 **)
  
  let fold f s x =
    Raw.fold f (this s) x
  
  (** val cardinal : t -> nat **)
  
  let cardinal s =
    Raw.cardinal (this s)
  
  (** val filter : (elt -> bool) -> t -> t **)
  
  let filter f s =
    coq_Build_slist' (Raw.filter f (this s))
  
  (** val for_all : (elt -> bool) -> t -> bool **)
  
  let for_all f s =
    Raw.for_all f (this s)
  
  (** val exists_ : (elt -> bool) -> t -> bool **)
  
  let exists_ f s =
    Raw.exists_ f (this s)
  
  (** val partition : (elt -> bool) -> t -> (t, t) prod **)
  
  let partition f s =
    let p = Raw.partition f (this s) in
    Pair ((coq_Build_slist' (fst p)), (coq_Build_slist' (snd p)))
  
  (** val compare : t -> t -> t compare **)
  
  let compare s s' =
    match Raw.compare (this s) (this s') with
      | LT -> LT
      | EQ -> EQ
      | GT -> GT
 end

module Make = 
 functor (X:UsualOrderedType) ->
 struct 
  module E = X
  
  module S = MakeRaw(X)
  
  type fset = S.t
  
  type elt = S.elt
 end

module type VARIABLES = 
 sig 
  type var 
  
  val var_default : var
  
  module Var_as_OT : 
   sig 
    type t = var
    
    val compare : t -> t -> t compare
   end
  
  module VarSet : 
   sig 
    module E : 
     sig 
      type t = var
      
      val compare : t -> t -> t compare
     end
    
    module S : 
     sig 
      module E : 
       sig 
        type t = E.t
        
        val compare : t -> t -> t compare
       end
      
      type elt = E.t
      
      type t 
      
      val empty : t
      
      val is_empty : t -> bool
      
      val mem : elt -> t -> bool
      
      val add : elt -> t -> t
      
      val singleton : elt -> t
      
      val remove : elt -> t -> t
      
      val union : t -> t -> t
      
      val inter : t -> t -> t
      
      val diff : t -> t -> t
      
      val compare : t -> t -> t compare
      
      val equal : t -> t -> bool
      
      val subset : t -> t -> bool
      
      val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1
      
      val for_all : (elt -> bool) -> t -> bool
      
      val exists_ : (elt -> bool) -> t -> bool
      
      val filter : (elt -> bool) -> t -> t
      
      val partition : (elt -> bool) -> t -> (t, t) prod
      
      val cardinal : t -> nat
      
      val elements : t -> elt list
      
      val min_elt : t -> elt option
      
      val max_elt : t -> elt option
      
      val choose : t -> elt option
     end
    
    type fset = S.t
    
    type elt = S.elt
   end
  
  type vars = VarSet.S.t
  
  val var_generate : vars -> var
  
  val var_fresh : vars -> var
  
  val var_of_nat : nat -> var
  
  val nat_of_var : var -> nat
 end

module Variables = 
 struct 
  type var = nat
  
  (** val var_default : var **)
  
  let var_default =
    O
  
  (** val var_of_nat : var -> var **)
  
  let var_of_nat x =
    x
  
  (** val nat_of_var : nat -> nat **)
  
  let nat_of_var x =
    x
  
  module Var_as_OT = Nat_as_OT
  
  module VarSet = Make(Var_as_OT)
  
  type vars = VarSet.S.t
  
  (** val finite_nat_list_max : nat list -> nat **)
  
  let rec finite_nat_list_max = function
    | Nil -> O
    | Cons (a, l0) -> max (finite_nat_list_max l0) a
  
  (** val finite_nat_list_max' : nat list -> nat **)
  
  let finite_nat_list_max' l =
    S (finite_nat_list_max l)
  
  (** val var_generate : vars -> var **)
  
  let var_generate l =
    proj1_sig (finite_nat_list_max' (VarSet.S.elements l))
  
  (** val var_fresh : vars -> var **)
  
  let var_fresh l =
    var_generate l
 end

module Var_as_OT_Facts = OrderedTypeFacts(Variables.Var_as_OT)

(** val eq_var_dec : Variables.var -> Variables.var -> sumbool **)

let eq_var_dec x y =
  Var_as_OT_Facts.eq_dec x y

(** val var_freshes : Variables.vars -> nat -> Variables.var list **)

let rec var_freshes l = function
  | O -> Nil
  | S n0 ->
      let s = Variables.var_fresh l in
      Cons (s,
      (Obj.magic
        (var_freshes
          (Variables.VarSet.S.union l (Variables.VarSet.S.singleton s)) n0)))

module Env = 
 struct 
  type 'a env = (Variables.var, 'a) prod list
  
  (** val empty : 'a1 env **)
  
  let empty =
    Nil
  
  (** val single : Variables.var -> 'a1 -> (Variables.var, 'a1) prod list **)
  
  let single x a =
    Cons ((Pair (x, a)), Nil)
  
  (** val concat : 'a1 env -> 'a1 env -> (Variables.var, 'a1) prod list **)
  
  let concat e f =
    app f e
  
  (** val dom : 'a1 env -> Variables.vars **)
  
  let rec dom = function
    | Nil -> Variables.VarSet.S.empty
    | Cons (p, e') ->
        let Pair (x, a) = p in
        Variables.VarSet.S.union (Variables.VarSet.S.singleton x) (dom e')
  
  (** val map : ('a1 -> 'a1) -> 'a1 env -> 'a1 env **)
  
  let rec map f = function
    | Nil -> Nil
    | Cons (p, e') ->
        let Pair (x, v) = p in Cons ((Pair (x, (f v))), (map f e'))
  
  (** val get : Variables.var -> 'a1 env -> 'a1 option **)
  
  let rec get x = function
    | Nil -> None
    | Cons (p, e') ->
        let Pair (y, a) = p in
        (match eq_var_dec x y with
           | Left -> Some a
           | Right -> get x e')
  
  (** val iter_push : Variables.var list -> 'a1 list -> (Variables.var, 'a1)
                      prod list **)
  
  let iter_push xs vs =
    rev (combine xs vs)
  
  (** val fv_in : ('a1 -> Variables.vars) -> 'a1 env -> Variables.vars **)
  
  let rec fv_in fv = function
    | Nil -> Variables.VarSet.S.empty
    | Cons (p, e') ->
        let Pair (x, a) = p in Variables.VarSet.S.union (fv a) (fv_in fv e')
 end

module type CstrIntf = 
 sig 
  type cstr 
 end

module type CstIntf = 
 sig 
  type const 
  
  val arity : const -> nat
 end

module MkDefs = 
 functor (Cstr:CstrIntf) ->
 functor (Const:CstIntf) ->
 struct 
  type typ =
    | Coq_typ_bvar of nat
    | Coq_typ_fvar of Variables.var
    | Coq_typ_arrow of typ * typ
  
  (** val typ_rect : (nat -> 'a1) -> (Variables.var -> 'a1) -> (typ -> 'a1 ->
                     typ -> 'a1 -> 'a1) -> typ -> 'a1 **)
  
  let rec typ_rect f f0 f1 = function
    | Coq_typ_bvar n -> f n
    | Coq_typ_fvar v -> f0 v
    | Coq_typ_arrow (t1, t2) ->
        f1 t1 (typ_rect f f0 f1 t1) t2 (typ_rect f f0 f1 t2)
  
  (** val typ_rec : (nat -> 'a1) -> (Variables.var -> 'a1) -> (typ -> 'a1 ->
                    typ -> 'a1 -> 'a1) -> typ -> 'a1 **)
  
  let rec typ_rec f f0 f1 = function
    | Coq_typ_bvar n -> f n
    | Coq_typ_fvar v -> f0 v
    | Coq_typ_arrow (t1, t2) ->
        f1 t1 (typ_rec f f0 f1 t1) t2 (typ_rec f f0 f1 t2)
  
  (** val typ_def : typ **)
  
  let typ_def =
    Coq_typ_bvar O
  
  type ckind = { kind_cstr : Cstr.cstr;
                 kind_rel : (Variables.var, typ) prod list }
  
  (** val ckind_rect : (Cstr.cstr -> __ -> (Variables.var, typ) prod list ->
                       __ -> 'a1) -> ckind -> 'a1 **)
  
  let ckind_rect f c =
    let { kind_cstr = x; kind_rel = x0 } = c in f x __ x0 __
  
  (** val ckind_rec : (Cstr.cstr -> __ -> (Variables.var, typ) prod list ->
                      __ -> 'a1) -> ckind -> 'a1 **)
  
  let ckind_rec f c =
    let { kind_cstr = x; kind_rel = x0 } = c in f x __ x0 __
  
  (** val kind_cstr : ckind -> Cstr.cstr **)
  
  let kind_cstr c =
    c.kind_cstr
  
  (** val kind_rel : ckind -> (Variables.var, typ) prod list **)
  
  let kind_rel c =
    c.kind_rel
  
  type kind = ckind option
  
  type sch = { sch_type : typ; sch_kinds : kind list }
  
  (** val sch_rect : (typ -> kind list -> 'a1) -> sch -> 'a1 **)
  
  let sch_rect f s =
    let { sch_type = x; sch_kinds = x0 } = s in f x x0
  
  (** val sch_rec : (typ -> kind list -> 'a1) -> sch -> 'a1 **)
  
  let sch_rec f s =
    let { sch_type = x; sch_kinds = x0 } = s in f x x0
  
  (** val sch_type : sch -> typ **)
  
  let sch_type s =
    s.sch_type
  
  (** val sch_kinds : sch -> kind list **)
  
  let sch_kinds s =
    s.sch_kinds
  
  (** val typ_open : typ -> typ list -> typ **)
  
  let rec typ_open t0 vs =
    match t0 with
      | Coq_typ_bvar i -> nth i vs typ_def
      | Coq_typ_fvar x -> Coq_typ_fvar x
      | Coq_typ_arrow (t1, t2) -> Coq_typ_arrow ((typ_open t1 vs),
          (typ_open t2 vs))
  
  (** val typ_fvars : Variables.var list -> typ list **)
  
  let rec typ_fvars = function
    | Nil -> Nil
    | Cons (a, t0) -> Cons ((Coq_typ_fvar a), (typ_fvars t0))
  
  (** val typ_open_vars : typ -> Variables.var list -> typ **)
  
  let typ_open_vars t0 xs =
    typ_open t0 (typ_fvars xs)
  
  (** val sch_open : sch -> typ list -> typ **)
  
  let sch_open m vs =
    typ_open (sch_type m) vs
  
  (** val sch_open_vars : sch -> Variables.var list -> typ **)
  
  let sch_open_vars m xs =
    typ_open_vars (sch_type m) xs
  
  (** val kind_types : kind -> typ list **)
  
  let kind_types = function
    | Some k0 ->
        let rec map0 = function
          | Nil -> Nil
          | Cons (a, t0) -> Cons ((snd a), (map0 t0))
        in map0 (kind_rel k0)
    | None -> Nil
  
  (** val ckind_map_spec : (typ -> typ) -> ckind -> ckind **)
  
  let ckind_map_spec f k =
    let { kind_cstr = kc; kind_rel = kr } = k in
    { kind_cstr = kc; kind_rel =
    (let rec map0 = function
       | Nil -> Nil
       | Cons (a, t0) -> Cons ((Pair ((fst a), (f (snd a)))), (map0 t0))
     in map0 kr) }
  
  (** val ckind_map : (typ -> typ) -> ckind -> ckind **)
  
  let ckind_map f k =
    proj1_sig
      (let { kind_cstr = kc; kind_rel = kr } = k in
      { kind_cstr = kc; kind_rel =
      (let rec map0 = function
         | Nil -> Nil
         | Cons (a, t0) -> Cons ((Pair ((fst a), (f (snd a)))), (map0 t0))
       in map0 kr) })
  
  (** val kind_map : (typ -> typ) -> kind -> kind **)
  
  let kind_map f = function
    | Some k0 -> Some
        (proj1_sig
          (let { kind_cstr = kc; kind_rel = kr } = k0 in
          { kind_cstr = kc; kind_rel =
          (let rec map0 = function
             | Nil -> Nil
             | Cons (a, t0) -> Cons ((Pair ((fst a), 
                 (f (snd a)))), (map0 t0))
           in map0 kr) }))
    | None -> None
  
  (** val kind_open : kind -> typ list -> kind **)
  
  let kind_open k vs =
    kind_map (fun t0 -> typ_open t0 vs) k
  
  type trm =
    | Coq_trm_bvar of nat
    | Coq_trm_fvar of Variables.var
    | Coq_trm_abs of trm
    | Coq_trm_let of trm * trm
    | Coq_trm_app of trm * trm
    | Coq_trm_cst of Const.const
  
  (** val trm_rect : (nat -> 'a1) -> (Variables.var -> 'a1) -> (trm -> 'a1 ->
                     'a1) -> (trm -> 'a1 -> trm -> 'a1 -> 'a1) -> (trm -> 'a1
                     -> trm -> 'a1 -> 'a1) -> (Const.const -> 'a1) -> trm ->
                     'a1 **)
  
  let rec trm_rect f f0 f1 f2 f3 f4 = function
    | Coq_trm_bvar n -> f n
    | Coq_trm_fvar v -> f0 v
    | Coq_trm_abs t1 -> f1 t1 (trm_rect f f0 f1 f2 f3 f4 t1)
    | Coq_trm_let (t1, t2) ->
        f2 t1 (trm_rect f f0 f1 f2 f3 f4 t1) t2
          (trm_rect f f0 f1 f2 f3 f4 t2)
    | Coq_trm_app (t1, t2) ->
        f3 t1 (trm_rect f f0 f1 f2 f3 f4 t1) t2
          (trm_rect f f0 f1 f2 f3 f4 t2)
    | Coq_trm_cst c -> f4 c
  
  (** val trm_rec : (nat -> 'a1) -> (Variables.var -> 'a1) -> (trm -> 'a1 ->
                    'a1) -> (trm -> 'a1 -> trm -> 'a1 -> 'a1) -> (trm -> 'a1
                    -> trm -> 'a1 -> 'a1) -> (Const.const -> 'a1) -> trm ->
                    'a1 **)
  
  let rec trm_rec f f0 f1 f2 f3 f4 = function
    | Coq_trm_bvar n -> f n
    | Coq_trm_fvar v -> f0 v
    | Coq_trm_abs t1 -> f1 t1 (trm_rec f f0 f1 f2 f3 f4 t1)
    | Coq_trm_let (t1, t2) ->
        f2 t1 (trm_rec f f0 f1 f2 f3 f4 t1) t2 (trm_rec f f0 f1 f2 f3 f4 t2)
    | Coq_trm_app (t1, t2) ->
        f3 t1 (trm_rec f f0 f1 f2 f3 f4 t1) t2 (trm_rec f f0 f1 f2 f3 f4 t2)
    | Coq_trm_cst c -> f4 c
  
  (** val trm_open_rec : nat -> trm -> trm -> trm **)
  
  let rec trm_open_rec k u = function
    | Coq_trm_bvar i ->
        (match eq_nat_dec k i with
           | Left -> u
           | Right -> Coq_trm_bvar i)
    | Coq_trm_fvar x -> Coq_trm_fvar x
    | Coq_trm_abs t1 -> Coq_trm_abs (trm_open_rec (S k) u t1)
    | Coq_trm_let (t1, t2) -> Coq_trm_let ((trm_open_rec k u t1),
        (trm_open_rec (S k) u t2))
    | Coq_trm_app (t1, t2) -> Coq_trm_app ((trm_open_rec k u t1),
        (trm_open_rec k u t2))
    | Coq_trm_cst c -> Coq_trm_cst c
  
  (** val trm_open : trm -> trm -> trm **)
  
  let trm_open t0 u =
    trm_open_rec O u t0
  
  (** val trm_def : trm **)
  
  let trm_def =
    Coq_trm_bvar O
  
  (** val trm_inst_rec : nat -> trm list -> trm -> trm **)
  
  let rec trm_inst_rec k tl = function
    | Coq_trm_bvar i ->
        (match le_lt_dec k i with
           | Left -> nth (minus i k) tl trm_def
           | Right -> Coq_trm_bvar i)
    | Coq_trm_fvar x -> Coq_trm_fvar x
    | Coq_trm_abs t1 -> Coq_trm_abs (trm_inst_rec (S k) tl t1)
    | Coq_trm_let (t1, t2) -> Coq_trm_let ((trm_inst_rec k tl t1),
        (trm_inst_rec (S k) tl t2))
    | Coq_trm_app (t1, t2) -> Coq_trm_app ((trm_inst_rec k tl t1),
        (trm_inst_rec k tl t2))
    | Coq_trm_cst c -> Coq_trm_cst c
  
  (** val trm_inst : trm -> trm list -> trm **)
  
  let trm_inst t0 tl =
    trm_inst_rec O tl t0
  
  type kenv = kind Env.env
  
  (** val kinds_open : kind list -> typ list -> kind list **)
  
  let rec kinds_open ks us =
    match ks with
      | Nil -> Nil
      | Cons (a, t0) -> Cons ((kind_open a us), (kinds_open t0 us))
  
  (** val kinds_open_vars : kind list -> Variables.var list ->
                            (Variables.var, kind) prod list **)
  
  let kinds_open_vars ks xs =
    combine xs
      (let rec map0 = function
         | Nil -> Nil
         | Cons (a, t0) -> Cons ((kind_open a (typ_fvars xs)), (map0 t0))
       in map0 ks)
  
  type env = sch Env.env
  
  (** val typ_fv : typ -> Variables.vars **)
  
  let rec typ_fv = function
    | Coq_typ_bvar i -> Variables.VarSet.S.empty
    | Coq_typ_fvar x -> Variables.VarSet.S.singleton x
    | Coq_typ_arrow (t1, t2) ->
        Variables.VarSet.S.union (typ_fv t1) (typ_fv t2)
  
  (** val typ_fv_list : typ list -> Variables.VarSet.S.t **)
  
  let rec typ_fv_list = function
    | Nil -> Variables.VarSet.S.empty
    | Cons (b, t0) -> Variables.VarSet.S.union (typ_fv b) (typ_fv_list t0)
  
  (** val kind_fv : kind -> Variables.VarSet.S.t **)
  
  let kind_fv k =
    typ_fv_list (kind_types k)
  
  (** val kind_fv_list : kind list -> Variables.VarSet.S.t **)
  
  let rec kind_fv_list = function
    | Nil -> Variables.VarSet.S.empty
    | Cons (b, t0) -> Variables.VarSet.S.union (kind_fv b) (kind_fv_list t0)
  
  (** val sch_fv : sch -> Variables.VarSet.S.t **)
  
  let sch_fv m =
    Variables.VarSet.S.union (typ_fv (sch_type m))
      (kind_fv_list (sch_kinds m))
  
  (** val env_fv : sch Env.env -> Variables.vars **)
  
  let rec env_fv = function
    | Nil -> Variables.VarSet.S.empty
    | Cons (p, e') ->
        let Pair (x, a) = p in
        Variables.VarSet.S.union (sch_fv a) (env_fv e')
  
  module type DeltaIntf = 
   sig 
    val coq_type : Const.const -> sch
   end
  
  module MkJudge = 
   functor (Delta:DeltaIntf) ->
   struct 
    type gc_kind =
      | GcAny
      | GcLet
    
    (** val gc_kind_rect : 'a1 -> 'a1 -> gc_kind -> 'a1 **)
    
    let gc_kind_rect f f0 = function
      | GcAny -> f
      | GcLet -> f0
    
    (** val gc_kind_rec : 'a1 -> 'a1 -> gc_kind -> 'a1 **)
    
    let gc_kind_rec f f0 = function
      | GcAny -> f
      | GcLet -> f0
    
    type gc_info = (bool, gc_kind) prod
    
    (** val gc_raise : gc_info -> gc_info **)
    
    let rec gc_raise gc =
      match snd gc with
        | GcAny -> gc
        | GcLet -> Pair (True, GcLet)
    
    (** val gc_lower : gc_info -> gc_info **)
    
    let rec gc_lower gc =
      match snd gc with
        | GcAny -> gc
        | GcLet -> Pair (False, GcLet)
   end
 end

(** val mkset : Variables.var list -> Variables.vars **)

let rec mkset = function
  | Nil -> Variables.VarSet.S.empty
  | Cons (h, t0) ->
      Variables.VarSet.S.union (Variables.VarSet.S.singleton h) (mkset t0)

module MkInfra = 
 functor (Cstr:CstrIntf) ->
 functor (Const:CstIntf) ->
 struct 
  module Defs = MkDefs(Cstr)(Const)
  
  (** val trm_fv : Defs.trm -> Variables.vars **)
  
  let rec trm_fv = function
    | Defs.Coq_trm_bvar i -> Variables.VarSet.S.empty
    | Defs.Coq_trm_fvar x -> Variables.VarSet.S.singleton x
    | Defs.Coq_trm_abs t1 -> trm_fv t1
    | Defs.Coq_trm_let (t1, t2) ->
        Variables.VarSet.S.union (trm_fv t1) (trm_fv t2)
    | Defs.Coq_trm_app (t1, t2) ->
        Variables.VarSet.S.union (trm_fv t1) (trm_fv t2)
    | Defs.Coq_trm_cst c -> Variables.VarSet.S.empty
  
  type subs = Defs.typ Env.env
  
  (** val typ_subst : subs -> Defs.typ -> Defs.typ **)
  
  let rec typ_subst s t0 = match t0 with
    | Defs.Coq_typ_bvar i -> Defs.Coq_typ_bvar i
    | Defs.Coq_typ_fvar x ->
        (match Env.get x s with
           | Some t' -> t'
           | None -> t0)
    | Defs.Coq_typ_arrow (t1, t2) -> Defs.Coq_typ_arrow (
        (typ_subst s t1), (typ_subst s t2))
  
  (** val kind_subst : subs -> Defs.kind -> Defs.kind **)
  
  let kind_subst s k =
    Defs.kind_map (typ_subst s) k
  
  (** val sch_subst : subs -> Defs.sch -> Defs.sch **)
  
  let sch_subst s m =
    { Defs.sch_type = (typ_subst s (Defs.sch_type m)); Defs.sch_kinds =
      (let rec map0 = function
         | Nil -> Nil
         | Cons (a, t0) -> Cons ((kind_subst s a), (map0 t0))
       in map0 (Defs.sch_kinds m)) }
  
  (** val trm_subst : Variables.var -> Defs.trm -> Defs.trm -> Defs.trm **)
  
  let rec trm_subst z u = function
    | Defs.Coq_trm_bvar i -> Defs.Coq_trm_bvar i
    | Defs.Coq_trm_fvar x ->
        (match eq_var_dec x z with
           | Left -> u
           | Right -> Defs.Coq_trm_fvar x)
    | Defs.Coq_trm_abs t1 -> Defs.Coq_trm_abs (trm_subst z u t1)
    | Defs.Coq_trm_let (t1, t2) -> Defs.Coq_trm_let (
        (trm_subst z u t1), (trm_subst z u t2))
    | Defs.Coq_trm_app (t1, t2) -> Defs.Coq_trm_app (
        (trm_subst z u t1), (trm_subst z u t2))
    | Defs.Coq_trm_cst c -> Defs.Coq_trm_cst c
  
  (** val const_app : Const.const -> Defs.trm list -> Defs.trm **)
  
  let const_app c vl =
    fold_left (fun x x0 -> Defs.Coq_trm_app (x, x0)) vl (Defs.Coq_trm_cst c)
  
  (** val map_get : Variables.var list -> 'a1 Env.env -> 'a1 list **)
  
  let rec map_get l e =
    match l with
      | Nil -> Nil
      | Cons (h, t0) ->
          (match Env.get h e with
             | Some x -> Cons (x, (map_get t0 e))
             | None -> map_get t0 e)
  
  module MkJudgInfra = 
   functor (Delta:Defs.DeltaIntf) ->
   struct 
    module Judge = Defs.MkJudge(Delta)
   end
 end

module MkSound = 
 functor (Cstr:CstrIntf) ->
 functor (Const:CstIntf) ->
 struct 
  module Infra = MkInfra(Cstr)(Const)
  
  module Mk2 = 
   functor (Delta:Infra.Defs.DeltaIntf) ->
   struct 
    module JudgInfra = Infra.MkJudgInfra(Delta)
    
    module type SndHypIntf = 
     sig 
      
     end
    
    module Mk3 = 
     functor (SH:SndHypIntf) ->
     struct 
      
     end
   end
 end

module MkUnify = 
 functor (Cstr:CstrIntf) ->
 functor (Const:CstIntf) ->
 struct 
  module Sound = MkSound(Cstr)(Const)
  
  module type Cstr2I = 
   sig 
    val unique : Cstr.cstr -> Variables.var list
    
    val lub : Cstr.cstr -> Cstr.cstr -> Cstr.cstr
    
    val valid : Cstr.cstr -> sumbool
   end
  
  module Mk2 = 
   functor (Cstr2:Cstr2I) ->
   struct 
    (** val compose : Sound.Infra.Defs.typ Env.env -> Sound.Infra.Defs.typ
                      Env.env -> Sound.Infra.subs **)
    
    let compose s1 s2 =
      Env.concat s1 (Env.map (Sound.Infra.typ_subst s1) s2)
    
    (** val unify_kind_rel : (Variables.var, Sound.Infra.Defs.typ) prod list
                             -> (Variables.var, Sound.Infra.Defs.typ) prod
                             list -> Variables.var list ->
                             (Sound.Infra.Defs.typ, Sound.Infra.Defs.typ)
                             prod list -> ((Variables.var,
                             Sound.Infra.Defs.typ) prod list,
                             (Sound.Infra.Defs.typ, Sound.Infra.Defs.typ)
                             prod list) prod **)
    
    let rec unify_kind_rel kr kr' un pairs =
      match kr with
        | Nil -> Pair (kr', pairs)
        | Cons (p, krem) ->
            let Pair (l, t0) = p in
            (match let rec f = function
                     | Nil -> Right
                     | Cons (a, l1) ->
                         (match eq_var_dec a l with
                            | Left -> Left
                            | Right -> f l1)
                   in f un with
               | Left ->
                   (match Env.get l kr' with
                      | Some t' ->
                          unify_kind_rel krem kr' un (Cons ((Pair (t0, t')),
                            pairs))
                      | None ->
                          unify_kind_rel krem (Cons ((Pair (l, t0)), kr')) un
                            pairs)
               | Right ->
                   unify_kind_rel krem (Cons ((Pair (l, t0)), kr')) un pairs)
    
    (** val remove_env : 'a1 Env.env -> Variables.var -> 'a1 Env.env **)
    
    let rec remove_env e x =
      match e with
        | Nil -> Nil
        | Cons (p, e') ->
            let Pair (y, a) = p in
            (match eq_var_dec x y with
               | Left -> e'
               | Right -> Cons ((Pair (y, a)), (remove_env e' x)))
    
    (** val unify_kinds : Sound.Infra.Defs.kind -> Sound.Infra.Defs.kind ->
                          (Sound.Infra.Defs.kind, (Sound.Infra.Defs.typ,
                          Sound.Infra.Defs.typ) prod list) prod option **)
    
    let unify_kinds k1 k2 =
      match k1 with
        | Some c ->
            let { Sound.Infra.Defs.kind_cstr = kc1;
              Sound.Infra.Defs.kind_rel = kr1 } = c
            in
            (match k2 with
               | Some c0 ->
                   let { Sound.Infra.Defs.kind_cstr = kc2;
                     Sound.Infra.Defs.kind_rel = kr2 } = c0
                   in
                   let kc = Cstr2.lub kc1 kc2 in
                   (match Cstr2.valid kc with
                      | Left ->
                          let krp =
                            unify_kind_rel (app kr1 kr2) Nil
                              (Cstr2.unique kc) Nil
                          in
                          Some (Pair ((Some { Sound.Infra.Defs.kind_cstr =
                          kc; Sound.Infra.Defs.kind_rel = 
                          (fst krp) }), (snd krp)))
                      | Right -> None)
               | None -> Some (Pair (k1, Nil)))
        | None -> Some (Pair (k2, Nil))
    
    (** val get_kind : Variables.var -> Sound.Infra.Defs.kind Env.env ->
                       Sound.Infra.Defs.kind **)
    
    let get_kind x e =
      match Env.get x e with
        | Some k -> k
        | None -> None
    
    (** val unify_vars : Sound.Infra.Defs.kenv -> Variables.var ->
                         Variables.var -> ((Variables.var,
                         Sound.Infra.Defs.kind) prod list,
                         (Sound.Infra.Defs.typ, Sound.Infra.Defs.typ) prod
                         list) prod option **)
    
    let unify_vars k x y =
      match unify_kinds (get_kind x k) (get_kind y k) with
        | Some p ->
            let Pair (k0, pairs) = p in
            Some (Pair
            ((Env.concat (remove_env (remove_env k x) y) (Env.single y k0)),
            pairs))
        | None -> None
    
    (** val unify_nv : (Sound.Infra.Defs.kenv -> Sound.Infra.subs ->
                       (Sound.Infra.Defs.kenv, Sound.Infra.subs) prod option)
                       -> Sound.Infra.Defs.kind Env.env ->
                       Sound.Infra.Defs.typ Env.env -> Variables.VarSet.S.elt
                       -> Sound.Infra.Defs.typ -> (Sound.Infra.Defs.kenv,
                       Sound.Infra.subs) prod option **)
    
    let unify_nv unify1 k s x t0 =
      match Variables.VarSet.S.mem x (Sound.Infra.Defs.typ_fv t0) with
        | True -> None
        | False ->
            (match get_kind x k with
               | Some c -> None
               | None ->
                   unify1 (remove_env k x) (compose (Env.single x t0) s))
    
    (** val unify0 : ((Sound.Infra.Defs.typ, Sound.Infra.Defs.typ) prod list
                     -> Sound.Infra.Defs.kenv -> Sound.Infra.subs ->
                     (Sound.Infra.Defs.kenv, Sound.Infra.subs) prod option)
                     -> nat -> (Sound.Infra.Defs.typ, Sound.Infra.Defs.typ)
                     prod list -> Sound.Infra.Defs.kenv -> Sound.Infra.subs
                     -> (Sound.Infra.Defs.kenv, Sound.Infra.subs) prod option **)
    
    let rec unify0 unify1 h pairs k s =
      match h with
        | O -> None
        | S h' ->
            (match pairs with
               | Nil -> Some (Pair (k, s))
               | Cons (p, pairs') ->
                   let Pair (t1, t2) = p in
                   (match Sound.Infra.typ_subst s t1 with
                      | Sound.Infra.Defs.Coq_typ_bvar n ->
                          (match Sound.Infra.typ_subst s t2 with
                             | Sound.Infra.Defs.Coq_typ_bvar m ->
                                 (match eq_nat_dec n m with
                                    | Left -> unify0 unify1 h' pairs' k s
                                    | Right -> None)
                             | Sound.Infra.Defs.Coq_typ_fvar x ->
                                 unify_nv (unify1 pairs') k s x
                                   (Sound.Infra.typ_subst s t1)
                             | Sound.Infra.Defs.Coq_typ_arrow (
                                 t0, t3) -> None)
                      | Sound.Infra.Defs.Coq_typ_fvar x ->
                          (match Sound.Infra.typ_subst s t2 with
                             | Sound.Infra.Defs.Coq_typ_bvar n ->
                                 unify_nv (unify1 pairs') k s x
                                   (Sound.Infra.typ_subst s t2)
                             | Sound.Infra.Defs.Coq_typ_fvar x0 ->
                                 (match eq_var_dec x x0 with
                                    | Left -> unify0 unify1 h' pairs' k s
                                    | Right ->
                                        (match unify_vars k x x0 with
                                           | Some p0 ->
                                               let Pair (k', pairs0) = p0 in
                                               unify1 
                                                 (app pairs0 pairs') k'
                                                 (compose
                                                  (Env.single x
                                                  (Sound.Infra.Defs.Coq_typ_fvar
                                                  x0)) s)
                                           | None -> None))
                             | Sound.Infra.Defs.Coq_typ_arrow (
                                 t0, t3) ->
                                 unify_nv (unify1 pairs') k s x
                                   (Sound.Infra.typ_subst s t2))
                      | Sound.Infra.Defs.Coq_typ_arrow (
                          t11, t12) ->
                          (match Sound.Infra.typ_subst s t2 with
                             | Sound.Infra.Defs.Coq_typ_bvar n -> None
                             | Sound.Infra.Defs.Coq_typ_fvar x ->
                                 unify_nv (unify1 pairs') k s x
                                   (Sound.Infra.typ_subst s t1)
                             | Sound.Infra.Defs.Coq_typ_arrow (
                                 t21, t22) ->
                                 unify0 unify1 h' (Cons ((Pair (t11, t21)),
                                   (Cons ((Pair (t12, t22)), pairs')))) k s)))
    
    (** val accum : ('a1 -> 'a2) -> ('a2 -> 'a2 -> 'a2) -> 'a2 -> 'a1 list ->
                    'a2 **)
    
    let rec accum f op unit0 = function
      | Nil -> unit0
      | Cons (a, rem) -> op (f a) (accum f op unit0 rem)
    
    (** val all_types : Sound.Infra.subs -> (Sound.Infra.Defs.typ,
                        Sound.Infra.Defs.typ) prod list ->
                        Sound.Infra.Defs.typ list **)
    
    let rec all_types s = function
      | Nil -> Nil
      | Cons (p, rem) -> Cons ((Sound.Infra.typ_subst s (fst p)), (Cons
          ((Sound.Infra.typ_subst s (snd p)), (all_types s rem))))
    
    (** val typ_size : Sound.Infra.Defs.typ -> nat **)
    
    let rec typ_size = function
      | Sound.Infra.Defs.Coq_typ_bvar n -> S O
      | Sound.Infra.Defs.Coq_typ_fvar v -> S O
      | Sound.Infra.Defs.Coq_typ_arrow (t1, t2) -> S
          (plus (typ_size t1) (typ_size t2))
    
    (** val pairs_size : Sound.Infra.subs -> (Sound.Infra.Defs.typ,
                         Sound.Infra.Defs.typ) prod list -> nat **)
    
    let pairs_size s pairs =
      let rec accum0 = function
        | Nil -> O
        | Cons (a, rem) -> plus (typ_size a) (accum0 rem)
      in accum0 (all_types s pairs)
    
    (** val unify : nat -> (Sound.Infra.Defs.typ, Sound.Infra.Defs.typ) prod
                    list -> Sound.Infra.Defs.kenv -> Sound.Infra.subs ->
                    (Sound.Infra.Defs.kenv, Sound.Infra.subs) prod option **)
    
    let rec unify h pairs k s =
      match h with
        | O -> None
        | S h' ->
            unify0 (unify h') (plus (pairs_size s pairs) (S O)) pairs k s
    
    (** val id : Sound.Infra.Defs.typ Env.env **)
    
    let id =
      Env.empty
    
    (** val all_fv : Sound.Infra.subs -> (Sound.Infra.Defs.typ,
                     Sound.Infra.Defs.typ) prod list -> Variables.vars **)
    
    let all_fv s pairs =
      let rec accum0 = function
        | Nil -> Variables.VarSet.S.empty
        | Cons (a, rem) ->
            Variables.VarSet.S.union (Sound.Infra.Defs.typ_fv a) (accum0 rem)
      in accum0 (all_types s pairs)
    
    (** val really_all_fv : Sound.Infra.subs -> Sound.Infra.Defs.kind Env.env
                            -> (Sound.Infra.Defs.typ, Sound.Infra.Defs.typ)
                            prod list -> Variables.VarSet.S.t **)
    
    let really_all_fv s k pairs =
      Variables.VarSet.S.union
        (let rec fv_in0 = function
           | Nil -> Variables.VarSet.S.empty
           | Cons (p, e') ->
               let Pair (x, a) = p in
               Variables.VarSet.S.union (Sound.Infra.Defs.kind_fv a)
                 (fv_in0 e')
         in fv_in0 (Env.map (Sound.Infra.kind_subst s) k)) 
        (all_fv s pairs)
    
    (** val size_pairs : Sound.Infra.subs -> Sound.Infra.Defs.kind Env.env ->
                         (Sound.Infra.Defs.typ, Sound.Infra.Defs.typ) prod
                         list -> nat **)
    
    let size_pairs s k pairs =
      Variables.VarSet.S.cardinal (really_all_fv s k pairs)
   end
 end

(** val index : ('a1 -> 'a1 -> sumbool) -> nat -> 'a1 -> 'a1 list -> nat
                option **)

let rec index eq_dec0 i x = function
  | Nil -> None
  | Cons (y, l') ->
      (match eq_dec0 x y with
         | Left -> Some i
         | Right -> index eq_dec0 (S i) x l')

module MkRename = 
 functor (Cstr:CstrIntf) ->
 functor (Const:CstIntf) ->
 struct 
  module Unify = MkUnify(Cstr)(Const)
  
  module Mk2 = 
   functor (Delta:Unify.Sound.Infra.Defs.DeltaIntf) ->
   struct 
    module Sound = Unify.Sound.Mk2(Delta)
    
    (** val typ_generalize : Variables.var list -> Unify.Sound.Infra.Defs.typ
                             -> Unify.Sound.Infra.Defs.typ **)
    
    let rec typ_generalize bs t0 = match t0 with
      | Unify.Sound.Infra.Defs.Coq_typ_bvar n ->
          Unify.Sound.Infra.Defs.Coq_typ_bvar (plus (length bs) n)
      | Unify.Sound.Infra.Defs.Coq_typ_fvar x ->
          (match index eq_var_dec O x bs with
             | Some n -> Unify.Sound.Infra.Defs.Coq_typ_bvar n
             | None -> t0)
      | Unify.Sound.Infra.Defs.Coq_typ_arrow (t1, t2) ->
          Unify.Sound.Infra.Defs.Coq_typ_arrow ((typ_generalize bs t1),
          (typ_generalize bs t2))
    
    (** val sch_generalize : Variables.var list -> Unify.Sound.Infra.Defs.typ
                             -> Unify.Sound.Infra.Defs.kind list ->
                             Unify.Sound.Infra.Defs.sch **)
    
    let sch_generalize bs t0 ks =
      { Unify.Sound.Infra.Defs.sch_type = (typ_generalize bs t0);
        Unify.Sound.Infra.Defs.sch_kinds =
        (let rec map0 = function
           | Nil -> Nil
           | Cons (a, t1) -> Cons
               ((Unify.Sound.Infra.Defs.kind_map (typ_generalize bs) a),
               (map0 t1))
         in map0 ks) }
    
    (** val list_fst : ('a1, 'a2) prod list -> 'a1 list **)
    
    let rec list_fst = function
      | Nil -> Nil
      | Cons (a, t0) -> Cons ((fst a), (list_fst t0))
   end
 end

module MkInfer = 
 functor (Cstr:CstrIntf) ->
 functor (Const:CstIntf) ->
 struct 
  module Rename = MkRename(Cstr)(Const)
  
  module Mk2 = 
   functor (Delta:Rename.Unify.Sound.Infra.Defs.DeltaIntf) ->
   functor (Cstr2:Rename.Unify.Cstr2I) ->
   struct 
    module Rename2 = Rename.Mk2(Delta)
    
    module Body = Rename.Unify.Mk2(Cstr2)
    
    (** val unify : Rename.Unify.Sound.Infra.Defs.kind Env.env ->
                    Rename.Unify.Sound.Infra.Defs.typ ->
                    Rename.Unify.Sound.Infra.Defs.typ ->
                    Rename.Unify.Sound.Infra.subs ->
                    (Rename.Unify.Sound.Infra.Defs.kenv,
                    Rename.Unify.Sound.Infra.subs) prod option **)
    
    let unify k t1 t2 s =
      Body.unify
        (plus (S O) (Body.size_pairs s k (Cons ((Pair (t1, t2)), Nil))))
        (Cons ((Pair (t1, t2)), Nil)) k s
    
    (** val fvs : Rename.Unify.Sound.Infra.Defs.typ Env.env ->
                  Rename.Unify.Sound.Infra.Defs.kind Env.env ->
                  Rename.Unify.Sound.Infra.Defs.sch Env.env ->
                  Variables.VarSet.S.t **)
    
    let fvs s k e =
      Variables.VarSet.S.union
        (Variables.VarSet.S.union
          (Variables.VarSet.S.union
            (Variables.VarSet.S.union (Env.dom s)
              (let rec fv_in0 = function
                 | Nil -> Variables.VarSet.S.empty
                 | Cons (p, e') ->
                     let Pair (x, a) = p in
                     Variables.VarSet.S.union
                       (Rename.Unify.Sound.Infra.Defs.typ_fv a) 
                       (fv_in0 e')
               in fv_in0 s)) (Env.dom k))
          (let rec fv_in0 = function
             | Nil -> Variables.VarSet.S.empty
             | Cons (p, e') ->
                 let Pair (x, a) = p in
                 Variables.VarSet.S.union
                   (Rename.Unify.Sound.Infra.Defs.kind_fv a) 
                   (fv_in0 e')
           in fv_in0 k)) (Rename.Unify.Sound.Infra.Defs.env_fv e)
    
    (** val close_fvars : nat -> Rename.Unify.Sound.Infra.Defs.kenv ->
                          Variables.vars -> Variables.vars -> Variables.vars **)
    
    let rec close_fvars n k vK vs =
      match n with
        | O -> vs
        | S n' ->
            (match Variables.VarSet.S.choose (Variables.VarSet.S.inter vK vs) with
               | Some x ->
                   close_fvars n' k (Variables.VarSet.S.remove x vK)
                     (match Env.get x k with
                        | Some k0 ->
                            Variables.VarSet.S.union vs
                              (Rename.Unify.Sound.Infra.Defs.kind_fv k0)
                        | None -> vs)
               | None -> vs)
    
    (** val close_fvk : (Variables.var, Rename.Unify.Sound.Infra.Defs.kind)
                        prod list -> Variables.vars -> Variables.vars **)
    
    let close_fvk k vs =
      close_fvars (length k) k (Env.dom k) vs
    
    (** val split_env : Variables.vars -> 'a1 Env.env -> ('a1 Env.env, 'a1
                        Env.env) prod **)
    
    let rec split_env b = function
      | Nil -> Pair (Nil, Nil)
      | Cons (xk, e') ->
          let Pair (eb, eB) = split_env b e' in
          (match Variables.VarSet.S.mem (fst xk) b with
             | True -> Pair (eb, (Cons (xk, eB)))
             | False -> Pair ((Cons (xk, eb)), eB))
    
    (** val vars_subst : Rename.Unify.Sound.Infra.subs ->
                         Variables.VarSet.S.t -> Variables.VarSet.S.t **)
    
    let vars_subst s l =
      Rename.Unify.Sound.Infra.Defs.typ_fv_list
        (let rec map0 = function
           | Nil -> Nil
           | Cons (a, t0) -> Cons
               ((Rename.Unify.Sound.Infra.typ_subst s
                  (Rename.Unify.Sound.Infra.Defs.Coq_typ_fvar a)), 
               (map0 t0))
         in map0 (Variables.VarSet.S.elements l))
    
    (** val typinf_generalize : (Variables.var,
                                Rename.Unify.Sound.Infra.Defs.kind) prod list
                                -> Rename.Unify.Sound.Infra.Defs.sch Env.env
                                -> Variables.vars ->
                                Rename.Unify.Sound.Infra.Defs.typ ->
                                ((Variables.var,
                                Rename.Unify.Sound.Infra.Defs.kind) prod
                                list, Rename.Unify.Sound.Infra.Defs.sch) prod **)
    
    let typinf_generalize k' e' l t1 =
      let ftve = close_fvk k' (Rename.Unify.Sound.Infra.Defs.env_fv e') in
      let Pair (k'', kA) = split_env ftve k' in
      let b = close_fvk k' (Rename.Unify.Sound.Infra.Defs.typ_fv t1) in
      let Pair (x, kB) = split_env b k'' in
      let Pair (bs, ks) = split kB in
      let bs' =
        Variables.VarSet.S.elements
          (Variables.VarSet.S.diff b
            (Variables.VarSet.S.union ftve (Env.dom kB)))
      in
      let Pair (x0, kC) = split_env l k'' in
      Pair ((Env.concat kA kC),
      (Rename2.sch_generalize (app bs bs') t1
        (app ks
          (let rec map0 = function
             | Nil -> Nil
             | Cons (a, t0) -> Cons (None, (map0 t0))
           in map0 bs'))))
    
    (** val kdom : Rename.Unify.Sound.Infra.Defs.kenv -> Variables.vars **)
    
    let rec kdom = function
      | Nil -> Variables.VarSet.S.empty
      | Cons (p, e') ->
          let Pair (x, k) = p in
          (match k with
             | Some c ->
                 Variables.VarSet.S.union (Variables.VarSet.S.singleton x)
                   (kdom e')
             | None -> kdom e')
    
    (** val typinf : Rename.Unify.Sound.Infra.Defs.kenv ->
                     Rename.Unify.Sound.Infra.Defs.env ->
                     Rename.Unify.Sound.Infra.Defs.trm ->
                     Rename.Unify.Sound.Infra.Defs.typ -> Variables.vars ->
                     Rename.Unify.Sound.Infra.subs -> nat ->
                     ((Rename.Unify.Sound.Infra.Defs.kenv,
                     Rename.Unify.Sound.Infra.subs) prod option,
                     Variables.vars) prod **)
    
    let rec typinf k e t0 t1 l s = function
      | O -> Pair (None, l)
      | S h' ->
          (match t0 with
             | Rename.Unify.Sound.Infra.Defs.Coq_trm_bvar n -> Pair (None, l)
             | Rename.Unify.Sound.Infra.Defs.Coq_trm_fvar x ->
                 (match Env.get x e with
                    | Some m ->
                        let vs =
                          proj1_sig
                            (var_freshes l
                              (length
                                (Rename.Unify.Sound.Infra.Defs.sch_kinds m)))
                        in
                        Pair
                        ((unify
                           (Env.concat k
                             (Rename.Unify.Sound.Infra.Defs.kinds_open_vars
                               (Rename.Unify.Sound.Infra.Defs.sch_kinds m)
                               vs))
                           (Rename.Unify.Sound.Infra.Defs.sch_open_vars m vs)
                           t1 s), (Variables.VarSet.S.union l (mkset vs)))
                    | None -> Pair (None, l))
             | Rename.Unify.Sound.Infra.Defs.Coq_trm_abs t2 ->
                 let x =
                   proj1_sig
                     (Variables.var_fresh
                       (Variables.VarSet.S.union (Env.dom e)
                         (Rename.Unify.Sound.Infra.trm_fv t2)))
                 in
                 let v1 = proj1_sig (Variables.var_fresh l) in
                 let v2 =
                   proj1_sig
                     (Variables.var_fresh
                       (Variables.VarSet.S.union l
                         (Variables.VarSet.S.singleton v1)))
                 in
                 (match unify k (Rename.Unify.Sound.Infra.Defs.Coq_typ_arrow
                          ((Rename.Unify.Sound.Infra.Defs.Coq_typ_fvar v1),
                          (Rename.Unify.Sound.Infra.Defs.Coq_typ_fvar v2)))
                          t1 s with
                    | Some p ->
                        let Pair (k', s') = p in
                        typinf k'
                          (Env.concat e
                            (Env.single x
                              { Rename.Unify.Sound.Infra.Defs.sch_type =
                              (Rename.Unify.Sound.Infra.Defs.Coq_typ_fvar
                              v1); Rename.Unify.Sound.Infra.Defs.sch_kinds =
                              Nil }))
                          (Rename.Unify.Sound.Infra.Defs.trm_open t2
                            (Rename.Unify.Sound.Infra.Defs.Coq_trm_fvar x))
                          (Rename.Unify.Sound.Infra.Defs.Coq_typ_fvar v2)
                          (Variables.VarSet.S.union
                            (Variables.VarSet.S.union l
                              (Variables.VarSet.S.singleton v1))
                            (Variables.VarSet.S.singleton v2)) s' h'
                    | None -> Pair (None, l))
             | Rename.Unify.Sound.Infra.Defs.Coq_trm_let (
                 t2, t3) ->
                 let v = proj1_sig (Variables.var_fresh l) in
                 let Pair (o, l') =
                   typinf k e t2 (Rename.Unify.Sound.Infra.Defs.Coq_typ_fvar
                     v)
                     (Variables.VarSet.S.union l
                       (Variables.VarSet.S.singleton v)) s h'
                 in
                 (match o with
                    | Some p ->
                        let Pair (k0, s') = p in
                        let Pair (kA, m) =
                          typinf_generalize
                            (Env.map (Rename.Unify.Sound.Infra.kind_subst s')
                              k0)
                            (Env.map (Rename.Unify.Sound.Infra.sch_subst s')
                              e)
                            (Rename.Unify.Sound.Infra.Defs.typ_fv_list
                              (let rec map0 = function
                                 | Nil -> Nil
                                 | Cons (a, t4) -> Cons
                                     ((Rename.Unify.Sound.Infra.typ_subst s'
                                        (Rename.Unify.Sound.Infra.Defs.Coq_typ_fvar
                                        a)), (map0 t4))
                               in map0 (Variables.VarSet.S.elements (kdom k))))
                            (Rename.Unify.Sound.Infra.typ_subst s'
                              (Rename.Unify.Sound.Infra.Defs.Coq_typ_fvar v))
                        in
                        let x =
                          proj1_sig
                            (Variables.var_fresh
                              (Variables.VarSet.S.union
                                (Variables.VarSet.S.union 
                                  (Env.dom e)
                                  (Rename.Unify.Sound.Infra.trm_fv t2))
                                (Rename.Unify.Sound.Infra.trm_fv t3)))
                        in
                        typinf kA (Env.concat e (Env.single x m))
                          (Rename.Unify.Sound.Infra.Defs.trm_open t3
                            (Rename.Unify.Sound.Infra.Defs.Coq_trm_fvar x))
                          t1 l' s' h'
                    | None ->
                        typinf k e t2
                          (Rename.Unify.Sound.Infra.Defs.Coq_typ_fvar v)
                          (Variables.VarSet.S.union l
                            (Variables.VarSet.S.singleton v)) s h')
             | Rename.Unify.Sound.Infra.Defs.Coq_trm_app (
                 t2, t3) ->
                 let v = proj1_sig (Variables.var_fresh l) in
                 let Pair (o, l') =
                   typinf k e t2 (Rename.Unify.Sound.Infra.Defs.Coq_typ_arrow
                     ((Rename.Unify.Sound.Infra.Defs.Coq_typ_fvar v), t1))
                     (Variables.VarSet.S.union l
                       (Variables.VarSet.S.singleton v)) s h'
                 in
                 (match o with
                    | Some p ->
                        let Pair (k', s') = p in
                        typinf k' e t3
                          (Rename.Unify.Sound.Infra.Defs.Coq_typ_fvar v) l'
                          s' h'
                    | None ->
                        typinf k e t2
                          (Rename.Unify.Sound.Infra.Defs.Coq_typ_arrow
                          ((Rename.Unify.Sound.Infra.Defs.Coq_typ_fvar v),
                          t1))
                          (Variables.VarSet.S.union l
                            (Variables.VarSet.S.singleton v)) s h')
             | Rename.Unify.Sound.Infra.Defs.Coq_trm_cst c ->
                 let m = Delta.coq_type c in
                 let vs =
                   proj1_sig
                     (var_freshes l
                       (length (Rename.Unify.Sound.Infra.Defs.sch_kinds m)))
                 in
                 Pair
                 ((unify
                    (Env.concat k
                      (Rename.Unify.Sound.Infra.Defs.kinds_open_vars
                        (Rename.Unify.Sound.Infra.Defs.sch_kinds m) vs))
                    (Rename.Unify.Sound.Infra.Defs.sch_open_vars m vs) t1 s),
                 (Variables.VarSet.S.union l (mkset vs))))
    
    (** val trm_depth : Rename.Unify.Sound.Infra.Defs.trm -> nat **)
    
    let rec trm_depth = function
      | Rename.Unify.Sound.Infra.Defs.Coq_trm_bvar n -> O
      | Rename.Unify.Sound.Infra.Defs.Coq_trm_fvar v -> O
      | Rename.Unify.Sound.Infra.Defs.Coq_trm_abs t1 -> S (trm_depth t1)
      | Rename.Unify.Sound.Infra.Defs.Coq_trm_let (
          t1, t2) -> S (max (trm_depth t1) (trm_depth t2))
      | Rename.Unify.Sound.Infra.Defs.Coq_trm_app (
          t1, t2) -> S (max (trm_depth t1) (trm_depth t2))
      | Rename.Unify.Sound.Infra.Defs.Coq_trm_cst c -> O
    
    (** val typinf' : Rename.Unify.Sound.Infra.Defs.trm ->
                      (Rename.Unify.Sound.Infra.Defs.kind Env.env,
                      Rename.Unify.Sound.Infra.Defs.typ) prod option **)
    
    let typinf' trm0 =
      let v = Rename.Unify.Sound.Infra.Defs.Coq_typ_fvar
        Variables.var_default
      in
      let Pair (o, v0) =
        typinf Env.empty Env.empty trm0 v
          (Variables.VarSet.S.singleton Variables.var_default) Env.empty (S
          (trm_depth trm0))
      in
      (match o with
         | Some p ->
             let Pair (k, s) = p in
             Some (Pair ((Env.map (Rename.Unify.Sound.Infra.kind_subst s) k),
             (Rename.Unify.Sound.Infra.typ_subst s v)))
         | None -> None)
    
    (** val coq_Gc : (bool, Rename2.Sound.JudgInfra.Judge.gc_kind) prod **)
    
    let coq_Gc =
      Pair (False, Rename2.Sound.JudgInfra.Judge.GcLet)
   end
 end

module Cstr = 
 struct 
  type cstr_impl = { cstr_low : Variables.vars;
                     cstr_high : Variables.vars option }
  
  (** val cstr_impl_rect : (Variables.vars -> Variables.vars option -> 'a1)
                           -> cstr_impl -> 'a1 **)
  
  let cstr_impl_rect f c =
    let { cstr_low = x; cstr_high = x0 } = c in f x x0
  
  (** val cstr_impl_rec : (Variables.vars -> Variables.vars option -> 'a1) ->
                          cstr_impl -> 'a1 **)
  
  let cstr_impl_rec f c =
    let { cstr_low = x; cstr_high = x0 } = c in f x x0
  
  (** val cstr_low : cstr_impl -> Variables.vars **)
  
  let cstr_low x = x.cstr_low
  
  (** val cstr_high : cstr_impl -> Variables.vars option **)
  
  let cstr_high x = x.cstr_high
  
  type cstr = cstr_impl
 end

module Const = 
 struct 
  type ops =
    | Coq_tag of Variables.var
    | Coq_matches of Variables.var list
  
  (** val ops_rect : (Variables.var -> 'a1) -> (Variables.var list -> __ ->
                     'a1) -> ops -> 'a1 **)
  
  let ops_rect f f0 = function
    | Coq_tag x -> f x
    | Coq_matches x -> f0 x __
  
  (** val ops_rec : (Variables.var -> 'a1) -> (Variables.var list -> __ ->
                    'a1) -> ops -> 'a1 **)
  
  let ops_rec f f0 = function
    | Coq_tag x -> f x
    | Coq_matches x -> f0 x __
  
  type const = ops
  
  (** val arity : ops -> nat **)
  
  let arity = function
    | Coq_tag v -> S O
    | Coq_matches l -> length l
 end

module Infer = MkInfer(Cstr)(Const)

module Delta = 
 struct 
  (** val matches_arg : nat -> Infer.Rename.Unify.Sound.Infra.Defs.typ **)
  
  let matches_arg n =
    Infer.Rename.Unify.Sound.Infra.Defs.Coq_typ_arrow
      ((Infer.Rename.Unify.Sound.Infra.Defs.Coq_typ_bvar n),
      (Infer.Rename.Unify.Sound.Infra.Defs.Coq_typ_bvar (S O)))
  
  (** val coq_type : Const.const -> Infer.Rename.Unify.Sound.Infra.Defs.sch **)
  
  let coq_type = function
    | Const.Coq_tag t0 -> { Infer.Rename.Unify.Sound.Infra.Defs.sch_type =
        (Infer.Rename.Unify.Sound.Infra.Defs.Coq_typ_arrow
        ((Infer.Rename.Unify.Sound.Infra.Defs.Coq_typ_bvar O),
        (Infer.Rename.Unify.Sound.Infra.Defs.Coq_typ_bvar (S O))));
        Infer.Rename.Unify.Sound.Infra.Defs.sch_kinds = (Cons (None, (Cons
        ((Some { Infer.Rename.Unify.Sound.Infra.Defs.kind_cstr =
        { Cstr.cstr_low = (Variables.VarSet.S.singleton t0); Cstr.cstr_high =
        None }; Infer.Rename.Unify.Sound.Infra.Defs.kind_rel = (Cons ((Pair
        (t0, (Infer.Rename.Unify.Sound.Infra.Defs.Coq_typ_bvar O))),
        Nil)) }), Nil)))) }
    | Const.Coq_matches l -> { Infer.Rename.Unify.Sound.Infra.Defs.sch_type =
        (let rec fold_right = function
           | Nil -> Infer.Rename.Unify.Sound.Infra.Defs.Coq_typ_arrow
               ((Infer.Rename.Unify.Sound.Infra.Defs.Coq_typ_bvar O),
               (Infer.Rename.Unify.Sound.Infra.Defs.Coq_typ_bvar (S O)))
           | Cons (b, t0) ->
               Infer.Rename.Unify.Sound.Infra.Defs.Coq_typ_arrow (b,
               (fold_right t0))
         in fold_right
              (let rec map0 = function
                 | Nil -> Nil
                 | Cons (a, t0) -> Cons ((matches_arg a), (map0 t0))
               in map0 (seq (S (S O)) (length l))));
        Infer.Rename.Unify.Sound.Infra.Defs.sch_kinds = (Cons ((Some
        { Infer.Rename.Unify.Sound.Infra.Defs.kind_cstr = { Cstr.cstr_low =
        Variables.VarSet.S.empty; Cstr.cstr_high = (Some 
        (mkset l)) }; Infer.Rename.Unify.Sound.Infra.Defs.kind_rel =
        (combine l
          (let rec map0 = function
             | Nil -> Nil
             | Cons (a, t0) -> Cons
                 ((Infer.Rename.Unify.Sound.Infra.Defs.Coq_typ_bvar a),
                 (map0 t0))
           in map0 (seq (S (S O)) (length l)))) }),
        (let rec map0 = function
           | Nil -> Nil
           | Cons (a, t0) -> Cons (None, (map0 t0))
         in map0 (seq O (S (length l)))))) }
  
  (** val matches_lhs : Variables.var list -> nat ->
                        Infer.Rename.Unify.Sound.Infra.Defs.trm **)
  
  let matches_lhs l k =
    Infer.Rename.Unify.Sound.Infra.Defs.Coq_trm_app
      ((Infer.Rename.Unify.Sound.Infra.const_app (Const.Coq_matches l)
         (let rec map0 = function
            | Nil -> Nil
            | Cons (a, t0) -> Cons
                ((Infer.Rename.Unify.Sound.Infra.Defs.Coq_trm_bvar a),
                (map0 t0))
          in map0 (seq (S O) (length l)))),
      (Infer.Rename.Unify.Sound.Infra.Defs.Coq_trm_app
      ((Infer.Rename.Unify.Sound.Infra.Defs.Coq_trm_cst (Const.Coq_tag
      (nth k l Variables.var_default))),
      (Infer.Rename.Unify.Sound.Infra.Defs.Coq_trm_bvar O))))
  
  (** val matches_rhs : nat -> Infer.Rename.Unify.Sound.Infra.Defs.trm **)
  
  let matches_rhs k =
    Infer.Rename.Unify.Sound.Infra.Defs.Coq_trm_app
      ((Infer.Rename.Unify.Sound.Infra.Defs.Coq_trm_bvar (S k)),
      (Infer.Rename.Unify.Sound.Infra.Defs.Coq_trm_bvar O))
 end

module Cstr2 = 
 struct 
  (** val unique : Cstr.cstr_impl -> Variables.VarSet.S.elt list **)
  
  let unique c =
    Variables.VarSet.S.elements c.Cstr.cstr_low
  
  (** val lub : Cstr.cstr_impl -> Cstr.cstr_impl -> Cstr.cstr_impl **)
  
  let lub c1 c2 =
    { Cstr.cstr_low =
      (Variables.VarSet.S.union c1.Cstr.cstr_low c2.Cstr.cstr_low);
      Cstr.cstr_high =
      (match c1.Cstr.cstr_high with
         | Some s1 ->
             (match c2.Cstr.cstr_high with
                | Some s2 -> Some (Variables.VarSet.S.inter s1 s2)
                | None -> c1.Cstr.cstr_high)
         | None -> c2.Cstr.cstr_high) }
  
  (** val valid : Cstr.cstr_impl -> sumbool **)
  
  let valid c =
    match c.Cstr.cstr_high with
      | Some v ->
          (match Variables.VarSet.S.subset c.Cstr.cstr_low v with
             | True -> Left
             | False -> Right)
      | None -> Left
 end

module Infer2 = Infer.Mk2(Delta)(Cstr2)
