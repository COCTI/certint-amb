(***************************************************************************
* Preservation and Progress for mini-ML (CBV) - Definitions                *
* Arthur Chargueraud, March 2007, Coq v8.1                                 *
* Extension to structural polymorphism                                     *
* Jacques Garrigue, October 2007 - May 2008                                *
***************************************************************************)

Set Implicit Arguments.
Require Import Metatheory List Arith.

(* Constraint domain specification *)

Module Type CstrIntf.
  Parameter cstr attr : Set.
  Parameter valid : cstr -> Prop.
  Parameter valid_dec : forall c, sumbool (valid c) (~valid c).
  Parameter eq_dec : forall x y:attr, {x=y}+{x<>y}.
  Parameter unique : cstr -> attr -> bool.
  Parameter lub : cstr -> cstr -> cstr.
  Parameter entails : cstr -> cstr -> Prop.
  Parameter entails_refl : forall c, entails c c.
  Hint Resolve entails_refl : core.
  Parameter entails_trans : forall c1 c2 c3,
    entails c1 c2 -> entails c2 c3 -> entails c1 c3.
  Parameter entails_lub : forall c1 c2 c,
    (entails c c1 /\ entails c c2) <-> entails c (lub c1 c2).
  Parameter entails_unique : forall c1 c2 v,
    entails c1 c2 -> unique c2 v = true -> unique c1 v = true.
  Parameter entails_valid : forall c1 c2,
    entails c1 c2 -> valid c1 -> valid c2.
  Parameter static : cstr -> bool.
  Parameter static_entails :
    forall c c', static c = true -> valid c' -> entails c' c -> entails c c'.

  (* 'a -> 'b *)
  Parameter arrow : cstr.
  Parameter arrow_dom : attr.
  Parameter arrow_cod : attr.
  Parameter arrow_attrs : arrow_dom <> arrow_cod.
  Parameter valid_arrow : valid arrow.
  Parameter static_arrow : static arrow = true.
  Parameter unique_dom : unique arrow arrow_dom = true.
  Parameter unique_cod : unique arrow arrow_cod = true.
  Parameter entails_arrow : forall c, entails c arrow -> c = arrow.

  (* 'a = 'b, or ('a, 'b) eq *)
  Parameter eq : cstr.
  Parameter eq_fst : attr.
  Parameter eq_snd : attr.
  Parameter eq_attrs : eq_fst <> eq_snd.
  Parameter valid_eq : valid eq.
  Parameter static_eq : static eq = true.
  Parameter unique_fst : unique eq eq_fst = true.
  Parameter unique_snd : unique eq eq_snd = true.
  Parameter entails_eq : forall c, entails c eq -> c = eq.
End CstrIntf.

Module Type CstIntf.
  Parameter const : Set.
  Parameter arity : const -> nat.
End CstIntf.

Declare Scope typ_scope.

(* Parameterized definitions *)

Module MkDefs(Cstr:CstrIntf)(Const:CstIntf).

(* ********************************************************************** *)
(** ** Description of types *)

(** Grammar of types. *)

Inductive typ : Set :=
  | typ_bvar  : nat -> typ
  | typ_fvar  : var -> typ.
  (* | typ_arrow : typ -> typ -> typ. *)

(** Types are inhabited, giving us a default value. *)

Definition typ_def := typ_bvar 0.

(** Constraint domain *)

Definition coherent kc (kr:list(Cstr.attr*typ)) := forall x T U,
  Cstr.unique kc x = true -> In (x,T) kr -> In (x,U) kr -> T = U.

Record ckind : Set := Kind {
  kind_cstr : Cstr.cstr;
  kind_valid : Cstr.valid kind_cstr;
  kind_rel  : list (Cstr.attr*typ);
  kind_coherent : coherent kind_cstr kind_rel }.

Definition static_ckind kc :=
  Cstr.static (kind_cstr kc) = true /\
  (forall x,
      Cstr.unique (kind_cstr kc) x = true -> In x (list_fst (kind_rel kc))).

Inductive rvar :=
  | rvar_b : nat -> rvar
  | rvar_f : var -> rvar
  | rvar_attr : rvar -> Cstr.attr -> rvar.

Definition kind : Set := option ckind * list rvar.
(* (main constructor, rigid variables) *)

Definition entails_ckind K K' :=
  Cstr.entails (kind_cstr K) (kind_cstr K') /\
  forall T:Cstr.attr*typ, In T (kind_rel K') -> In T (kind_rel K).

Definition entails (k k' : kind) :=
  match fst k, fst k' with
  | Some K, Some K' => entails_ckind K K'
  | _, None => True
  | None, Some _ => False
  end /\
  forall r, In r (snd k') -> In r (snd k).

(** Type schemes. *)

Record sch : Set := Sch { 
  sch_type  : typ ;
  sch_kinds : list kind }.

Notation "'sch_arity' M" :=
  (length (sch_kinds M)) (at level 20, no associativity).

(* Tree types *)

Inductive tree : Set :=
  (* | tr_bvar : nat -> tree *)
  | tr_arrow : tree -> tree -> tree
  | tr_eq : tree -> tree -> tree
  | tr_rvar : rvar -> tree.

(* Annotation: \( t -> t )/ *)

Definition tree_kind : Set :=
  option (Cstr.cstr * list (Cstr.attr*tree)) * list rvar.

Definition tree_type : Set :=
  tree * list tree_kind.

Lemma coherent_pair k (a b : Cstr.attr) (T T' : typ) :
  a <> b -> coherent k ((a,T) :: (b,T') :: nil).
Proof.
intros ab x U U' _; simpl.
destruct 1.
  destruct 1.
    inversions H; now inversions H0.
  destruct H0.
    inversions H; inversions H0. contradiction.
  contradiction.
destruct H.
  destruct 1.
    inversions H; inversions H0; contradiction.
  destruct H0.
    inversions H; now inversions H0.
  contradiction.
contradiction.
Qed.
    
Definition arrow_kind (m n : nat) :=
  Kind Cstr.valid_arrow
       (coherent_pair (T:=typ_bvar m) (T':=typ_bvar n) Cstr.arrow_attrs).
Definition eq_kind (m n : nat) :=
  Kind Cstr.valid_eq
       (coherent_pair (T:=typ_bvar m) (T':=typ_bvar n) Cstr.eq_attrs).

Fixpoint graph_of_tree ofs (tr : tree) : nat * list kind :=
  match tr with
  (* | tr_bvar n => (n, nil) *)
  | tr_arrow t1 t2 =>
    let '(n1, g1) := graph_of_tree (ofs + 1) t1 in
    let '(n2, g2) := graph_of_tree (ofs + length g1 + 1) t2 in
    (ofs, (Some (arrow_kind n1 n2), nil) :: g1 ++ g2)
  | tr_eq t1 t2 =>
    let '(n1, g1) := graph_of_tree (ofs + 1) t1 in
    let '(n2, g2) := graph_of_tree (ofs + length g1 + 1) t2 in
    (ofs, (Some (eq_kind n1 n2), nil) :: g1 ++ g2)
  | tr_rvar rv =>
    (ofs, (None, rv :: nil) :: nil)
  end.

Fixpoint graph_of_kinds ofs (Ks : list tree_kind) : list kind * list kind :=
  match Ks with
  | nil => (nil, nil)
  | (None,rvs) :: rem =>
    let '(K, K') := graph_of_kinds ofs rem in
    ((None,rvs) :: K, K')
  | (Some(kc,kr),rvs) :: rem =>
    let K' := fold_left
                (fun K' atr =>
                   let '(_, K'') :=
                       graph_of_tree (ofs + length K') (snd atr) in
                   K' ++ K'')
                kr nil
    in
    let '(K, K'') := graph_of_kinds (ofs + length K') rem in
    (K, K' ++ K'')
  end.
  
Definition graph_of_tree_type (S : tree_type) : nat * list kind :=
  let '(T,Ks) := S in
  let '(K,K') := graph_of_kinds (length Ks) Ks in
  let '(n,K'') := graph_of_tree (length K + length K') T in
  (n, K ++ K' ++ K'').

Eval compute in
  graph_of_tree_type (tr_arrow (tr_rvar (rvar_b 0)) (tr_rvar (rvar_b 1)), nil).

Definition static_tree_kind (k : tree_kind) :=
  match k with
  | (None,nil) => false
  | (None,_) => true
  | (Some (kc,kr),_) => Cstr.static kc
  end.

Fixpoint build_right_map pos ofs (Ks : list tree_kind) n :=
  match Ks with
  | nil => n
  | k :: rem =>
    if static_tree_kind k then
      if n === pos then ofs else build_right_map (S pos) (S ofs) rem n
    else build_right_map (S pos) ofs rem n
  end.

Section right_tree.
Variable V : nat -> nat.
Fixpoint bsubst_tree (T : tree) :=
  match T with
  (* | tr_bvar x => tr_bvar (V x) *)
  | tr_arrow T U => tr_arrow (bsubst_tree T) (bsubst_tree U)
  | tr_eq T U => tr_eq (bsubst_tree T) (bsubst_tree U)
  | tr_rvar r => T
  end.

Definition bsubst_tree_kind (k : tree_kind) :=
  match k with
  | (Some (c, trees), rvars) =>
    (Some (c, List.map (fun p => (fst p, bsubst_tree (snd p))) trees), rvars)
  | (None, rvars) => k
  end.

Definition right_tree_kinds :=
  map (fun k => if static_tree_kind k then bsubst_tree_kind k else k).
End right_tree.

Definition annotation_tree (S : tree_type) :=
  let '(T,K) := S in
  let V := build_right_map 0 (length K) K in
  (tr_arrow T (bsubst_tree T), K ++ right_tree_kinds K).

(* Need also to define substitution of rigid variables *)
Fixpoint rvar_open (k : nat) (u : rvar) (t : rvar) :=
  match t with
  | rvar_b i => if k === i then u else rvar_b i
  | rvar_f v => rvar_f v
  | rvar_attr r att => rvar_attr (rvar_open k u r) att
  end.

Fixpoint tree_open_rigid (k : nat) (u : rvar) (T : tree) :=
  match T with
  (* | tr_bvar _ => T *)
  | tr_arrow T1 T2 => tr_arrow (tree_open_rigid k u T1) (tree_open_rigid k u T2)
  | tr_eq T1 T2 => tr_eq (tree_open_rigid k u T1) (tree_open_rigid k u T2)
  | tr_rvar v => tr_rvar (rvar_open k u v)
  end.

Definition tree_type_open_rigid (k : nat) (u : rvar) (S : tree_type) :=
  (tree_open_rigid k u (fst S), snd S).

Fixpoint rvar_shift (k : nat) (t : rvar) :=
  match t with
  | rvar_b i => if le_lt_dec k i then rvar_b (i+1) else rvar_b i
  | rvar_f v => rvar_f v
  | rvar_attr r att => rvar_attr (rvar_shift k r) att
  end.

Fixpoint tree_shift_rigid (k : nat) (T : tree) :=
  match T with
  (* | tr_bvar _ => T *)
  | tr_arrow T1 T2 => tr_arrow (tree_shift_rigid k T1) (tree_shift_rigid k T2)
  | tr_eq T1 T2 => tr_eq (tree_shift_rigid k T1) (tree_shift_rigid k T2)
  | tr_rvar v => tr_rvar (rvar_shift k v)
  end.

Section tree_subst.
Variable S : env tree.

Inductive lookup_rvar : rvar -> tree -> Prop :=
  | lr_f : forall r T,
      binds r T S ->
      lookup_rvar (rvar_f r) T
  | lr_attr_dom : forall rv T1 T2,
      lookup_rvar rv (tr_arrow T1 T2) ->
      lookup_rvar (rvar_attr rv Cstr.arrow_dom) T1
  | lr_attr_cod : forall rv T1 T2,
      lookup_rvar rv (tr_arrow T1 T2) ->
      lookup_rvar (rvar_attr rv Cstr.arrow_cod) T2
  | lr_attr_fst : forall rv T1 T2,
      lookup_rvar rv (tr_eq T1 T2) ->
      lookup_rvar (rvar_attr rv Cstr.eq_fst) T1
  | lr_attr_snd : forall rv T1 T2,
      lookup_rvar rv (tr_eq T1 T2) ->
      lookup_rvar (rvar_attr rv Cstr.eq_snd) T2.

Inductive tree_subst_eq : tree -> tree -> Prop :=
  | tse_var1 : forall rv T1 T2,
      lookup_rvar rv T1 ->
      tree_subst_eq T1 T2 ->
      tree_subst_eq (tr_rvar rv) T2
  | tse_var2 : forall rv T1 T2,
      lookup_rvar rv T2 ->
      tree_subst_eq T1 T2 ->
      tree_subst_eq T1 (tr_rvar rv)
  | tse_arrow : forall T1 T2 T1' T2',
      tree_subst_eq T1 T1' -> tree_subst_eq T2 T2' ->
      tree_subst_eq (tr_arrow T1 T2) (tr_arrow T1' T2')
  | tse_eq : forall T1 T2 T1' T2',
      tree_subst_eq T1 T1' -> tree_subst_eq T2 T2' ->
      tree_subst_eq (tr_eq T1 T2) (tr_eq T1' T2')
  | tse_rvar : forall rv, tree_subst_eq (tr_rvar rv) (tr_rvar rv).

(*
Fixpoint tree_subst (T : tree) :=
  match T with
  | tr_bvar x => T
  | tr_arrow T U => tr_arrow (tree_subst T) (tree_subst U)
  | tr_eq T U => tr_eq (tree_subst T) (tree_subst U)
  | tr_rvar r =>
  end.
*)
End tree_subst.

Eval compute in
  graph_of_tree_type (
  annotation_tree (tr_arrow (tr_rvar (rvar_b 0)) (tr_rvar (rvar_b 1)), nil)).

(* Eval compute in
  annotation_tree (tr_arrow (tr_rvar (rvar_b 0)) (tr_bvar 0),
                   (None, rvar_b 1 :: nil) :: nil). 

Eval compute in
  graph_of_tree_type (
  annotation_tree (tr_arrow (tr_rvar (rvar_b 0)) (tr_bvar 0),
                   (None, rvar_b 1 :: nil) :: nil)). *)

(*
\/ 'a::int, 'b. eq('a, 'b)
Sch (tr_eq (tr_bvar 0) (tr_bvar 1)) [({sch_cstr:=int;...},nil); (None,nil)]

[({sch_cstr:=int;...},nil); (None,nil); ({sch_cstr:=int;...},nil)]
Vl : 0 => 0, 1 => 1
Vr : 0 => 2, 1 => 1

graph_of_tree Vl 3 s = (3, [(eq,{fst=>typ_bvar 0; snd=>typ_bar 2},nil)]) 
graph_of_tree Vr 4 s = (4, [(eq,{fst=>typ_bvar 1; snd=>typ_bar 2},nil)])
(typ_bvar 5,
[({sch_cstr:=int;...},nil); (None,nil); ({sch_cstr:=int;...},nil);
 (eq,{fst=>typ_bvar 0; snd=>typ_bvar 1},nil);
 (eq,{fst=>typ_bvar 2; snd=>typ_bvar 1},nil);
 (arrow,{left=>typ_bvar 3; right=> typ_bvar 4}, nil)]
*)

(** Opening body of type schemes. *)

Fixpoint typ_open (T : typ) (Vs : list typ) {struct T} : typ :=
  match T with
  | typ_bvar i => nth i Vs typ_def
  | typ_fvar x => typ_fvar x
  end.

(* Opening kind with rigid variables. *)

Definition kind_open_rigid (k : nat) (u : rvar) (t : kind) : kind :=
  (fst t, map (rvar_open k u) (snd t)).

Definition sch_open_rigid (k : nat) (u : rvar) (T : sch) : sch :=
  Sch (sch_type T) (map (kind_open_rigid k u) (sch_kinds T)).

(** Opening body of type schemes with variables *)

Definition typ_fvars := 
  List.map typ_fvar.

Definition typ_open_vars T Xs := 
  typ_open T (typ_fvars Xs).

(** Instanciation of a type scheme *)

Definition sch_open M := 
  typ_open (sch_type M).

Definition sch_open_vars M := 
  typ_open_vars (sch_type M).
  
Notation "M ^^ Vs" := (sch_open M Vs) 
  (at level 67, only parsing) : typ_scope.
Notation "M ^ Xs" := 
  (sch_open_vars M Xs) (only parsing) : typ_scope.

Bind Scope typ_scope with typ.
Open Scope typ_scope.

(** Locally closed types *)

Inductive type : typ -> Prop :=
  | type_fvar : forall X, 
      type (typ_fvar X).

(** List of n locally closed types *)

Definition types := list_for_n type.

(** Iterating and opening kinds *)

Definition kind_types (K:kind) :=
  match fst K with
  | None => nil
  | Some k => list_snd (kind_rel k)
  end.

Definition All_kind_types (P:typ->Prop) K :=
  list_forall P (kind_types K).

Lemma map_coherent : forall f kc kr,
  coherent kc kr ->
  coherent kc (map_snd f kr).
Proof.
  intros. intro; intros.
  puts (H x).
  destruct (map_snd_inv _ _ _ _ H1) as [T' [Heq Hin]].
  destruct (map_snd_inv _ _ _ _ H2) as [U' [Heq' Hin']].
  subst.
  rewrite* (H3 T' U').
Qed.

Definition ckind_map_spec (f:typ->typ) (k:ckind):
  {k' |  kind_cstr k = kind_cstr k' /\ 
  kind_rel k' = map_snd f (kind_rel k)}.
Proof.
  intros.
  destruct k as [kc kv kr kh].
  exists (Kind kv (map_coherent f kh)).
  simpl. auto.
Defined.

Definition ckind_map f k := proj1_sig (ckind_map_spec f k).

Definition kind_map f (K:kind) : kind :=
  (match fst K with
   | None => None
   | Some k => Some (ckind_map f k)
   end, snd K).

Definition kind_open K Vs := kind_map (fun T => typ_open T Vs) K.

(** Body of a scheme *)

Definition typ_body T Ks :=
  forall Xs, length Ks = length Xs ->
    type (typ_open_vars T Xs) /\
    list_forall (All_kind_types (fun T' => type (typ_open_vars T' Xs))) Ks.

(** Definition of a well-formed scheme *)

Definition scheme M :=
   typ_body (sch_type M) (sch_kinds M) /\ list_forall (fun _ => True) (sch_kinds M).

(* ********************************************************************** *)
(** ** Description of terms *)

(** Grammar of terms. *)

Inductive trm_sort := sort_typ | sort_rvar | sort_trm.

Inductive trm : Set :=
  | trm_eq    : trm
  | trm_bvar  : nat -> trm
  | trm_fvar  : var -> trm
  | trm_abs   : trm -> trm
  | trm_let   : trm -> trm -> trm
  | trm_app   : trm -> trm -> trm
  | trm_cst   : Const.const -> trm
  | trm_use   : trm -> tree -> tree -> trm -> trm
  | trm_rigid : trm -> trm
  | trm_ann   : tree -> trm.

(** Opening term binders. *)

Fixpoint trm_shift_rigid k (t : trm) : trm :=
  match t with
  | trm_eq | trm_bvar _ | trm_fvar _ | trm_cst _ => t
  | trm_abs t' => trm_abs (trm_shift_rigid k t')
  | trm_let t1 t2 => trm_let (trm_shift_rigid k t1) (trm_shift_rigid k t2)
  | trm_app t1 t2 => trm_app (trm_shift_rigid k t1) (trm_shift_rigid k t2)
  | trm_use t1 T1 T2 t2 =>
    trm_use (trm_shift_rigid k t1) (tree_shift_rigid k T1)
            (tree_shift_rigid k T1) (trm_shift_rigid k t2)
  | trm_rigid t => trm_rigid (trm_shift_rigid (k+1) t)
  | trm_ann T => trm_ann (tree_shift_rigid k T)
  end.

Fixpoint trm_open_rec (k : nat) (u : trm) (t : trm) {struct t} : trm :=
  match t with
  | trm_eq        => trm_eq
  | trm_bvar i    => if k === i then u else (trm_bvar i)
  | trm_fvar x    => trm_fvar x 
  | trm_abs t1    => trm_abs (trm_open_rec (S k) u t1) 
  | trm_let t1 t2 => trm_let (trm_open_rec k u t1) (trm_open_rec (S k) u t2) 
  | trm_app t1 t2 => trm_app (trm_open_rec k u t1) (trm_open_rec k u t2)
  | trm_cst c     => trm_cst c
  | trm_use t1 T U t2 => trm_use (trm_open_rec k u t1) T U (trm_open_rec k u t2)
  | trm_rigid t => trm_rigid (trm_open_rec k (trm_shift_rigid 0 u) t)
  | trm_ann T     => trm_ann T
  end.

Definition trm_open t u := trm_open_rec 0 u t.

(* Notation "{ k ~> u } t" := (trm_open_rec k u t) (at level 67). *)
Notation "t ^^ u" := (trm_open t u) (at level 67).
Notation "t ^ x" := (trm_open t (trm_fvar x)).


Fixpoint trm_rigid_rec (k : nat) (u : rvar) (t : trm) {struct t} : trm :=
  match t with
  | trm_eq        => trm_eq
  | trm_bvar i    => trm_bvar i
  | trm_fvar x    => trm_fvar x 
  | trm_abs t1    => trm_abs (trm_rigid_rec k u t1) 
  | trm_let t1 t2 => trm_let (trm_rigid_rec k u t1) (trm_rigid_rec (S k) u t2) 
  | trm_app t1 t2 => trm_app (trm_rigid_rec k u t1) (trm_rigid_rec k u t2)
  | trm_cst c     => trm_cst c
  | trm_use t1 T U t2 =>
    trm_use (trm_rigid_rec k u t1) (tree_open_rigid k u T)
            (tree_open_rigid k u U) (trm_rigid_rec k u t2)
  | trm_rigid t => trm_rigid (trm_rigid_rec (S k) u t)
  | trm_ann T   => trm_ann (tree_open_rigid k u T)
  end.

Definition trm_open_rigid t u := trm_rigid_rec 0 u t.

(** Locally closed termessions *)

Inductive term : trm -> Prop :=
  | term_var : forall x, 
      term (trm_fvar x)
  | term_abs : forall L t1,
      (forall x, x \notin L -> term (t1 ^ x)) -> 
      term (trm_abs t1)
  | term_let : forall L t1 t2,
      term t1 -> 
      (forall x, x \notin L -> term (t2 ^ x)) -> 
      term (trm_let t1 t2)
  | term_app : forall t1 t2,
      term t1 -> 
      term t2 -> 
      term (trm_app t1 t2)
  | term_cst : forall c,
      term (trm_cst c)
  | term_rigid : forall t1,
      term t1 ->
      term (trm_rigid t1)
  | term_use : forall t1 T1 T2 t2,
      term t1 ->
      term t2 ->
      term (trm_use t1 T1 T2 t2)
  | term_ann : forall T,
      (* tree T -> *)
      term (trm_ann T)
  | term_eq : term trm_eq.


(** Definition of the body of an abstraction *)

Definition term_body t :=
  exists L, forall x, x \notin L -> term (t ^ x).

(** Term instanciation *)

Definition trm_def := trm_bvar 0.

Fixpoint trm_inst_rec (k : nat) (tl : list trm) (t : trm) {struct t} : trm :=
  match t with
  | trm_eq        => trm_eq
  | trm_bvar i    => if le_lt_dec k i then nth (i-k) tl t else trm_bvar i
  | trm_fvar x    => trm_fvar x 
  | trm_abs t1    => trm_abs (trm_inst_rec (S k) tl t1) 
  | trm_let t1 t2 => trm_let (trm_inst_rec k tl t1) (trm_inst_rec (S k) tl t2) 
  | trm_app t1 t2 => trm_app (trm_inst_rec k tl t1) (trm_inst_rec k tl t2)
  | trm_cst c     => trm_cst c
  | trm_use t1 T U t2 =>
    trm_use (trm_inst_rec k tl t1) T U (trm_inst_rec k tl t2)
  | trm_rigid t   => trm_rigid (trm_inst_rec k tl t)
  | trm_ann T     => trm_ann T (* need to substitute *)
  end.

Definition trm_inst t tl := trm_inst_rec 0 tl t.

(** Applying a constant *)

Definition const_app c vl := fold_left trm_app vl (trm_cst c).

(* ********************************************************************** *)
(** ** Description of typing *)

(** Definition of kinding environments *)

Inductive qitem :=
  | qvar : var -> qitem
  | qeq : tree -> tree -> qitem.

Definition qenv := list qitem.

Inductive qsat_item (S : env tree) : qitem -> Prop :=
| qsat_qvar : forall x, qsat_item S (qvar x)
| qsat_qeq : forall T1 T2, tree_subst_eq S T1 T2 -> qsat_item S (qeq T1 T2).

Definition qsat Q S := list_forall (qsat_item S) Q.

Inductive qcoherent (Q : qenv) : kind -> Prop :=
  | qc_var : forall rvs,
      (forall rv1 rv2 S, qsat Q S -> In rv1 rvs -> In rv2 rvs ->
          tree_subst_eq S (tr_rvar rv1) (tr_rvar rv2)) ->
      qcoherent Q (None, rvs)
  | qc_arrow : forall k rvs,
      kind_cstr k = Cstr.arrow ->
      (forall S, qsat Q S ->
         exists T1 T2, forall rv,
             In rv rvs -> tree_subst_eq S (tr_rvar rv) (tr_arrow T1 T2)) ->
      qcoherent Q (Some k, rvs)
  | qc_eq : forall k rvs,
      kind_cstr k = Cstr.eq ->
      (forall S, qsat Q S ->
         exists T1 T2, forall rv,
             In rv rvs -> tree_subst_eq S (tr_rvar rv) (tr_eq T1 T2)) ->
      qcoherent Q (Some k, rvs).

Definition kenv := env kind.

Inductive is_prefix : rvar -> rvar -> Prop :=
| prefix_eq : forall r, is_prefix r r
| prefix_attr : forall r s attr, is_prefix r s ->
                            is_prefix r (rvar_attr s attr).

Inductive wf_kind : kenv -> kind -> Prop :=
| wf_empty : forall K r, wf_kind K (None, r)
| wf_attrs : forall K (ck : ckind) (r : list rvar),
    (forall l a,
        Cstr.unique (kind_cstr ck) l = true ->
        In (l, typ_fvar a) (kind_rel ck) ->
        (exists k rvs, binds a (k, rvs) K /\
          (forall rv, In rv r ->
            (exists rv', In rv' rvs /\ is_prefix rv' (rvar_attr rv l))))) ->
    wf_kind K (Some ck, r).

Definition kenv_ok (Q : qenv) K :=
  ok K /\ env_prop (All_kind_types type) K /\ env_prop (qcoherent Q) K
  /\ env_prop (wf_kind K) K.

(** Proper instantiation *)

Inductive well_kinded : kenv -> kind -> typ -> Prop :=
  | wk_any : forall K T,
      well_kinded K (None, nil) T
  | wk_kind : forall k' K k x,
      binds x k' K ->
      entails k' k ->
      wf_kind K k' ->
      well_kinded K k (typ_fvar x).

Hint Constructors well_kinded : core.

Definition kinds_open Ks Us :=
  List.map (fun k:kind => kind_open k Us) Ks.

Definition proper_instance K Ks Us :=
  types (length Ks) Us /\
  list_forall2 (well_kinded K) (kinds_open Ks Us) Us.

Definition kinds_open_vars Ks Xs :=
  List.combine Xs (kinds_open Ks (typ_fvars Xs)).

(** Definition of typing environments *)

Definition env := env sch.

Definition env_ok (E:env) := ok E /\ env_prop scheme E.

(** Computing free variables of a type. *)

Definition typ_fv (T : typ) : vars :=
  match T with
  | typ_bvar i      => {}
  | typ_fvar x      => {{x}}
(*   | typ_arrow T1 T2 => (typ_fv T1) \u (typ_fv T2) *)
  end.

(** Computing free variables of a list of terms. *)

Definition typ_fv_list :=
  List.fold_right (fun t acc => typ_fv t \u acc) {}.

(** Computing free variables of a kind. *)

Definition kind_fv k :=
  typ_fv_list (kind_types k).

Definition kind_fv_list :=
  List.fold_right (fun t acc => kind_fv t \u acc) {}.

(** Computing free variables of a type scheme. *)

Definition sch_fv M := 
  typ_fv (sch_type M) \u kind_fv_list (sch_kinds M).

(** Computing free type variables of the values of an environment. *)

Definition env_fv := 
  fv_in sch_fv.

(** Grammar of values *)

Inductive valu : nat -> trm -> Prop :=
  | value_abs : forall t1, term (trm_abs t1) -> valu 0 (trm_abs t1)
  | value_cst : forall c, valu (Const.arity c) (trm_cst c)
  | value_app : forall n t1 n2 t2,
      valu (S n) t1 ->
      valu n2 t2 ->
      valu n (trm_app t1 t2)
  | value_eq  : valu 0 trm_eq
  | value_ann : forall n t T, valu n t -> valu n (trm_app (trm_ann T) t)
  | value_rigid : forall n t, valu n t -> valu n (trm_rigid t)
  | value_use : forall t1 T1 T2 n t2,
      valu 0 t1 -> valu n t2 -> valu n (trm_use t1 T1 T2 t2).

Definition value t := exists n, valu n t.

(** Another functor for delta-rules *)

Module Type DeltaIntf.
  Parameter type : Const.const -> sch.
  Parameter closed : forall c, sch_fv (type c) = {}.
  Parameter scheme : forall c, scheme (type c).
  Parameter reduce : forall c tl,
    list_for_n value (S(Const.arity c)) tl -> trm.
  Parameter term : forall c tl vl,
    term (@reduce c tl vl).
End DeltaIntf.

Module MkJudge(Delta:DeltaIntf).

(** The typing judgment *)

(*Reserved Notation "K ; E ; Q | gc |= t ~: T" (at level 69).*)

Inductive gc_kind : Set := GcAny | GcLet.
Definition gc_info : Set := (bool * gc_kind)%type.
Fixpoint gc_ok (gc:gc_info) := fst gc = true. 
Fixpoint gc_raise (gc:gc_info) : gc_info :=
  match snd gc with
  | GcLet => (true, GcLet)
  | _ => gc
  end.
Fixpoint gc_lower (gc:gc_info) : gc_info :=
  match snd gc with
  | GcLet => (false, GcLet)
  | _ => gc
  end.

Reserved Notation "[ Q ; K ; E | gc |= t ~: T ]" (at level 69).

Inductive typing (gc:gc_info) : qenv -> kenv -> env -> trm -> typ -> Prop :=
  | typing_var : forall Q K E x M Us,
      kenv_ok Q K ->
      env_ok E -> 
      binds x M E -> 
      proper_instance K (sch_kinds M) Us ->
      [ Q; K; E | gc |= (trm_fvar x) ~: (M ^^ Us) ]
  | typing_abs : forall Q L (K : kenv) E U T t1 V k rvs,
      type U ->
      binds V (Some k, rvs) K ->
      kind_cstr k = Cstr.arrow ->
      In (Cstr.arrow_dom, U) (kind_rel k) ->
      In (Cstr.arrow_cod, T) (kind_rel k) ->
      (forall x, x \notin L -> 
        [ Q; K; (E & x ~ Sch U nil) | gc_raise gc |= (t1 ^ x) ~: T ]) ->
      [ Q; K; E | gc |= (trm_abs t1) ~: typ_fvar V ]
  | typing_let : forall Q M L1 L2 K E T2 t1 t2,
      (forall Xs, fresh L1 (sch_arity M) Xs ->
         [ Q; (K & kinds_open_vars (sch_kinds M) Xs); E | gc_raise gc |=
           t1 ~: (M ^ Xs) ]) ->
      (forall x, x \notin L2 ->
         [ Q; K; (E & x ~ M) | gc_raise gc |= (t2 ^ x) ~: T2]) -> 
      [ Q; K; E | gc |= (trm_let t1 t2) ~: T2 ]
  | typing_app : forall Q K E V k rvs S T t1 t2,
      binds V (Some k, rvs) K ->
      kind_cstr k = Cstr.arrow ->
      In (Cstr.arrow_dom, S) (kind_rel k) ->
      In (Cstr.arrow_cod, T) (kind_rel k) ->
      [ Q; K; E | gc_lower gc |= t1 ~: typ_fvar V ] ->
      [ Q; K; E | gc_lower gc |= t2 ~: S ] ->   
      [ Q; K; E | gc |= (trm_app t1 t2) ~: T ]
  | typing_cst : forall Q K E Us c,
      kenv_ok Q K ->
      env_ok E ->
      proper_instance K (sch_kinds (Delta.type c)) Us ->
      [ Q; K; E | gc |= (trm_cst c) ~: (Delta.type c ^^ Us) ]
  | typing_gc : forall Q Ks L K E t T,
      gc_ok gc ->
      (forall Xs, fresh L (length Ks) Xs ->
        [ Q; K & kinds_open_vars Ks Xs; E | gc |= t ~: T ]) ->
      [ Q; K; E | gc |= t ~: T ]
  | typing_ann : forall Q (T : tree) n Ks K E Us,
      kenv_ok Q K ->
      env_ok E ->
      graph_of_tree_type (annotation_tree (T,nil)) = (n, Ks) ->
      proper_instance K Ks Us ->
      [ Q; K; E | gc |= (trm_ann T) ~: nth n Us typ_def ]
  | typing_rigid : forall Q L K Ks Us E t T,
      proper_instance K ((None, nil) :: Ks) Us ->
      (forall R Xs, fresh L (1 + length Us) (R :: Xs) ->
        [ qvar R :: Q; K & kinds_open_vars ((None, rvar_f R :: nil) :: Ks) Xs; E
        | gc_raise gc |= trm_open_rigid t (rvar_f R) ~: typ_open_vars T Xs ]) ->
      [ Q; K; E | gc |= trm_rigid t ~: typ_open T Us ]
  | typing_use : forall n Ks Us Q K E t T1 T2,
      graph_of_tree_type (tr_eq T1 T2, nil) = (n, Ks) ->
      proper_instance K Ks Us ->
      env_prop (qcoherent Q) K ->
      [ qeq T1 T2 :: Q; K; E | gc_raise gc |= t ~: nth n Us typ_def ] -> 
      [ Q; K; E | gc |= t ~: nth n Us typ_def ]
  | typing_eq : forall Q K E x k rs T,
      kenv_ok Q K ->
      env_ok E ->
      binds x (Some k, rs) K ->
      In (Cstr.eq_fst, T) (kind_rel k) ->
      In (Cstr.eq_snd, T) (kind_rel k) ->
      [ Q; K; E | gc |= trm_eq ~: typ_fvar x ]

where "[ Q ; K ; E | gc |= t ~: T ]" := (typing gc Q K E t T).


(* ********************************************************************** *)
(** ** Description of the semantics *)

(** Reduction rules *)

Inductive red : trm -> trm -> Prop :=
  | red_abs : forall t1 t2, 
      term (trm_abs t1) -> 
      value t2 ->  
      red (trm_app (trm_abs t1) t2) (t1 ^^ t2)
  | red_let : forall t1 t2, 
      term (trm_let t1 t2) ->
      value t1 -> 
      red (trm_let t1 t2) (t2 ^^ t1)
  | red_delta : forall c tl vl,
      red (const_app c tl) (@Delta.reduce c tl vl)
  | red_let_1 : forall t1 t1' t2, 
      term_body t2 ->
      red t1 t1' -> 
      red (trm_let t1 t2) (trm_let t1' t2)
  | red_app_1 : forall t1 t1' t2,
      value t2 ->
      red t1 t1' -> 
      red (trm_app t1 t2) (trm_app t1' t2)
  | red_app_2 : forall t1 t2 t2', 
      term t1 ->
      red t2 t2' ->
      red (trm_app t1 t2) (trm_app t1 t2')
  | red_use_1 : forall t1 t1' T T' t2,
      term t1 ->
      term t2 ->
      red t1 t1' ->
      red (trm_use t1 T T' t2) (trm_use t1' T T' t2)
  | red_use_2 : forall t1 T T' t2 t2',
      term t1 ->
      term t2 ->
      red t2 t2' ->
      red (trm_use t1 T T' t2) (trm_use t1 T T' t2')
  | red_rigid : forall t t',
      term t ->
      red t t' ->
      red (trm_rigid t) (trm_rigid t')
  (* | red_drop_ann  : forall rv t t',
      term t ->
      term t' ->
      red (trm_app (trm_app (trm_ann (tr_rvar rv, nil)) t) t')
          (trm_app t t') *)
  | red_apply_ann_1 : forall T U t t',
      term (trm_abs t) ->
      term t' ->
      red (trm_app (trm_app (trm_ann (tr_arrow T U)) (trm_abs t)) t')
          (trm_let (trm_app (trm_ann T) t')
                   (trm_app (trm_ann U) t))
  | red_apply_ann_2 : forall r t t',
      term (trm_abs t) ->
      term t' ->
      red (trm_app (trm_app (trm_ann (tr_rvar r)) (trm_abs t)) t')
          (trm_let (trm_app (trm_ann (tr_rvar (rvar_attr r Cstr.arrow_dom))) t')
                   (trm_app (trm_ann (tr_rvar (rvar_attr r Cstr.arrow_cod))) t))
  | red_apply_use : forall t1 T1 T2 t2 t3,
      term t1 -> term t2 -> term t3 ->
      red (trm_app (trm_use t1 T1 T2 t2) t3)
          (trm_use t1 T1 T2 (trm_app t2 t3))
  | red_apply_rigid : forall t1 t2,
      term t1 -> term t2 ->
      red (trm_app (trm_rigid t1) t2)
          (trm_rigid (trm_app t1 (trm_shift_rigid 0 t2))).
               

Notation "t --> t'" := (red t t') (at level 68).


(* ********************************************************************** *)
(** ** Description of the results *)

(** Goal is to prove preservation and progress *)

Definition preservation := forall Q K E t t' T,
  [ Q; K; E | (true,GcAny) |= t ~: T ] ->
  t --> t' ->
  [ Q; K; E | (true,GcAny) |= t' ~: T ].

Definition progress := forall Q K t T, 
  [ Q; K; empty | (true,GcAny) |= t ~: T ] ->
     value t
  \/ exists t', t --> t'.

End MkJudge.

End MkDefs.
