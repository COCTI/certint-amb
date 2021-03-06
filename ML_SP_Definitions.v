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
  Global Hint Resolve entails_refl : core.
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
    forall c c', static c = true -> valid c' -> entails c' c -> c = c'.

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

  Parameter arrow_eq : arrow <> eq.
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
Definition var_def := var_generate {}.

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

(** Definition of kinding environment *)

Definition kenv := env kind.

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
  | tr_rvar : rvar -> tree
  | tr_stuck : tree -> Cstr.attr -> tree.

(* Relation of tree type constructors with kinds *)

Record tycon_info := mkTycon
  { ty_con : tree -> tree -> tree;
    ty_cstr : Cstr.cstr;
    ty_attr1 : Cstr.attr;
    ty_attr2 : Cstr.attr;
    ty_unique1 : Cstr.unique ty_cstr ty_attr1 = true;
    ty_unique2 : Cstr.unique ty_cstr ty_attr2 = true;
    ty_static : Cstr.static ty_cstr = true }.

Variant tycon_kind : tycon_info -> Prop :=
| tk_arrow : tycon_kind
    (mkTycon tr_arrow Cstr.unique_dom Cstr.unique_cod Cstr.static_arrow)
| tk_eq    : tycon_kind
    (mkTycon tr_eq Cstr.unique_fst Cstr.unique_snd Cstr.static_eq).

Lemma ty_cstr_inj ty ty' :
  tycon_kind ty -> tycon_kind ty' -> ty_cstr ty = ty_cstr ty' -> ty = ty'.
Proof.
  induction 1; induction 1; auto; simpl; intros; now elim Cstr.arrow_eq.
Qed.

(** Instantiation of a tree *)

Inductive tree_instance (K : kenv) : var -> tree -> Prop :=
  | tri_rvar : forall x k rvs rv,
      binds x (k,rvs) K ->
      In rv rvs ->
      tree_instance K x (tr_rvar rv)
  | tri_tycon : forall x ck rvs y z ty T1 T2,
      binds x (Some ck, rvs) K ->
      tycon_kind ty ->
      kind_cstr ck = ty_cstr ty ->
      In (ty_attr1 ty, typ_fvar y) (kind_rel ck) ->
      In (ty_attr2 ty, typ_fvar z) (kind_rel ck) ->
      tree_instance K y T1 ->
      tree_instance K z T2 ->
      tree_instance K x (ty_con ty T1 T2).

Lemma tree_instance_binds K x T :
  tree_instance K x T -> exists kr, binds x kr K.
Proof. intros []; esplit; auto*. Qed.

(* Need also to define substitution of rigid variables *)
Fixpoint rvar_open (k : nat) (u : rvar) (t : rvar) :=
  match t with
  | rvar_b i =>
    if k === i then u else rvar_b (if le_lt_dec k i then i-1 else i)
  | rvar_f v => rvar_f v
  | rvar_attr r att => rvar_attr (rvar_open k u r) att
  end.

Fixpoint tree_open_rigid (k : nat) (u : rvar) (T : tree) :=
  match T with
  (* | tr_bvar _ => T *)
  | tr_arrow T1 T2 => tr_arrow (tree_open_rigid k u T1) (tree_open_rigid k u T2)
  | tr_eq T1 T2 => tr_eq (tree_open_rigid k u T1) (tree_open_rigid k u T2)
  | tr_rvar v => tr_rvar (rvar_open k u v)
  | tr_stuck T1 l => tr_stuck (tree_open_rigid k u T1) l
  end.

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
  | tr_stuck T1 l => tr_stuck (tree_shift_rigid k T1) l
  end.

Section tree_subst.
Variable S : env tree.

Fixpoint rvar_subst V :=
  match V with
  | rvar_f x =>
    match get x S with
    | None => tr_rvar V
    | Some T => T
    end
  | rvar_b _ => tr_rvar V
  | rvar_attr V a =>
    let T := rvar_subst V in
    match T with
    | tr_arrow T1 T2 =>
      if Cstr.eq_dec a Cstr.arrow_dom then T1 else
        if Cstr.eq_dec a Cstr.arrow_cod then T2 else
          tr_stuck T a
    | tr_eq T1 T2 =>
      if Cstr.eq_dec a Cstr.eq_fst then T1 else
        if Cstr.eq_dec a Cstr.eq_snd then T2 else
          tr_stuck T a
    | tr_rvar r =>
      tr_rvar (rvar_attr r a)
    | _ =>
      tr_stuck T a
    end
  end.

Fixpoint tree_subst T :=
  match T with
  | tr_rvar rv     => rvar_subst rv
  | tr_arrow T1 T2 => tr_arrow (tree_subst T1) (tree_subst T2)
  | tr_eq T1 T2    => tr_eq (tree_subst T1) (tree_subst T2)
  | tr_stuck T1 a  => tr_stuck (tree_subst T1) a
  end.

Definition tree_subst_eq T1 T2 := tree_subst T1 = tree_subst T2.

Lemma tree_subst_tycon ty T1 T2 :
  tycon_kind ty ->
  tree_subst (ty_con ty T1 T2) =
  ty_con ty (tree_subst T1) (tree_subst T2).
Proof. intros []; simpl*. Qed.

Lemma tree_subst_eq_refl T : tree_subst_eq T T.
Proof. induction T; simpl; constructor; auto. Qed.
End tree_subst.

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

(** Coherence *)

Inductive qsat_item (S : env tree) : tree * tree -> Prop :=
| qsat_qeq : forall T1 T2, tree_subst_eq S T1 T2 -> qsat_item S (T1, T2).

Definition qenv := list (tree * tree).

Section qcoherent.
Variable Q : qenv.

Definition qsat S := list_forall (qsat_item S) Q.

Definition qcoherent_rvars rvs :=
  forall rv1 rv2 S, qsat S -> In rv1 rvs -> In rv2 rvs ->
                    tree_subst_eq S (tr_rvar rv1) (tr_rvar rv2).

Definition qcoherent_tycon ty rvs :=
  forall rv S, qsat S -> In rv rvs ->
               tree_subst_eq S (tr_rvar rv)
                     (ty_con ty (tr_rvar (rvar_attr rv (ty_attr1 ty)))
                                (tr_rvar (rvar_attr rv (ty_attr2 ty)))).

Inductive qcoherent : kind -> Prop :=
  | qc_var : forall rvs,
      qcoherent_rvars rvs ->
      qcoherent (None, rvs)
  | qc_tycon : forall ty k rvs,
      tycon_kind ty ->
      kind_cstr k = ty_cstr ty ->
      qcoherent_rvars rvs ->
      qcoherent_tycon ty rvs ->
      qcoherent (Some k, rvs).

Lemma tree_subst_eq_rvars k rvs : qcoherent (k, rvs) -> qcoherent_rvars rvs.
Proof. intros; inversions* H. Qed.

End qcoherent.

(* Properties of kinding environments *)

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
                       forall rv, In rv r -> In (rvar_attr rv l) rvs))
            (*(exists rv', In rv' rvs /\ is_prefix rv' (rvar_attr rv l)))))*) ->
    wf_kind K (Some ck, r).

Definition kenv_ok (Q : qenv) K :=
  ok K /\ env_prop (All_kind_types type) K /\ env_prop (qcoherent Q) K
  /\ env_prop (wf_kind K) K.

Definition kinds_open Ks Us :=
  List.map (fun k:kind => kind_open k Us) Ks.

Definition kinds_open_vars Ks Xs :=
  List.combine Xs (kinds_open Ks (typ_fvars Xs)).

(** Body of a scheme *)

Definition typ_body Q K T Ks :=
  list_forall (qcoherent Q) Ks /\
  forall Xs, length Ks = length Xs ->
    type (typ_open_vars T Xs) /\
    list_forall (All_kind_types (fun T' => type (typ_open_vars T' Xs))) Ks /\
    exists L, fresh L (length Ks) Xs ->
              list_forall (wf_kind (K & kinds_open_vars Ks Xs))
                          (kinds_open Ks (typ_fvars Xs)).

(** Definition of a well-formed scheme *)

Definition scheme Q K M :=
   typ_body Q K (sch_type M) (sch_kinds M).

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
  | trm_ann   : trm -> tree -> trm.

(** Opening term binders. *)

Fixpoint trm_shift_rigid k (t : trm) : trm :=
  match t with
  | trm_eq | trm_bvar _ | trm_fvar _ | trm_cst _ => t
  | trm_abs t' => trm_abs (trm_shift_rigid k t')
  | trm_let t1 t2 => trm_let (trm_shift_rigid k t1) (trm_shift_rigid k t2)
  | trm_app t1 t2 => trm_app (trm_shift_rigid k t1) (trm_shift_rigid k t2)
  | trm_use t1 T1 T2 t2 =>
    trm_use (trm_shift_rigid k t1) (tree_shift_rigid k T1)
            (tree_shift_rigid k T2) (trm_shift_rigid k t2)
  | trm_rigid t => trm_rigid (trm_shift_rigid (k+1) t)
  | trm_ann t T => trm_ann (trm_shift_rigid k t) (tree_shift_rigid k T)
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
  | trm_ann t1 T  => trm_ann (trm_open_rec k u t1) T
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
  | trm_let t1 t2 => trm_let (trm_rigid_rec k u t1) (trm_rigid_rec k u t2) 
  | trm_app t1 t2 => trm_app (trm_rigid_rec k u t1) (trm_rigid_rec k u t2)
  | trm_cst c     => trm_cst c
  | trm_use t1 T U t2 =>
    trm_use (trm_rigid_rec k u t1) (tree_open_rigid k u T)
            (tree_open_rigid k u U) (trm_rigid_rec k u t2)
  | trm_rigid t1  => trm_rigid (trm_rigid_rec (S k) (rvar_shift 0 u) t1)
  | trm_ann t1 T  => trm_ann (trm_rigid_rec k u t1) (tree_open_rigid k u T)
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
  | term_ann : forall t1 T1,
      term t1 ->
      term (trm_ann t1 T1)
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
  | trm_ann t1 T  => trm_ann (trm_inst_rec k tl t1) T (* need to substitute *)
  end.

Definition trm_inst t tl := trm_inst_rec 0 tl t.

(** Applying a constant *)

Definition const_app c vl := fold_left trm_app vl (trm_cst c).

(* ********************************************************************** *)
(** ** Description of typing *)

(** Proper instantiation *)

Inductive well_kinded : kenv -> kind -> typ -> Prop :=
  (*| wk_any : forall K T,
      well_kinded K (None, nil) T*)
  | wk_kind : forall k' K k x,
      binds x k' K ->
      entails k' k ->
      wf_kind K k' ->
      well_kinded K k (typ_fvar x).

Global Hint Constructors well_kinded : core.

Definition proper_instance K Ks Us :=
  types (length Ks) Us /\
  list_forall2 (well_kinded K) (kinds_open Ks Us) Us.

(** Definition of typing environments *)

Definition env := env sch.

Definition env_ok Q K (E:env) := ok E /\ env_prop (scheme Q K) E.

(** Grammar of values *)

Inductive valu : nat -> trm -> Prop :=
  | value_abs : forall t1, term (trm_abs t1) -> valu 0 (trm_abs t1)
  | value_cst : forall c, valu (Const.arity c) (trm_cst c)
  | value_app : forall n t1 n2 t2,
      valu (S n) t1 ->
      valu n2 t2 ->
      valu n (trm_app t1 t2)
  | value_eq  : valu 0 trm_eq
  | value_ann : forall n t T, valu n t -> valu 0 (trm_ann t T)
  | value_rigid : forall n t, valu n t -> valu n (trm_rigid t)
  | value_use : forall t1 T1 T2 n t2,
      valu 0 t1 -> valu n t2 -> valu n (trm_use t1 T1 T2 t2).

Definition value t := exists n, valu n t.

(** Another functor for delta-rules *)

Module Type DeltaIntf.
  Parameter type : Const.const -> sch.
  Parameter closed : forall c, sch_fv (type c) = {}.
  Parameter scheme : forall c, scheme nil empty (type c).
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
      env_ok Q K E -> 
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
      env_ok Q K E ->
      proper_instance K (sch_kinds (Delta.type c)) Us ->
      [ Q; K; E | gc |= (trm_cst c) ~: (Delta.type c ^^ Us) ]
  | typing_gc : forall Q Ks L K E t T,
      gc_ok gc ->
      (forall Xs, fresh L (length Ks) Xs ->
        [ Q; K & kinds_open_vars Ks Xs; E | gc |= t ~: T ]) ->
      [ Q; K; E | gc |= t ~: T ]
(* | typing_ann : forall Q t (T : tree) n Ks K E Us Us',
      graph_of_tree_type T = (n, Ks) ->
      proper_instance K Ks Us ->
      proper_instance K Ks Us' ->
      [ Q; K; E | gc_lower gc |= t ~: nth n Us typ_def ] ->
      [ Q; K; E | gc |= (trm_ann t T) ~: nth n Us' typ_def ] *)
  | typing_ann : forall Q t (T : tree) K E x y,
      tree_instance K x T ->
      tree_instance K y T ->
      [ Q; K; E | gc_lower gc |= t ~: typ_fvar x ] ->
      [ Q; K; E | gc |= (trm_ann t T) ~: typ_fvar y ]
  | typing_rigid : forall Q L K Ks Us E t T,
      kenv_ok Q K ->
      env_ok Q K E ->
      proper_instance K ((None, nil) :: Ks) Us ->
      (forall R Xs, fresh L (1 + length Us) (R :: Xs) ->
        [ Q; K & kinds_open_vars ((None, rvar_f R :: nil) :: Ks) Xs; E
        | gc_raise gc |= trm_open_rigid t (rvar_f R) ~: typ_open_vars T Xs ]) ->
      [ Q; K; E | gc |= trm_rigid t ~: typ_open T Us ]
(* | typing_use : forall n Ks Us Q K E t1 T1 T2 t2 T,
      graph_of_tree_type (tr_eq T1 T2) = (n, Ks) ->
      proper_instance K Ks Us ->
      [ Q; K; E | gc_raise gc |= t1 ~: nth n Us typ_def ] ->
      [ qeq T1 T2 :: Q; K; E | gc_raise gc |= t2 ~: T ] -> 
      [ Q; K; E | gc |= trm_use t1 T1 T2 t2 ~: T ] *)
  | typing_use : forall Q K E t1 T1 T2 x t2 T,
      tree_instance K x (tr_eq T1 T2) ->
      [ Q; K; E | gc_raise gc |= t1 ~: typ_fvar x ] ->
      [ (T1, T2) :: Q; K; E | gc_raise gc |= t2 ~: T ] -> 
      [ Q; K; E | gc |= trm_use t1 T1 T2 t2 ~: T ]
  | typing_eq : forall Q K E x k rs T,
      kenv_ok Q K ->
      env_ok Q K E ->
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
  | red_use : forall T T' t2,
      term t2 ->
      red (trm_use trm_eq T T' t2) t2
  | red_use_1 : forall t1 t1' T T' t2,
      term t2 ->
      red t1 t1' ->
      red (trm_use t1 T T' t2) (trm_use t1' T T' t2)
  | red_rigid_1 : forall t1 t1',
      red t1 t1' ->
      red (trm_rigid t1) (trm_rigid t1')
  | red_apply_ann_1 : forall T U t t',
      term t ->
      term t' ->
      red (trm_app (trm_ann t (tr_arrow T U)) t')
          (trm_ann (trm_app t (trm_ann t' T)) U)
  | red_apply_ann_2 : forall r t t',
      term (trm_abs t) ->
      term t' ->
      red (trm_app (trm_ann (trm_abs t) (tr_rvar r)) t')
        (trm_let (trm_ann t' (tr_rvar (rvar_attr r Cstr.arrow_dom)))
                 (trm_ann t (tr_rvar (rvar_attr r Cstr.arrow_cod))))
  | red_ann_1 : forall T t1 t1',
      red t1 t1' ->
      red (trm_ann t1 T) (trm_ann t1' T).
(*
  | red_ann_abs_1 : forall T U t1,
      term (trm_abs t1) ->
      red (trm_ann (trm_abs t1) (tr_arrow T U))
          (trm_abs (trm_let (trm_ann (trm_bvar 0) T)
                            (trm_ann t1 U)))
  | red_ann_abs_2 : forall r t1,
      term (trm_abs t1) ->
      red (trm_ann (trm_abs t1) (tr_rvar r))
          (trm_abs (trm_let
              (trm_ann (trm_bvar 0) (tr_rvar (rvar_attr r Cstr.arrow_dom)))
              (trm_ann t1 (tr_rvar (rvar_attr r Cstr.arrow_cod)))))
  | red_rigid_abs : forall t1,
      term (trm_abs t1) ->
      red (trm_rigid (trm_abs t1)) (trm_abs (trm_rigid t1))
  | red_rigid_apply : forall t1 t2,
      term t1 -> term t2 ->
      red (trm_rigid (trm_app t1 t2))
          (trm_app (trm_rigid t1) (trm_rigid t2)).
*)

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
