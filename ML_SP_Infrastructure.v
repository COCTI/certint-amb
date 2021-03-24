(***************************************************************************
* Preservation and Progress for mini-ML (CBV) - Infrastructure             *
* Arthur Chargueraud, March 2007, Coq v8.1                                 *
* Extension to structural polymorphism                                     *
* Jacques Garrigue, October 2007 - May 2008                                *
***************************************************************************)

Set Implicit Arguments.
Require Import Arith List Lia Metatheory ML_SP_Definitions.
Require Import ProofIrrelevance.

(* ====================================================================== *)
(** * The infrastructure needs to be parameterized over definitions *)

Module MkInfra(Cstr:CstrIntf)(Const:CstIntf).

Module Defs := MkDefs(Cstr)(Const).
Import Defs.

(* These tactics needs definitions *)

Ltac length_hyps :=
  instantiate_fail;
  repeat match goal with
  | H: fresh _ _ _ |- _ => puts (fresh_length _ _ _ H); clear H
  | H: types _ _ |- _ => puts (proj1 H); clear H
  | H: list_for_n _ _ _ |- _ => puts (proj1 H); clear H
  | H: list_forall2 _ _ _ |- _ => puts (list_forall2_length H); clear H
  | H: split _ = (_,_) |- _ => puts (split_length _ H); clear H
  end;
  repeat progress
    (simpl in *; unfold typ_fvars, kinds_open_vars, kinds_open in *;
      try rewrite map_length in *; try rewrite app_length in *).

Global Hint Extern 1 (_ = length _) => length_hyps; lia : core.
Global Hint Extern 1 (length _ = _) => length_hyps; lia : core.

Lemma dom_kinds_open_vars : forall Xs Ks,
  length Ks = length Xs ->
  dom (kinds_open_vars Ks Xs) = mkset Xs.
Proof.
  intros. unfold kinds_open_vars; rewrite* dom_combine.
Qed.

Ltac disjoint_simpls :=
  repeat match goal with
  | H: fresh _ _ _ |- _ =>
    let Hf := fresh "Hf" in poses Hf (fresh_disjoint _ _ H);
    let Hn := fresh "Hn" in poses Hn (fresh_length _ _ _ H); clear H
  | H: ok (_ & _) |- _ =>
    let Ho := fresh "Ho" in poses Ho (ok_disjoint _ _ H); clear H
  | H: kenv_ok (_ & _) |- _ =>
    let Hk := fresh "Hk" in poses Hk (ok_disjoint _ _ (proj1 H)); clear H
  | H: binds _ _ _ |- _ =>
    let Hb := fresh "Hb" in poses Hb (binds_dom H); clear H
  | H: get _ _ = None |- _ =>
    let Hn := fresh "Hn" in poses Hn (get_none_notin _ H); clear H
  | H: In _ _ |- _ =>
    let Hi := fresh "Hi" in poses Hi (in_mkset H); clear H
  | H: ~In _ _ |- _ =>
    let Hn := fresh "Hn" in poses Hn (notin_mkset _ H); clear H
  | x := ?y : env _ |- _ => subst x
  end.

Ltac disjoint_solve :=
  instantiate_fail;
  disjoint_simpls;
  fold kind in *; unfold env_fv in *;
  repeat progress
    (simpl dom in *; simpl fv_in in *; simpl typ_fv in *;
     try rewrite dom_concat in *; try rewrite fv_in_concat in *;
     try rewrite dom_map in *;
     try (rewrite dom_combine in * by (length_hyps; lia));
     try (rewrite dom_kinds_open_vars in * by (length_hyps; lia)));
  sets_solve.

Global Hint Extern 1 (_ \in _) => solve [disjoint_solve] : core.
Global Hint Extern 1 (_ << _) => solve [disjoint_solve] : core.
Global Hint Extern 1 (_ \notin _) => solve [disjoint_solve] : core.
Global Hint Extern 1 (disjoint _ _) => solve [disjoint_solve] : core.

Lemma disjoint_fresh : forall n L1 Xs L2,
  fresh L1 n Xs ->
  disjoint L2 (mkset Xs) ->
  fresh L2 n Xs.
Proof.
  induction n; destruct Xs; simpl; intros; auto; try discriminate.
  split2*.
Qed.

Ltac env_ok_hyps :=
  repeat match goal with
  | H: env_ok _ _ _ |- _ => destruct H
  end.

Ltac kenv_ok_hyps :=
  repeat match goal with
  | H: kenv_ok _ _ |- _ => destruct H as [? [? []]]
  end.

Ltac env_ok_solve :=
  env_ok_hyps; split; [ok_solve | env_prop_solve].

Ltac kenv_ok_solve :=
  kenv_ok_hyps; split4;
  [ok_solve | env_prop_solve | env_prop_solve | env_prop_solve].

Global Hint Extern 2 (env_ok _ _ _) => solve [env_ok_solve] : core.
Global Hint Extern 2 (kenv_ok _ _) => solve [kenv_ok_solve] : core.

(* ====================================================================== *)
(** * Additional Definitions used in the Proofs *)

(* ********************************************************************** *)
(** ** Free Variables *)

(** Computing free variables of a term. *)

Fixpoint trm_fv (t : trm) {struct t} : vars :=
  match t with
  | trm_bvar i    => {}
  | trm_fvar x    => {{x}}
  | trm_abs t1    => (trm_fv t1)
  | trm_let t1 t2 => (trm_fv t1) \u (trm_fv t2)
  | trm_app t1 t2 => (trm_fv t1) \u (trm_fv t2)
  | trm_cst c     => {}
  | trm_use t1 _ _ t2 => (trm_fv t1) \u (trm_fv t2)
  | trm_rigid t1  => (trm_fv t1)
  | trm_ann t1 _  => (trm_fv t1)
  | trm_eq        => {}
  end.

Fixpoint rvar_fv (r : rvar) : vars :=
  match r with
  | rvar_b _ => {}
  | rvar_f x => {{x}}
  | rvar_attr x _ => rvar_fv x
  end.

Fixpoint tree_fv (T : tree) : vars :=
  match T with
  (* | tr_bvar i   => {} *)
  | tr_arrow T1 T2
  | tr_eq T1 T2 => (tree_fv T1) \u (tree_fv T2)
  | tr_rvar r   => rvar_fv r
  end.

Definition qitem_fv (q : qitem) : vars :=
  match q with
  | qvar x    => {{x}}
  | qeq T1 T2 => (tree_fv T1) \u (tree_fv T2)
  end.

Fixpoint qenv_fv (Q : qenv) : vars :=
  match Q with
  | nil => {}
  | q :: Q' => (qitem_fv q) \u (qenv_fv Q')
  end.

Definition var_fv (x : var) : vars := {{x}}.

(* ********************************************************************** *)
(** ** Substitution for free names *)

Definition subs := Env.env var.

(** Substitution for names for types *)

Definition var_subst (S : subs) (X : var) :=
  match get X S with
  | None => X
  | Some Y => Y
  end.

Fixpoint typ_subst (S : subs) (T : typ) {struct T} : typ :=
  match T with
  | typ_bvar i => typ_bvar i
  | typ_fvar X => typ_fvar (var_subst S X)
  end.

(** Substitution for names for schemes. *)

Definition kind_subst S := kind_map (typ_subst S).

Definition sch_subst S M := 
  Sch (typ_subst S (sch_type M)) (List.map (kind_subst S) (sch_kinds M)).

Lemma kind_subst_none S rvs : kind_subst S (None, rvs) = (None, rvs).
Proof. now unfold kind_subst, kind_map. Qed.

(** Substitution for name in a term. *)

Fixpoint trm_subst (z : var) (u : trm) (t : trm) {struct t} : trm :=
  match t with
  | trm_bvar i    => trm_bvar i 
  | trm_fvar x    => if x == z then u else (trm_fvar x)
  | trm_abs t1    => trm_abs (trm_subst z u t1) 
  | trm_let t1 t2 => trm_let (trm_subst z u t1) (trm_subst z u t2) 
  | trm_app t1 t2 => trm_app (trm_subst z u t1) (trm_subst z u t2)
  | trm_cst c     => trm_cst c
  | trm_use t1 T1 T2 t2 => trm_use (trm_subst z u t1) T1 T2 (trm_subst z u t2)
  | trm_rigid t1  => trm_rigid (trm_subst z (trm_shift_rigid 0 u) t1)
  | trm_ann t1 T  => trm_ann (trm_subst z u t1) T
  | trm_eq        => trm_eq
  end.

Notation "[ z ~> u ] t" := (trm_subst z u t) (at level 68).


(* ====================================================================== *)
(** * Tactics *)

(* ********************************************************************** *)
(** ** Instanciation of Tactics *)

Ltac gather_vars :=
  let A := gather_vars_with (fun x : vars => x) in
  let B := gather_vars_with (fun x : var => {{ x }}) in
  let C := gather_vars_with (fun x : env => dom x) in
  let D := gather_vars_with (fun x : trm => trm_fv x) in
  let E := gather_vars_with (fun x : typ => typ_fv x) in
  let F := gather_vars_with (fun x : list typ => typ_fv_list x) in
  let G := gather_vars_with (fun x : env => env_fv x) in
  let H := gather_vars_with (fun x : sch => sch_fv x) in
  let I := gather_vars_with (fun x : kenv => dom x) in
  let J := gather_vars_with (fun x : kenv => fv_in kind_fv x) in
  let K := gather_vars_with (fun x : list kind => kind_fv_list x) in
  let L := gather_vars_with (fun x : qenv => qenv_fv x) in
  let N := gather_vars_with (fun x : subs => fv_in var_fv x) in
  let O := gather_vars_with (fun x : list var => mkset x) in
  constr:(A \u B \u C \u D \u E \u F \u G \u H \u I \u J \u K \u L \u N \u O).

Tactic Notation "pick_fresh" ident(x) :=
  let L := gather_vars in (pick_fresh_gen L x).

Tactic Notation "pick_freshes" constr(n) ident(x) :=
  let L := gather_vars in (pick_freshes_gen L n x).

Tactic Notation "apply_fresh" constr(T) "as" ident(x) :=
  apply_fresh_base T gather_vars x.

Tactic Notation "apply_fresh" "*" constr(T) "as" ident(x) :=
  apply_fresh T as x; auto*.


(* ********************************************************************** *)
(** ** Automation *)

Global Hint Constructors type term well_kinded : core.

Lemma typ_def_fresh : typ_fv typ_def = {}.
Proof.
  auto.
Qed.

Global Hint Extern 1 (_ \notin typ_fv typ_def) =>
  rewrite typ_def_fresh : core.

Global Hint Extern 1 (types _ _) => split; auto : core.


(* ====================================================================== *)
(** ** Properties of fv *)

Lemma typ_fv_typ_fvars Ys : typ_fv_list (typ_fvars Ys) = mkset Ys.
Proof. induction Ys; simpl*. rewrite* IHYs. Qed.

Lemma fv_in_combine_vars Xs Vs :
  length Vs = length Xs -> fv_in var_fv (combine Xs Vs) = mkset Vs.
Proof.
  revert Vs; induction Xs; destruct Vs; simpls*; intros; try discriminate.
  injection H; intros; rewrite* IHXs.
Qed.

Lemma in_typ_fv : forall t l,
  In t l -> typ_fv t << typ_fv_list l.
Proof.
  induction l; simpl; intros H x Hx. elim H.
  destruct* H.
  subst; simpl*.
Qed.

Lemma in_kind_fv : forall k Ks,
  In k Ks -> kind_fv k << kind_fv_list Ks.
Proof.
  induction Ks; simpl; intros; intros y Hy. elim H.
  destruct H. subst*.
  use (IHKs H _ Hy).
Qed.

Lemma typ_fv_open : forall Us T,
  typ_fv (typ_open T Us) << typ_fv T \u typ_fv_list Us.
Proof.
  induction T; simpl*.
  intros x Hx.
  gen n; induction Us; destruct n; simpl; intros; auto.
  use (IHUs n Hx).
Qed.

Lemma kind_fv_open : forall Us k,
  kind_fv (kind_open k Us) << kind_fv k \u typ_fv_list Us.
Proof.
  destruct k as [[[kc kv kr kh]|] rvs]; unfold kind_fv, kind_types; simpl*.
  rewrite list_snd_map_snd.
  clear; induction kr; simpl*.
  disjoint_solve.
  use (typ_fv_open _ _ H).
Qed.

Lemma fv_in_kinds_open_vars Ks Xs :
  fv_in kind_fv (kinds_open_vars Ks Xs) << kind_fv_list Ks \u mkset Xs.
Proof.
  unfold kinds_open_vars.
  intros.
  rewrite <- typ_fv_typ_fvars.
  set (Us := typ_fvars Xs); clearbody Us.
  gen Ks; induction Xs; destruct Ks; simpl*.
  sets_solve.
    use (kind_fv_open _ _ H).
  use (IHXs Ks _ H).
Qed.


(* ====================================================================== *)
(** ** Properties of kinds *)

Lemma kind_cstr_map f k : kind_cstr (ckind_map f k) = kind_cstr k.
Proof. now destruct k. Qed.

Lemma kind_rel_map f k : kind_rel (ckind_map f k) = map_snd f (kind_rel k).
Proof. now destruct k. Qed.

Lemma ckind_pi : forall k k',
  kind_cstr k = kind_cstr k' ->
  kind_rel k = kind_rel k' ->
  k = k'.
Proof.
  intros [kc kv kr kh] [kc' kv' kr' kh']; simpl; intros.
  subst.
  rewrite (proof_irrelevance _ kv kv').
  rewrite (proof_irrelevance _ kh kh').
  auto.
Qed.

Lemma kind_pi : forall k k',
  kind_cstr k = kind_cstr k' ->
  kind_rel k = kind_rel k' ->
  Some k = Some k'.
Proof. intros; rewrite* (ckind_pi k k'). Qed.

(* ====================================================================== *)
(** * Properties of terms *)

(* begin hide *)

(** Substitution on indices is identity on well-formed terms. *)

Lemma trm_open_rec_core :forall t j v i u, i <> j ->
  trm_open_rec j v t = trm_open_rec i u (trm_open_rec j v t) ->
  t = trm_open_rec i u t.
Proof.
  induction t; introv Neq Equ;
  simpl in *; inversion* Equ; f_equal*.  
  case_nat*. case_nat*. 
Qed.

Lemma trm_open_rec_term : forall t u,
  term t -> forall k, t = trm_open_rec k u t.
Proof.
  intros; revert u k; induction H; intros; simpl; f_equal*. 
  unfolds trm_open. pick_fresh x.
   apply* (@trm_open_rec_core t1 0 (trm_fvar x)).
  unfolds trm_open. pick_fresh x.
  apply* (@trm_open_rec_core t2 0 (trm_fvar x)).
Qed.

(* end hide *)

Lemma rvar_shift_comm k j r : k <= j ->
  rvar_shift k (rvar_shift j r) = rvar_shift (j + 1) (rvar_shift k r).
Proof.
  induction r; simpl; intros; try solve [f_equal*].
  repeat (destruct Compare_dec.le_lt_dec; simpl); auto; elimtype False; lia.
Qed.

Lemma tree_shift_rigid_comm k j t : k <= j ->
  tree_shift_rigid k (tree_shift_rigid j t) =
  tree_shift_rigid (j + 1) (tree_shift_rigid k t).
Proof.
  revert k j; induction t; simpls; intros; f_equal*.
  now apply rvar_shift_comm.
Qed.

Lemma trm_shift_rigid_comm k j t : k <= j ->
  trm_shift_rigid k (trm_shift_rigid j t) =
  trm_shift_rigid (j + 1) (trm_shift_rigid k t).
Proof.
revert k j; induction t; simpls; intros; auto; try solve [f_equal*].
- f_equal*; now apply tree_shift_rigid_comm.
- f_equal; auto with arith.
- f_equal*; now apply tree_shift_rigid_comm.
Qed.

Lemma rvar_open_shift n s r : rvar_open n s (rvar_shift n r) = r.
Proof.
  induction r; simpl; try congruence.
  destruct Compare_dec.le_lt_dec; simpl.
    case (n === n0 + 1); intros; subst. lia.
    destruct Compare_dec.le_lt_dec. f_equal; lia.
    lia.
  case (n === n0); intros; subst. lia.
  destruct* Compare_dec.le_lt_dec. lia.
Qed.

Lemma tree_rigid_shift n r t : tree_open_rigid n r (tree_shift_rigid n t) = t.
Proof. induction t; simpl; try congruence; rewrite* rvar_open_shift. Qed.
  
Lemma trm_rigid_shift n r u : trm_rigid_rec n r (trm_shift_rigid n u) = u.
Proof.
  revert n r; induction u; intros; simpls*; try congruence.
  - repeat rewrite tree_rigid_shift; congruence.
  - rewrite plus_comm; simpl; congruence.
  - rewrite tree_rigid_shift; congruence.
Qed.

Lemma trm_rigid_rec_subst_comm x n u t r :
  trm_subst x u (trm_rigid_rec n r t) =
  trm_rigid_rec n r (trm_subst x (trm_shift_rigid n u) t).
Proof.
  revert t n u r.
  induction t; simpl*; intros*; try congruence.
  + case (v == x); intros H; simpl*. rewrite* trm_rigid_shift.
  + rewrite IHt, (@trm_shift_rigid_comm 0), plus_comm; auto with arith.
Qed.

Lemma trm_open_rigid_subst_comm x u t r :
  trm_subst x u (trm_open_rigid t r) =
  trm_open_rigid (trm_subst x (trm_shift_rigid 0 u) t) r.
Proof.
  unfold trm_open_rigid.
  rewrite* trm_rigid_rec_subst_comm.
Qed.

(** Substitution for a fresh name is identity. *)

Lemma trm_subst_fresh : forall x t u, 
  x \notin trm_fv t ->  [x ~> u] t = t.
Proof.
  intros. revert u. induction t; intros; simpls; f_equal*.
  case_var*. notin_contradiction.
Qed.

(** Substitution distributes on the open operation. *)
Lemma trm_shift_rigid_open_var : forall t k j x,
  trm_shift_rigid k (trm_open_rec j (trm_fvar x) t) =
  trm_open_rec j (trm_fvar x) (trm_shift_rigid k t).
Proof.
  induction t; intros; simpls; f_equal*.
  case_nat*.
Qed.
  
Lemma term_trm_shift_rigid : forall k t, term t ->
  term (trm_shift_rigid k t).
Proof.
  intros; revert k. induction H; intros; simpls; f_equal*;
  econstructor; try auto; intros;
  unfolds trm_open; rewrite* <- trm_shift_rigid_open_var.
Qed.
Global Hint Resolve term_trm_shift_rigid : core.

Lemma trm_shift_rigid_open_rec : forall t k j u , term u ->
  trm_shift_rigid k (trm_open_rec j u t) =
  trm_open_rec j (trm_shift_rigid k u)
                 (trm_shift_rigid k t).
Proof.
  induction t; intros; simpls; f_equal*.
  case_nat*. rewrite* IHt. rewrite* <- trm_shift_rigid_comm; lia.
Qed.

Lemma trm_shift_rigid_subst : forall k x u t, term u ->
  trm_shift_rigid k ([x ~> u] t) = [x ~> trm_shift_rigid k u] (trm_shift_rigid k t).
Proof.
  intros. revert u k H. induction t; intros; simpls; f_equal*.
  case_var*. rewrite* trm_shift_rigid_comm; try lia. 
Qed.
  
Lemma trm_subst_open : forall x u t1 t2, term u -> 
  [x ~> u] (t1 ^^ t2) = ([x ~> u]t1) ^^ ([x ~> u]t2).
Proof.
  intros. revert u H t2. unfold trm_open. generalize 0.
  induction t1; intros; simpl; f_equal*.
  case_nat*. case_var*. apply* trm_open_rec_term.
  rewrite* IHt1. rewrite* trm_shift_rigid_subst.
Qed.

(** Substitution and open_var for distinct names commute. *)

Lemma trm_subst_open_var : forall x y u e, y <> x -> term u ->
  ([x ~> u]e) ^ y = [x ~> u] (e ^ y).
Proof.
  introv Neq Wu. rewrite* trm_subst_open.
  simpl. case_var*.
Qed.

(** Opening up an abstraction of body t with a term u is the same as opening
  up the abstraction with a fresh name x and then substituting u for x. *)

Lemma trm_subst_intro : forall x t u, 
  x \notin (trm_fv t) -> term u ->
  t ^^ u = [x ~> u](t ^ x).
Proof.
  introv Fr Wu. rewrite* trm_subst_open.
  rewrite* trm_subst_fresh. simpl. case_var*.
Qed.

(** Terms are stable by substitution *)

Lemma trm_subst_term : forall t z u,
  term u -> term t -> term ([z ~> u]t).
Proof.
  intros; revert u H. induction H0; intros; simpl*.
  case_var*.
  apply_fresh term_abs as y. rewrite* trm_subst_open_var.
  apply_fresh* term_let as y. rewrite* trm_subst_open_var.
Qed.

Global Hint Resolve trm_subst_term : core.

(** Conversion from locally closed abstractions and bodies *)

Lemma term_abs_to_body : forall t1, 
  term (trm_abs t1) -> term_body t1.
Proof.
  intros. unfold term_body. inversion* H.
Qed.

Lemma body_to_term_abs : forall t1, 
  term_body t1 -> term (trm_abs t1).
Proof.
  intros. inversion* H.
Qed.

Lemma term_let_to_body : forall t1 t2, 
  term (trm_let t1 t2) -> term_body t2.
Proof.
  intros. unfold term_body. inversion* H.
Qed.

Lemma body_to_term_let : forall t1 t2, 
  term_body t2 -> term t1 -> term (trm_let t1 t2).
Proof.
  intros. inversion* H.
Qed.

Global Hint Resolve body_to_term_abs body_to_term_let : core.

Global Hint Extern 1 (term_body ?t) =>
  match goal with 
  | H: context [trm_abs t] |- _ => 
    apply term_abs_to_body 
  | H: context [trm_let ?t1 t] |- _ => 
    apply (@term_let_to_body t1) 
  end : core.

(** ** Opening a body with a term gives a term *)

Lemma trm_open_term : forall t u,
  term_body t -> term u -> term (t ^^ u).
Proof.
  intros. destruct H. pick_fresh y. rewrite* (@trm_subst_intro y).
Qed.

Global Hint Resolve trm_open_term : core.


(* ====================================================================== *)
(** * Properties of types *)

(** Extract vars from types *)

Lemma vars_of_types n Us :
  types n Us -> exists Vs, length Vs = n /\ typ_fvars Vs = Us.
Proof.
  intros [Len FA].
  revert n Len; induction FA; destruct n; try discriminate; simpl; intros.
    exists* (@nil var).
  inversions Len.
  inversions H.
  destruct* (IHFA (length L)) as [Xs []].
  rewrite <- H0, <- H1.
  exists* (X :: Xs).
Qed.

(** Open on a type is the identity. *)

Lemma typ_open_type : forall T Us,
  type T -> T = typ_open T Us.
Proof.
  introv W. induction T; simpls; inversions W; f_equal*.
Qed.

(** Substitution for a fresh name is identity. *)

Lemma typ_subst_fresh : forall S T, 
  disjoint (dom S) (typ_fv T) ->
  typ_subst S T = T.
Proof.
  intros. induction T; simpls; f_equal*.
  unfold var_subst; rewrite* get_notin_dom.
Qed.

Lemma kind_subst_fresh : forall S k,
  disjoint (dom S) (kind_fv k) ->
  kind_subst S k = k.
Proof.
  unfold kind_subst, kind_fv, kind_types, kind_map, ckind_map.
  intros. destruct k as [[[kc kv kr kh]|] rvs]; simpl*. f_equal*.
  apply* kind_pi; simpl in *.
  clear -H; induction* kr; intros.
  destruct a; simpl.
  rewrite* IHkr.
    rewrite* typ_subst_fresh. simpl in H. auto.
  simpl in *. auto.
Qed.

Lemma typ_subst_fresh_list : forall S ts,
  disjoint (dom S) (typ_fv_list ts) ->
  ts = List.map (typ_subst S) ts.
Proof.
  induction ts; simpl; intros Fr.
  auto. f_equal*. rewrite~ typ_subst_fresh.
Qed.

Lemma typ_subst_fresh_trm_fvars : forall S xs,
  fresh (dom S) (length xs) xs ->
  typ_fvars xs = List.map (typ_subst S) (typ_fvars xs).
Proof.
  intros. apply typ_subst_fresh_list.
  induction xs; intro v; simpls. auto.
  destruct H.
  destruct (fresh_union_r _ _ _ _ H0).
  use (IHxs H1).
Qed.

(** Substitution distributes on the open operation. *)

Lemma typ_subst_open S T1 T2 :
  typ_subst S (typ_open T1 T2) = 
   typ_open (typ_subst S T1) (List.map (typ_subst S) T2).
Proof.
  induction T1; simpl; f_equal*.
  apply list_map_nth. apply* typ_subst_fresh.
Qed.

(** Substitution and open_var for distinct names commute. *)

Lemma typ_subst_open_vars S Ys T :
  fresh (dom S) (length Ys) Ys -> 
  typ_open_vars (typ_subst S T) Ys = typ_subst S (typ_open_vars T Ys).
Proof.
  intros Fr. unfold typ_open_vars.
  rewrite* typ_subst_open. f_equal.
  induction Ys; simpls. auto.
  destruct Fr.
  unfold var_subst; rewrite* get_notin_dom.
  rewrite* <- IHYs.
Qed.

Lemma kind_subst_open_vars S k Xs :
  fresh (dom S) (length Xs) Xs ->
  kind_subst S (kind_open k (typ_fvars Xs)) =
  kind_open (kind_subst S k) (typ_fvars Xs).
Proof.
  intros Fr.
  destruct* k as [[[kc kv kr kh]|] rvs]. 
  unfold kind_subst, kind_open, kind_map, ckind_map.
  simpl. f_equal*.
  apply* kind_pi; simpl.
  clear kh; induction* kr.
  simpl. fold (typ_open_vars (snd a) Xs).
  rewrite* <- typ_subst_open_vars.
  rewrite* IHkr.
Qed.

Lemma map_combine {A B : Set} (f : A->B) Xs Ys :
  map f (combine Xs Ys) = combine Xs (List.map f Ys).
Proof. revert Ys; induction Xs; destruct Ys; simpl*. rewrite* IHXs. Qed.

Lemma kinds_subst_open_vars S Ks Xs :
  fresh (dom S) (length Xs) Xs ->
  map (kind_subst S) (kinds_open_vars Ks Xs) =
  kinds_open_vars (List.map (kind_subst S) Ks) Xs.
Proof.
  unfold kinds_open_vars.
  intros Fr.
  rewrite map_combine.
  apply (f_equal (combine Xs (B:=kind))).
  unfold kinds_open.
  induction* Ks.
  simpls. rewrite IHKs.
  rewrite* kind_subst_open_vars.
Qed.

Lemma fresh_ok_combine {A:Set} K Xs (Vs : list A) :
  ok (K & combine Xs Vs) ->
  length Vs = length Xs -> fresh (dom K) (length Vs) Xs.
Proof.
  revert Vs; induction Xs; destruct Vs; simpl; intros; try discriminate; auto.
  inversions H.
  inversions H0.
  splits*.
  forward~ (IHXs Vs) as Fr.
  apply* disjoint_fresh.
Qed.

Lemma fresh_kinds_open_vars K Xs Ks :
  ok (K & kinds_open_vars Ks Xs) ->
  length Ks = length Xs -> fresh (dom K) (length Ks) Xs.
Proof.
  intros Ok Len.
  unfold kinds_open_vars, kinds_open in Ok.
  forward~ (fresh_ok_combine _ _ _ Ok).
  rewrite* map_length.
Qed.

(** Opening up an abstraction of body t with a term u is the same as opening
  up the abstraction with a fresh name x and then substituting u for x. *)

Lemma typ_subst_nil : forall T,
  typ_subst nil T = T.
Proof.
  induction T; simpl; auto.
Qed.

Lemma typ_subst_nth : forall S1 n S Xs Ys,
  fresh (dom S) (length Xs) Xs ->
  length Xs = length Ys ->
  typ_open_vars (typ_bvar n) Ys =
  typ_subst (S1 & combine Xs Ys & S) (typ_open_vars (typ_bvar n) Xs).
Proof.
  induction n; intros; destruct Xs; destruct Ys;
    rewrite concat_assoc; simpls; try discriminate; auto.
    assert (Bv: binds v v0 ((v, v0) :: combine Xs Ys)).
      unfold binds; simpl.
      destruct* (eq_var_dec v v).
    destruct H; assert (v # S) by auto.
    unfold var_subst.
    rewrite* (binds_prepend S1 (binds_concat_fresh S Bv H2)).
  destruct H.
  unfold typ_open_vars in *; simpl in *.
  rewrite* (IHn (S ++ (v,v0)::nil) Xs).
    fold (((v,v0)::nil) & S).
    repeat rewrite <- concat_assoc. simpl*.
  fold (((v,v0)::nil) & S).
  rewrite* dom_concat.
Qed.

Lemma typ_subst_intro0 : forall S Xs Ys T, 
  fresh (typ_fv T) (length Xs) Xs -> 
  length Xs = length Ys ->
  typ_open_vars (typ_subst S T) Ys =
  typ_subst (S & combine Xs Ys) (typ_open_vars T Xs).
Proof.
  induction T; simpls; intros.
      rewrite <- (concat_empty (combine Xs Ys)).
      rewrite <- concat_assoc.
      apply* typ_subst_nth.
    unfold var_subst.
    case_eq (get v S); intros.
      rewrite* (binds_concat_fresh (combine Xs Ys) H1).
    rewrite* get_notin_dom.
Qed.

Lemma typ_subst_intro : forall Xs Ys T, 
  fresh (typ_fv T) (length Xs) Xs -> 
  length Xs = length Ys ->
  typ_open_vars T Ys = typ_subst (combine Xs Ys) (typ_open_vars T Xs).
Proof.
  intros.
  rewrite (app_nil_end (combine Xs Ys)).
  fold (empty(A:=typ)).
  pattern T at 1.
  rewrite <- (typ_subst_fresh empty T).
    apply* (typ_subst_intro0 empty Xs Ys T H).
  simpl; intro; auto.
Qed.

(** Types are stable by type substitution *)

Lemma typ_subst_type : forall S T, type T -> type (typ_subst S T).
Proof. induction 1; simpl*. Qed.

Global Hint Resolve typ_subst_type : core.

(** List of types are stable by type substitution *)

Lemma typ_subst_type_list : forall S Ts n,
  types n Ts -> 
  types n (List.map (typ_subst S) Ts).
Proof.
  unfold types, list_for_n.
  induction Ts; destruct n; simpl; intros [EQ TT]. 
  auto. auto. inversion EQ.
  inversions TT. forward~ (IHTs n) as [K1 K2].
Qed.

(** ** Opening a body with a list of types gives a type *)

Lemma typ_open_types : forall Q K T Ys Ks,
  typ_body Q K T Ks ->
  length Ks = length Ys -> 
  type (typ_open_vars T Ys).
Proof.
  introv TB Len. pick_freshes (length Ks) Xs.
  rewrite* (@typ_subst_intro Xs).
  apply* typ_subst_type.
  destruct* (proj2 TB Xs).
Qed.


(* ====================================================================== *)
(** * Properties of schemes *)

(** Substitution for a fresh name is identity. *)

Lemma sch_subst_fresh : forall S M, 
  disjoint (dom S) (sch_fv M) -> 
  sch_subst S M = M.
Proof.
  intros. destruct M as [T K]. unfold sch_subst.
  unfold sch_fv in H; simpl in H.
  rewrite* typ_subst_fresh.
  simpl. apply (f_equal (Sch T)).
  induction* K.
  simpl in *; rewrite* IHK.
  rewrite* kind_subst_fresh.
Qed.

(** Trivial lemma to unfolding definition of [sch_subst] by rewriting. *)

Lemma sch_subst_fold : forall S T K,
  Sch (typ_subst S T) (List.map (kind_subst S) K) = sch_subst S (Sch T K).
Proof.
  auto.
Qed. 

(** Distributivity of type substitution on opening of scheme. *)

Lemma sch_subst_open S M Us :
  typ_subst S (sch_open M Us)
  = sch_open (sch_subst S M) (List.map (typ_subst S) Us).
Proof.
  unfold sch_open. destruct M. simpl.
  rewrite* <- typ_subst_open.
Qed.

(** Distributivity of type substitution on opening of scheme with variables. *)

Lemma sch_subst_open_vars S M Xs :
  fresh (dom S) (length Xs) Xs -> 
  typ_subst S (sch_open_vars M Xs) = sch_open_vars (sch_subst S M) Xs.
Proof.
  unfold sch_open_vars. intros. destruct M.
  rewrite* <- typ_subst_open_vars.
Qed.

(** Distributivity of type substitution on opening of kinds. *)

Lemma kind_subst_open S k Us :
  kind_subst S (kind_open k Us) =
  kind_open (kind_subst S k) (List.map (typ_subst S) Us).
Proof.
  intros.
  destruct* k as  [[[kc kv kr kh]|] rvs].
  unfold kind_subst, kind_open, kind_map, ckind_map. simpl; f_equal*.
  apply* kind_pi; simpl.
  clear kh; induction* kr.
  simpl. rewrite <- IHkr.
  rewrite* typ_subst_open.
Qed.

Lemma kinds_subst_open S Ks Us :
  List.map (kind_subst S) (kinds_open Ks Us) =
  kinds_open (List.map (kind_subst S) Ks) (List.map (typ_subst S) Us).
Proof.
  unfold kinds_open.
  induction* Ks.
  simpl; rewrite <- IHKs.
  rewrite* kind_subst_open.
Qed.

(** Properties of entailment. *)

Lemma entails_ckind_refl : forall k, entails_ckind k k.
Proof.
  intros. split2*.
Qed.
Global Hint Resolve entails_ckind_refl : core.

Lemma entails_refl : forall k, entails k k.
Proof.
  intros. destruct k as [[k'|] ?]; split2*; simpl*.
Qed.
Global Hint Resolve entails_refl : core.

Lemma entails_ckind_trans : forall k1 k2 k3,
  entails_ckind k1 k2 -> entails_ckind k2 k3 -> entails_ckind k1 k3.
Proof.
  intros.
  destruct H; destruct H0.
  split.
  apply* (Cstr.entails_trans H H0).
  intros; auto.
Qed.

Lemma entails_trans : forall k1 k2 k3,
  entails k1 k2 -> entails k2 k3 -> entails k1 k3.
Proof.
  intros.
  destruct k1 as [[k1'|] ?]; destruct k2 as [[k2'|] ?]; destruct k3 as [[k3'|] ?];
  destruct H; destruct H0; simpl in *; split; simpl*.
  apply (entails_ckind_trans H H0).
Qed.

Lemma ckind_subst_entails_ckind : forall S k k',
  entails_ckind k' k ->
  entails_ckind (ckind_map (typ_subst S) k') (ckind_map (typ_subst S) k).
Proof.
  intros.
  destruct H.
  destruct k as [kc kr]; destruct k' as [kc' kr'].
  split; simpl*.
  intros; simpl in *.
  destruct T.
  destruct (map_snd_inv _ _ _ _ H1) as [T' [e i]].
  rewrite <- e.
  apply* in_map_snd.
Qed.
Global Hint Resolve ckind_subst_entails_ckind : core.

Lemma kind_subst_entails : forall S k k',
  entails k' k ->
  entails (kind_map (typ_subst S) k') (kind_map (typ_subst S) k).
Proof.
  intros.
  destruct k as [[k|] ?]; destruct k' as [[k'|] ?]; inversion H; simpl in *;
  unfold kind_map; split; simpl*.
Qed.

(** Properties of well-kindedness *)

Global Hint Constructors wf_kind : core.

Lemma wf_kind_extend : forall K K' k,
  ok (K & K') -> wf_kind K k -> wf_kind (K & K') k.
Proof.
  intros.
  destruct* H0.
  apply* wf_attrs; intros. 
  destruct* (H0 l a) as [k1 [rvs1 []]].
Qed.
Global Hint Resolve wf_kind_extend : core.

Lemma entails_wf_kind K k k' : entails k k' -> wf_kind K k -> wf_kind K k'.    
Proof.
  intros Ekk' WF.
  destruct WF; destruct* k' as [[k'|] rvs]; try solve [cbv in Ekk'; auto*].
  constructor.
  intros.
  unfold entails,entails_ckind in Ekk'; simpl in Ekk'.
  destruct Ekk' as [[EnC EnR] EnRV].
  destruct* (H l a) as [? [? []]].
  apply (Cstr.entails_unique EnC H0).
Qed.

Lemma well_kinded_extend : forall K K' x T,
  ok (K & K') -> well_kinded K x T -> well_kinded (K & K') x T.
Proof. induction 2; auto*. Qed.
Global Hint Resolve well_kinded_extend : core.

Lemma wf_kind_comm : forall K K' K'' k,
  ok (K & K' & K'') -> wf_kind (K & K' & K'') k -> wf_kind (K & K'' & K') k.
Proof.
  introv Hok Hwf; inversions* Hwf.
  apply* wf_attrs; intros. 
  destruct* (H l a) as [k1 [rvs1 []]].
Qed.
Global Hint Resolve wf_kind_comm : core.

Lemma well_kinded_comm : forall K K' K'',
  ok (K & K' & K'') ->
  forall x T,
  well_kinded (K & K'' & K') x T ->
  well_kinded (K & K' & K'') x T.
Proof.
  introv OK; introv WK. gen_eq (K & K'' & K') as H. gen K''.
  induction WK; introv Ok EQ; subst.
  apply* (@wk_kind k').
  apply binds_comm; auto.
Qed.

Lemma well_kinded_weaken : forall K K' K'',
  ok (K & K' & K'') ->
  forall x T,
  well_kinded (K & K'') x T ->
  well_kinded (K & K' & K'') x T.
Proof.
  intros. apply* well_kinded_comm.
Qed.
Global Hint Resolve well_kinded_weaken : core.

(** Well substitutions *)

(* Need to define typ_subst first *)
Definition well_subst K K' S :=
  forall Z k,
    binds Z k K ->
    well_kinded K' (kind_subst S k) (typ_subst S (typ_fvar Z)).

Lemma well_kinded_subst: forall S K K' k T,
  well_subst K K' S ->
  well_kinded K k T ->
  well_kinded K' (kind_subst S k) (typ_subst S T).
Proof.
  intros.
  induction H0.
  generalize (H x _ H0); intro HW.
  inversions HW; clear HW.
  simpl.
  unfold var_subst in *.
  case_eq (get x S); introv Hget; rewrite Hget in H4.
    apply* wk_kind.
    refine (entails_trans H5 _).
    apply* kind_subst_entails.
  apply* wk_kind.
  refine (entails_trans H5 _).
  apply* kind_subst_entails.
Qed.
Global Hint Resolve well_kinded_subst : core.

(** Properties of instantiation and constants *)

Lemma trm_inst_nil : forall t, trm_inst t nil = t.
Proof.
  unfold trm_inst; intros.
  generalize 0; induction t; intros; simpl*;
    try solve [rewrite* IHt | rewrite IHt1; rewrite* IHt2].
  destruct* (Compare_dec.le_lt_dec n0 n).
  destruct* (n-n0).
Qed.

Lemma const_app_app : forall c l l',
  const_app c (l++l') = fold_left trm_app l' (const_app c l).
Proof.
  intros. unfold const_app. apply fold_left_app.
Qed.

Lemma trm_inst_app : forall c tl pl,
  trm_inst_rec 0 tl (const_app c pl) =
  const_app c (List.map (trm_inst_rec 0 tl) pl).
Proof.
  introv.
  rewrite <- (rev_involutive pl).
  induction (rev pl). simpl. auto.
  simpl in *.
  rewrite map_app.
  repeat rewrite const_app_app.
  simpl. congruence.
Qed.

Lemma const_app_inv : forall c pl,
  pl = nil \/
  exists t1, exists t2, const_app c pl = trm_app t1 t2.
Proof.
  intros.
  destruct* pl.
  right*.
  destruct* (exists_last (l:=t::pl)). intro; discriminate.
  destruct s. rewrite e.
  rewrite const_app_app. simpl.
  esplit; esplit; reflexivity.
Qed.
  
Lemma trm_inst_app_inv : forall c pl tl,
  pl = nil \/
  exists t1, exists t2,
    trm_inst (const_app c pl) tl = trm_app t1 t2.
Proof.
  intros.
  destruct* (const_app_inv c pl).
  right*.
  destruct H as [x1 [x2 e]].
  rewrite e.
  exists (trm_inst x1 tl).
  exists* (trm_inst x2 tl).
Qed.

Lemma const_app_eq : forall c1 vl1 c2 vl2,
  const_app c1 vl1 = const_app c2 vl2 -> c1 = c2 /\ vl1 = vl2.
Proof.
  intros.
  gen vl2.
  induction vl1 using rev_ind; intros.
    unfold const_app in H.
    destruct vl2 using rev_ind; simpl in H.
      inversions* H.
    rewrite fold_left_app in H. simpl in H. discriminate.
  destruct vl2 using rev_ind; repeat rewrite const_app_app in H.
    discriminate.
  inversions H; clear H.
  destruct (IHvl1 _ H1).
  subst*.
Qed.


(* Extra properties *)

Lemma All_kind_types_None : forall P rvs, All_kind_types P (None, rvs).
Proof.
  unfold All_kind_types, kind_types. simpl*.
Qed.

Global Hint Resolve All_kind_types_None : core.

Lemma All_kind_types_imp (P P' : typ -> Prop) k:
  (forall x, P x -> P' x) ->
  All_kind_types P k -> All_kind_types P' k.
Proof.
  intros.
  destruct* k as [[[kc kv kr kh]|] rvs].
  unfold All_kind_types, kind_types in *.
  simpl in *.
  clear -H H0; induction kr; simpl in *. auto.
  inversions* H0.
Qed.

Lemma All_kind_types_map : forall P f a,
  All_kind_types (fun x => P (f x)) a ->
  All_kind_types P (kind_map f a).
Proof.
  intros.
  destruct a as [[[kc kv kr kh]|] rvs].
    unfold All_kind_types, kind_map, ckind_map, kind_types in H |- *; simpl in *.
    rewrite list_snd_map_snd.
    apply* list_forall_map.
    simpl*.
  apply All_kind_types_None.
Qed.

Lemma All_kind_types_inv: forall P f a,
  All_kind_types P (kind_map f a) ->
  All_kind_types (fun x => P (f x)) a.
Proof.
  intros.
  destruct a as [[[kc kv kr kh]|] rvs]; simpl*.
    unfold All_kind_types, kind_map, ckind_map, kind_types in H |- *; simpl in *.
  clear kv kh; induction kr. simpl*.
  simpl in *. inversions* H.
Qed.

Lemma All_kind_types_subst : forall k S,
  All_kind_types type k ->
  All_kind_types type (kind_subst S k).
Proof.
  intros; unfold kind_subst; apply All_kind_types_map.
  apply* All_kind_types_imp.
Qed.

Global Hint Resolve All_kind_types_subst : core.

Lemma incr_subst_fresh : forall a t S Xs,
  fresh {{a}} (length Xs) Xs ->
  List.map (typ_subst ((a, t) :: S)) (typ_fvars Xs) =
  List.map (typ_subst S) (typ_fvars Xs).
Proof.
  induction Xs; simpl; intros. auto.
  unfold var_subst; simpl.
  destruct* (eq_var_dec a0 a).
    rewrite e in H. destruct* H. elim H. auto.
  rewrite* IHXs.
Qed.

Lemma fresh_subst : forall L Xs Vs,
  fresh L (length Vs) Xs ->
  List.map (typ_subst (combine Xs Vs)) (typ_fvars Xs) = List.map typ_fvar Vs.
Proof.
  induction Xs; destruct Vs; intros; try contradiction; simpl*.
  unfold var_subst; simpl in *.
  destruct* (eq_var_dec a a).
  rewrite incr_subst_fresh. rewrite* IHXs.
  destruct* H.
Qed.

Lemma kind_fv_fresh : forall k Ks n Xs,
  In k Ks ->
  fresh (kind_fv_list Ks) n Xs ->
  fresh (typ_fv_list (kind_types k)) n Xs.
Proof.
  induction Ks; intros. elim H.
  simpl in H; destruct H.
    rewrite H in H0; destruct (fresh_union_r _ _ _ _ H0).
    unfold kind_fv in H1. auto.
  apply* IHKs.
  simpls; auto*.
Qed.

Lemma typ_fvars_app : forall Xs Ys,
  typ_fvars (Xs++Ys) = typ_fvars Xs ++ typ_fvars Ys.
Proof.
  unfold typ_fvars; intros; apply map_app.
Qed.

Lemma types_typ_fvars : forall Xs,
  types (length Xs) (typ_fvars Xs).
Proof.
  unfold typ_fvars; intro; split.
    rewrite* map_length.
  induction Xs; simpl*.
Qed.
Global Hint Immediate types_typ_fvars : core.

(** Schemes are stable by type substitution. *)

Lemma typ_open_other_type : forall Us Vs T,
  type (typ_open T Us) ->
  types (length Us) Vs ->
  type (typ_open T Vs).
Proof.
  induction T; simpl; intros.
      destruct H0.
      gen Us Vs; induction n; destruct Us; destruct Vs;
        simpl in *; intros; try discriminate;
        inversion* H1.
    simpl*.
Qed.

Lemma typ_open_vars_type : forall Xs Ys T,
  type (typ_open_vars T Xs) ->
  length Ys = length Xs ->
  type (typ_open_vars T Ys).
Proof.
  intros.
  unfold typ_open_vars.
  apply (typ_open_other_type (typ_fvars Xs)). apply H.
  replace (length (typ_fvars Xs)) with (length Ys).
    apply types_typ_fvars.
  unfold typ_fvars. rewrite* map_length.
Qed.

Lemma type_open_vars_subst S T Xs :
  type (typ_open_vars T (List.map (var_subst S) Xs)) ->
  type (typ_open_vars (typ_subst S T) Xs).
Proof.
 destruct T; simpl in *; intros.
   apply* typ_open_vars_type.
 constructor.
Qed.

Lemma qcoherent_subst Q S k :
  qcoherent Q k -> qcoherent Q (kind_subst S k).
Proof.
  induction 1.
  - constructor. auto.
  - constructor; simpls*.
    now rewrite kind_cstr_map.
  - apply qc_eq; simpls*.
    now rewrite kind_cstr_map.
Qed.
    
Lemma map_id {A} l : List.map (@id A) l = l.
Proof. induction l; simpls; auto. rewrite* IHl. Qed.

Lemma var_subst_fresh S x : x # S -> var_subst S x = x.
Proof. intros; unfold var_subst; rewrite* get_notin_dom. Qed.

Lemma wf_kind_open_subst  K K' S Ks Xs L :
  well_subst K K' S ->
  fresh (L \u dom K' \u dom S) (length Ks) Xs ->
  list_forall (wf_kind (K & kinds_open_vars Ks Xs))
              (List.map (fun k => kind_open k (typ_fvars Xs)) Ks) ->
  list_forall (wf_kind (K' & kinds_open_vars (List.map (kind_subst S) Ks) Xs))
              (List.map (fun k => kind_open(kind_subst S k)(typ_fvars Xs)) Ks).
Proof.
  intros WS Fr WF.
  apply list_forall_in; intros k Hk.
  destruct (proj1 (in_map_iff _ _ _) Hk) as [k' [Hko Hk']].
  forward~ (list_forall_out WF (kind_open k' (typ_fvars Xs))) as WFk'; clear WF.
    refine (in_map _ _ _ Hk').
  destruct* k as [[k|] rvs].
  destruct k' as [[k'|] rvs']; try discriminate.
  inversions Hko; clear Hko.
  constructor; introv.
  repeat rewrite kind_cstr_map, kind_rel_map.
  unfold map_snd; rewrite map_map; simpl.
  fold (map_snd (fun T => typ_open(typ_subst S T)(typ_fvars Xs)) (kind_rel k')).
  intros HU Hl.
  assert (Ha': exists T', exists a',
               In (l, T') (kind_rel k')
               /\ typ_open_vars T' Xs = typ_fvar a'
               /\ typ_subst S (typ_fvar a') = typ_fvar a).
    destruct (proj1 (in_map_iff _ _ _) Hl) as [[l' T'] [Hkl Hkl']].
    simpl in Hkl; inversions Hkl; clear Hkl.
    assert (HT' := typ_subst_open_vars S Xs T').
    forward~ HT' as HT''; clear HT'.
    unfold typ_open_vars in HT''; rewrite HT'' in *.
    revert H1.
    case_eq (typ_open T' (typ_fvars Xs)); introv HOT'; try discriminate.
    intros _.
    exists T'; exists v.
    splits*.
  destruct Ha' as [T' [a' [HlT' [Ha' Haa']]]].
  inversions WFk'; clear WFk'.
  forward~ (H1 l a') as [k'' [rvs'' [B FA]]]; clear H1.
      now rewrite kind_cstr_map.
    rewrite kind_rel_map.
    rewrite <- Ha'.
    unfold typ_open_vars, map_snd.
    now apply(in_map (fun p =>(fst p, typ_open(snd p)(typ_fvars Xs))) _ (l,T')).
  binds_cases B.
    assert (WK := WS _ _ B0).
    inversions WK.
    simpl in Haa'; inversions Haa'; clear Haa'.
    destruct k'0 as [k'0 rvs'0].
    exists k'0; exists rvs'0.
    splits*.
    intros rv Hrv.
    (*destruct (FA _ Hrv) as [rv' [Hrv' Hpf]].
    exists rv'; splits*.*)
    destruct H1 as [_ EnRV].
    apply* EnRV.
  exists (fst (kind_subst S (k'',rvs''))); exists rvs''.
  assert (Ha'Xs : a' \in mkset Xs).
    puts (binds_dom B1).
    now rewrite dom_kinds_open_vars in H by auto.
  rewrite typ_subst_fresh in Haa' by auto.
  inversions Haa'.
  split.
    apply binds_prepend.
    rewrite <- kinds_subst_open_vars by auto.
    apply* (@binds_map _ _ a (k'',rvs'') (kind_subst S)).
  intros.
  apply* FA.
Qed.

Lemma vars_subst_fresh S n Xs :
  fresh (dom S) n Xs -> List.map (var_subst S) Xs = Xs.
Proof.
  intros Fr.
  rewrite <- (map_ext_in id); intros.
    now rewrite map_id.
  pose (in_mkset _ _ H).
  rewrite* var_subst_fresh.
Qed.

Lemma sch_subst_type Q K K' S M :
  well_subst K K' S ->
  scheme Q K M -> scheme Q K' (sch_subst S M).
Proof.
  destruct M as [T Ks].
  unfold scheme; simpls; intros WS [QC SC].
  split.
    apply* list_forall_map.
    intros k Hk Qk.
    apply* qcoherent_subst.
  introv Len.
  destruct (SC (List.map (var_subst S) Xs)) as [TP [KT [L WF]]].
    now rewrite map_length in *.
  splits.
  - apply* type_open_vars_subst.
  - refine (list_forall_map _ _ _ KT).
    intros x Hx AKx.
    apply All_kind_types_map.
    revert AKx.
    apply All_kind_types_imp.
    intros U HU.
    apply* type_open_vars_subst.
  - unfold kinds_open in *.
    rewrite map_length in *.
    exists (L \u dom K' \u dom S).
    intros Fr.
    rewrite (vars_subst_fresh S (length Ks) Xs) in * by auto.
    forward~ WF as WF'; clear WF.
    rewrite map_map.
    apply* wf_kind_open_subst.
Qed.

Global Hint Resolve sch_subst_type : core.

(** Scheme arity is preserved by type substitution. *)

Lemma sch_subst_arity : forall S M, 
  sch_arity (sch_subst S M) = sch_arity M.
Proof.
  intros. simpl; rewrite* map_length.
Qed.

(** ** Opening a scheme with a list of types gives a type *)

Lemma sch_open_types : forall Q K M Us,
  scheme Q K M ->
  types (sch_arity M) Us ->
  type (sch_open M Us).
Proof. 
  unfold scheme, sch_open. intros Q K [T Ks] Us WB [Ar TU].
  simpls.
  destruct (var_freshes {} (length Ks)) as [Xs HXs].
  apply (typ_open_other_type (List.map typ_fvar Xs)).
    apply* typ_open_types.
  splits*.
Qed.

Global Hint Resolve sch_open_types : core.

Definition kenv_ok_is_ok Q K (H : kenv_ok Q K) : ok K := proj1 H.
Definition env_ok_is_ok Q K E (H:env_ok Q K E) := proj1 H.
Definition kenv_ok_type Q K (H : kenv_ok Q K) := proj32 H.
Definition kenv_ok_qcoherent Q K (H : kenv_ok Q K) := proj43 H.
Definition kenv_ok_wf_kind Q K (H : kenv_ok Q K) := proj44 H.
Definition env_ok_scheme Q K E (H:env_ok Q K E) := proj2 H.

Global Hint Immediate kenv_ok_is_ok env_ok_is_ok kenv_ok_type kenv_ok_qcoherent : core.
Global Hint Immediate kenv_ok_wf_kind env_ok_scheme : core.

Ltac env_hyps T :=
  match T with
  | sch => env_ok_hyps
  | kind => kenv_ok_hyps
  end.

Global Hint Extern 2 (@env_prop ?T _ ?E) =>
  progress env_hyps T; solve [env_prop_solve] : core.

Global Hint Extern 2 (@ok ?T ?E) =>
  progress env_hyps T; solve [ok_solve] : core.

Lemma env_prop_binds : forall (A:Set) (P:A->Prop) x (a:A) E,
  binds x a E -> env_prop P E -> P a.
Proof.
  intros. apply* (H0 x).
Qed.

(* ====================================================================== *)
(** * Properties of judgments *)

Module MkJudgInfra(Delta:DeltaIntf).
Module Judge := MkJudge(Delta).
Import Judge.
Global Hint Constructors typing valu red : core.

(* ********************************************************************** *)
(** ** Regularity of relations *)

(** A typing relation is restricted to well-formed objects. *)
Lemma graph_of_tree_n m T :
  let '(n, Ks) := graph_of_tree m T in
  n < length Ks + m.
Proof.
  revert m. induction T; intros; simpl*.
  case_eq (graph_of_tree (m + 1) T1); intros.
  case_eq (graph_of_tree (m + length l + 1) T2); intros.
  simpl*. lia.
  case_eq (graph_of_tree (m + 1) T1); intros.
  case_eq (graph_of_tree (m + length l + 1) T2); intros.
  simpl*. lia.
Qed.
  
Lemma graph_of_tree_type_n T :
  let '(n, Ks) := graph_of_tree_type T in
  n < length Ks.
Proof.
  unfold graph_of_tree_type.
  case_eq (graph_of_tree 0 T); intros.
  generalize (graph_of_tree_n 0 T).
  rewrite H. lia.
Qed.

Lemma qsat_remove_qvar x Q Ts :
   qsat Q Ts -> qsat (qvar x :: Q) Ts.
Proof.
  unfold qsat. assert (qsat_item Ts (qvar x)) by constructor.
  auto*.
Qed.
Global Hint Resolve qsat_remove_qvar : core.

Lemma qcoherent_remove_qvar x Q k :
  qcoherent (qvar x :: Q) k -> qcoherent Q k.
Proof.
  remember (qvar x :: Q) as Q'.
  induction 1; subst Q'; solve [constructor; auto*].
Qed.

Lemma qsat_add_item Q q Q' S : qsat (Q ++ q :: Q') S -> qsat (Q ++ Q') S.
Proof. induction Q; simpl; intros; inversions* H; constructor; auto*. Qed.

Lemma qcoherent_add_qitem Q q Q' k :
  qcoherent (Q ++ Q') k -> qcoherent (Q ++ q :: Q') k.
Proof.
  intros QC; gen_eq (Q ++ Q') as Q0; gen Q.
  induction QC; intros; subst;
  constructor; auto; introv QS; apply qsat_add_item in QS; auto*.
Qed.
Global Hint Resolve qcoherent_add_qitem : core.

Lemma tree_eq_of_instance Q K x T1 T2 S :
  tree_instance K x T1 -> tree_instance K x T2 -> kenv_ok Q K ->
  qsat Q S -> tree_subst_eq S T1 T2.
Abort.

Lemma rvar_shift_open n m r r0 : m <= n ->
                                 rvar_shift m (rvar_open n r r0) =
                                 rvar_open (S n) (rvar_shift m r) (rvar_shift m r0).
Proof.
  intros; induction r0; simpl*.
  case (n === n0).
  + intros; subst. case le_lt_dec; try lia; intros. rewrite plus_comm. simpl.
    case (n0 === n0); try lia. auto.
  + intros; simpl*; repeat (case le_lt_dec in *; intros; try lia).
    * assert (n0 = n0 - 1 + 1) by lia. rewrite <- H0.
      rewrite plus_comm; simpl*.
      case (n === n0); try lia.
      case le_lt_dec; try lia; simpl*.
      rewrite* <- minus_n_O.
    * simpl*. 
      assert (n0 + 1 = S n0) by lia.
      rewrite* H0. destruct (n === n0); auto*.
      destruct (le_lt_dec n n0); simpl*; try lia.
    * simpl*. destruct n0; auto*.
      case (n === n0); try lia. intros.
      destruct le_lt_dec; try lia; simpl*.
  + rewrite* IHr0. 
Qed.

Lemma tree_open_rigid_shift_rigid n m r T : m <= n ->
        tree_shift_rigid m (tree_open_rigid n r T) =
        tree_open_rigid (S n) (rvar_shift m r) (tree_shift_rigid m T).
Proof.
  induction T; simpl*; intros; try now rewrite IHT1, IHT2.
  rewrite* rvar_shift_open. 
Qed.

Lemma trm_shift_rigid_rec n m r u : m <= n ->
     trm_shift_rigid m (trm_rigid_rec n r u) =
     trm_rigid_rec (S n) (rvar_shift m r) (trm_shift_rigid m u).
Proof.
  revert n m r. induction u; simpl*; intros;
    try now (rewrite IHu || rewrite IHu1, IHu2).
  + rewrite* IHu1; rewrite* IHu2.
    repeat rewrite tree_open_rigid_shift_rigid; auto with arith.
  + rewrite IHu; try lia. rewrite* <- rvar_shift_comm. lia.
  + rewrite IHu, tree_open_rigid_shift_rigid; auto*.
Qed.

Lemma trm_rigid_rec_open n r t u :
  trm_rigid_rec n r (t ^^ u) = trm_rigid_rec n r t ^^ trm_rigid_rec n r u.
Proof.
  unfold trm_open.
  generalize 0.
  revert n u r; induction t; simpl*; intros;
    try now (rewrite IHt || rewrite IHt1, IHt2).
    case (n1 === n); auto*.
  f_equal. rewrite IHt.
  rewrite* trm_shift_rigid_rec.
  lia.
Qed.                               
      
Lemma trm_rigid_rec_open_shift n r t u :
  trm_rigid_rec n r t ^^ u = trm_rigid_rec n r (t ^^ (trm_shift_rigid n u)).
Proof.
  unfold trm_open.
  generalize 0.
  revert n u r; induction t; simpl*; intros;
    try now (rewrite IHt || rewrite IHt1, IHt2).
    case (n1 === n); auto*.
    intro; subst. rewrite* trm_rigid_shift.
  f_equal. rewrite IHt. rewrite* (@trm_shift_rigid_comm 0).
  rewrite* plus_comm. auto with arith.
Qed.

Lemma trm_rigid_rec_open_var n r t x :
  trm_rigid_rec n r t ^ x = trm_rigid_rec n r (t ^ x).
Proof.
  apply* (trm_rigid_rec_open_shift n r t (trm_fvar x)).
Qed.

(* This could not be right, so the next lemma must not be right...*)
(* Lemma rvar_open_shift n u r : rvar_open (S n) (rvar_shift 0 u) r = r.
Proof.
  revert n u.
  induction r; intros; simpl*.
  + destruct n; auto*.
    case (n0 === n); simpl*; intros. admit.
    destruct le_lt_dec; simpl*. admit.
  + rewrite* IHr.
Admitted.

Lemma tree_open_rigid_rvar_shift n r T :
  tree_open_rigid (S n) (rvar_shift 0 r) T = T.
Proof.
  About tree_open_rigid_shift_rigid.
  revert n r.
  induction T; intros; simpl*.
  + rewrite IHT1, IHT2. auto*.
  + rewrite IHT1, IHT2. auto*.
  + f_equal.
Admitted. *)

Lemma term_rigid_of_open n t r :
  term (trm_rigid_rec n r t) -> term t.
Proof.
  remember (trm_rigid_rec n r t) as t'. 
  intros Term; revert n r t Heqt'.
  induction Term; destruct t; simpl*; intros; try discriminate;
    inversions Heqt'; econstructor; intros; auto*; clear Heqt'.
  - specialize (H _ H1).
    apply (H0 _ H1 n r).
    apply trm_rigid_rec_open_var.
  - apply (H0 _ H1 n r).
    apply trm_rigid_rec_open_var.
Qed.

Lemma term_rigid_rec n r t :
  term t -> term (trm_rigid_rec n r t).
Proof.
  intros Term; revert n r.
  induction Term; simpl*; intros.
  - apply (@term_abs L); intros.
    rewrite* trm_rigid_rec_open_var.
  - apply* (@term_let L); intros.
    rewrite* trm_rigid_rec_open_var.
Qed.

Lemma wf_kind_weaken K K' K'' k :
  ok (K & K' & K'') -> wf_kind (K & K'') k -> wf_kind (K & K' & K'') k.
Proof.
  remember (K & K'') as K0.
  intros Ok WF.
  revert HeqK0.
  induction WF; simpl*; intros.
  subst; constructor; intros.
  destruct (H _ _ H0 H1) as [k [rvs [B]]].
  exists k; exists rvs.
  splits*.
  binds_cases B; auto*.
Qed.

Global Hint Resolve wf_kind_weaken : core.

Lemma wf_kind_strengthen K K' x k :
  disjoint (fv_in kind_fv K) (dom K') ->
  In (x, k) K -> wf_kind (K & K') k -> wf_kind K k.
Proof.
  intros Dis B Wf.
  inversions Wf.
    constructor.
  constructor; intros.
  destruct (H l a H0 H1) as [k [rvs [B1 Hrvs]]].
  exists k; exists rvs; splits*.
  binds_cases B1; auto.
  elim (binds_fresh B2).
  assert (Ha' : a \in fv_in kind_fv K).
    apply (fv_in_spec kind_fv K _ _ B).
    unfold kind_fv, kind_types; simpl.
    revert H1; clear.
    induction (kind_rel ck); simpl*; intros.
    destruct H1; subst; simpl*.
  auto.
Qed.

Lemma kenv_ok_strengthen Q K K' :
  disjoint (fv_in kind_fv K) (dom K') ->
  kenv_ok Q (K & K') ->
  kenv_ok Q K.
Proof.
  intros Fr Kok.
  splits*.
  destruct Kok as [_ []].
  intros x k Hx.
  apply* wf_kind_strengthen.
Qed.

Lemma scheme_strengthen_kinds Q K K' M :
  disjoint (dom K') (sch_fv M) ->
  scheme Q (K & K') M -> scheme Q K M.
Proof.
  intros Dis [].
  split; auto.
  intros Xs Len.
  destruct (H0 _ Len) as [? [? [L ?]]]; clear H0.
  splits*.
  exists (L \u dom K'); intros.
  forward~ H3 as FA; clear H3.
  apply list_forall_in; intros k B.
  assert (WF := list_forall_out FA k B).
  inversions* WF.
  constructor; intros.
  destruct* (H3 _ _ H4 H5) as [k [rvs [Ba RV]]]; clear H2 H3 H4.
  exists k; exists rvs; splits*.
  binds_cases Ba; auto.
  elimtype False.
  unfold kinds_open in B.
  destruct (proj1 (in_map_iff _ _ _) B) as [k' [Hko Hk']].
  assert (Ha : a \in kind_fv (Some ck, r)).
    unfold kind_fv, kind_types; simpl.
    assert (Ha := in_map snd _ _ H5).
    simpl in Ha.
    apply in_typ_fv in Ha.
    apply Ha; simpl*.
  rewrite <- (f_equal kind_fv Hko) in Ha.
  apply kind_fv_open in Ha.
  apply S.union_1 in Ha.
  destruct Ha as [Ha|Ha].
    apply in_kind_fv in Hk'.
    apply Hk' in Ha.
    apply (S.union_3 (typ_fv (sch_type M))) in Ha.
    fold (sch_fv M) in Ha.
    auto.
  rewrite typ_fv_typ_fvars in Ha.
  auto.
Qed.

Lemma env_ok_strengthen_kinds Q K K' E :
  disjoint (dom K') (fv_in sch_fv E) ->
  env_ok Q (K & K') E -> env_ok Q K E.
Proof.
  intros Dis []; split; auto; intros x M B.
  apply* scheme_strengthen_kinds.
  use (fv_in_spec sch_fv E _ _ B).
Qed.
  
Lemma typing_regular : forall gc Q K E e T,
  typing gc Q K E e T -> kenv_ok Q K /\ env_ok Q K E /\ term e /\ type T.
Proof.
introv H.
induction* H; try (pick_freshes (length Ks) Xs; forward~ (H1 Xs)); split4*.
  (* typing_var *)
- assert (scheme Q K M) by apply* env_prop_binds.
  pick_fresh y. destruct* H2.
  (* typing_abs *)
- pick_fresh y. apply* (H5 y).
- pick_fresh y. destruct* (H5 y) as [_ [[] _]].
- apply (@term_abs L); intros y Hy. destruct* (H5 y) as [_ [_ [HT _]]].
  (* typing_let *)
- pick_fresh y. apply* (H2 y).
- pick_fresh y. destruct* (H2 y) as [_ [[] _]].
- apply_fresh* term_let as y.
    pick_freshes (sch_arity M) Xs.
    forward~ (H0 Xs) as [_ [_ []]].
  forward~ (H2 y) as [_ [_ []]].
- pick_fresh y. forward~ (H2 y) as [_ [_ []]].
  (* typing_app *)
- destruct IHtyping1 as [[OkK [TK QK]] _].
  specialize (env_prop_binds H TK).
  unfold All_kind_types; simpl.
  intros HL.
  apply (list_forall_out HL T).
  apply* (in_map snd (kind_rel k) _ H2).
  (* typing_cst *)
- destruct H1. use (Delta.scheme c).
  (* typing_gc *)
- apply* kenv_ok_strengthen.
  rewrite* dom_kinds_open_vars.
- destruct (var_freshes (L \u fv_in sch_fv E) (length Ks)) as [Ys FrY].
  destruct* (H1 Ys) as [_ [? _]].
  apply* env_ok_strengthen_kinds.
  rewrite* dom_kinds_open_vars.
  (* typing_rigid *)
- pick_freshes (1 + length Us) Xs.
  destruct Xs as [|R Xs]; try contradiction.
  destruct* (H3 R Xs).
  constructor.
  apply* term_rigid_of_open.
- pick_freshes (1 + length Us) Xs.
  destruct Xs as [|R Xs]; try contradiction.
  destruct* (H3 R Xs) as [_ [_ []]].
  apply* typ_open_other_type.
  generalize (fresh_length _ _ _ Fr); simpl; intro Hlen.
  injection Hlen; intro Hlen'.
  unfold typ_fvars.
  rewrite map_length, <- Hlen'.
  splits*.
  destruct* H1 as [[] _].
Qed.

(** The value predicate only holds on locally-closed terms. *)

Lemma value_regular : forall e,
  value e -> term e.
Proof.
  intros. destruct H. induction H; auto.
Qed.

Global Hint Resolve value_regular : core.

(** A reduction relation only holds on pairs of locally-closed terms. *)

Lemma red_regular : forall e e',
  red e e' -> term e /\ term e'.
Proof.
  induction 1; auto*.
  - split.
      destruct vl.
      clear H; unfold const_app.
      assert (term (trm_cst c)) by auto.
      revert H; generalize (trm_cst c); induction H0; simpl*.
    apply* Delta.term.
  - splits*.
    inversions H.
    econstructor; unfold trm_open; simpl*.
  - splits*.
    inversions H.
    econstructor; unfold trm_open; simpl*.
Qed.

(* ********************************************************************** *)
(** ** Automation *)

(** Automation for reasoning on well-formedness. *)

Ltac kenv_ok_hyps ::=
  repeat match goal with
  | H: typing _ _ _ _ _ _ |- _ =>
    destruct (proj41 (typing_regular H)) as [? [? []]]; clear H
  | H: kenv_ok ?Q ?K |- _ => destruct H as [? [? []]]
  end.

Ltac env_ok_hyps ::=
  repeat match goal with
  | H: typing _ _ _ _ _ _ |- _ => destruct (proj42 (typing_regular H)); clear H
  | H: env_ok ?Q ?K ?E |- _ => destruct H
  end.

Global Hint Extern 1 (term ?t) =>
  match goal with
  | H: typing _ _ _ _ t _ |- _ => apply (proj43 (typing_regular H))
  | H: red t _ |- _ => apply (proj1 (red_regular H))
  | H: red _ t |- _ => apply (proj2 (red_regular H))
  | H: value t |- _ => apply (value_regular H)
  end : core.

Global Hint Extern 1 (type ?T) => match goal with
  | H: typing _ _ _ _ _ T |- _ => apply (proj44 (typing_regular H))
  end : core.

End MkJudgInfra.

End MkInfra.
