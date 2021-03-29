(***************************************************************************
* Preservation and Progress for mini-ML (CBV) - Graph handling             *
* Jacques Garrigue, 2021                                                   *
***************************************************************************)

Set Implicit Arguments.
Require Import Arith List Lia.
Require Import Metatheory ML_SP_Definitions ML_SP_Infrastructure.

Module MkGraph(Cstr:CstrIntf)(Const:CstIntf).

Module Infra := MkInfra(Cstr)(Const).
Import Infra Defs.

(* Definitions *)

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
  | tr_stuck t1 _ =>
    graph_of_tree ofs t1
  end.

Definition graph_of_tree_type S := graph_of_tree 0 S.

Definition annotation_tree (S : tree) := tr_arrow S S.

(*
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
*)

(*
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
*)

Eval compute in
  graph_of_tree_type (
  annotation_tree (tr_arrow (tr_rvar (rvar_b 0)) (tr_rvar (rvar_b 1)))).

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

(** Check if there are free rigid variables *)
Fixpoint rclosed_rvar (r : rvar) : Prop :=
  match r with
  | rvar_b _ => False
  | rvar_f _ => True
  | rvar_attr l a => rclosed_rvar l
  end.

Fixpoint rclosed_tree (T : tree) : Prop :=
  match T with
  | tr_arrow T1 T2 | tr_eq T1 T2 => rclosed_tree T1 /\ rclosed_tree T2
  | tr_rvar r => rclosed_rvar r
  | tr_stuck T1 a => rclosed_tree T1
  end.

Fixpoint rclosed (t : trm) : Prop :=
  match t with
  | trm_eq | trm_bvar _ | trm_fvar _ | trm_cst _ => True
  | trm_abs t' => rclosed t'
  | trm_let t1 t2 | trm_app t1 t2 => rclosed t1 /\ rclosed t2
  | trm_use t1 T1 T2 t2 =>
    rclosed t1 /\ rclosed t2 /\
    rclosed_tree T1 /\ rclosed_tree T2
  | trm_rigid t => rclosed t
  | trm_ann t T => rclosed t /\ rclosed_tree T
  end.

(* Infrastructure *)

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
  apply IHT.
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

(* Soundness *)

Lemma graph_of_tree_subst ofs tr S :
  let Ks := snd (graph_of_tree ofs tr) in
  List.map (kind_subst S) Ks = Ks.
Proof.
  revert ofs; induction tr; simpl; intros; auto.
  - specialize (IHtr1 (ofs+1)); revert IHtr1.
    case_eq (graph_of_tree (ofs + 1) tr1); simpl; introv Htr1 IHtr1.
    specialize (IHtr2 (ofs+length l+1)); revert IHtr2.
    case_eq (graph_of_tree (ofs + length l + 1) tr2); simpl; introv Htr2 IHtr2.
    rewrite map_app, IHtr1, IHtr2.
    unfold kind_subst, kind_map.
    f_equal.
    f_equal.
    now apply kind_pi.
  - specialize (IHtr1 (ofs+1)); revert IHtr1.
    case_eq (graph_of_tree (ofs + 1) tr1); simpl; introv Htr1 IHtr1.
    specialize (IHtr2 (ofs+length l+1)); revert IHtr2.
    case_eq (graph_of_tree (ofs + length l + 1) tr2); simpl; introv Htr2 IHtr2.
    rewrite map_app, IHtr1, IHtr2.
    unfold kind_subst, kind_map.
    f_equal.
    f_equal.
    now apply kind_pi.
Qed.

Lemma graph_of_tree_type_subst n Ks tr S :
  graph_of_tree_type tr = (n, Ks) ->
  List.map (kind_subst S) Ks = Ks.
Proof.
  unfold graph_of_tree_type.
  case_eq (graph_of_tree 0 tr); introv HK E.
  injection E; intros; subst.
  generalize (graph_of_tree_subst 0 tr S); simpl.
  now rewrite HK.
Qed.

(*
Lemma graph_of_kinds_subst ofs TKs S :
  let (Ks, Ks') := graph_of_kinds ofs TKs in
  List.map (kind_subst S) Ks = Ks /\ List.map (kind_subst S) Ks' = Ks'.
Proof.
  revert ofs.
  induction TKs; simpl; intros; auto.
  destruct a as [[[]|] rvs].
    set (ofs' := ofs + _).
    specialize (IHTKs ofs'); revert IHTKs.
    case_eq (graph_of_kinds ofs' TKs); introv HG; intros [E1 E2].
    splits*.
    rewrite map_app, E2.
    f_equal.
    assert (List.map (kind_subst S) nil = nil) by auto.
    revert H; generalize (@nil kind).
    clear; induction l; simpl; intros; auto.
    generalize (graph_of_tree_subst (ofs + length l0) (snd a) S).
    case_eq (graph_of_tree (ofs + length l0) (snd a)); simpl; intros.
    apply IHl.
    now rewrite map_app, H, H1.
  specialize (IHTKs ofs); revert IHTKs.
  case_eq (graph_of_kinds ofs TKs); simpl; introv HG; intros [E1 E2].
  unfold kind_subst at 1, kind_map; simpl.
  now rewrite E1, E2.
Qed.

Lemma graph_of_tree_type_subst n Ks tr S :
  graph_of_tree_type tr = (n, Ks) ->
  List.map (kind_subst S) Ks = Ks.
Proof.
  simpl.
  unfold graph_of_tree_type.
  destruct tr as [T K].
  generalize (graph_of_kinds_subst (length K) K S).
  case_eq (graph_of_kinds (length K) K); simpl; introv HG; intros [E1 E2].
  generalize (graph_of_tree_subst (length l + length l0) T S).
  case_eq (graph_of_tree (length l + length l0) T); simpl; introv HT E E'.
  injection E'; intros; subst.
  now rewrite map_app, map_app, E1, E2, E.
Qed.
*)

Section set_nth.
Variable A : Type.
Fixpoint set_nth (n : nat) (x : A) l def :=
  match n with
  | 0 => x :: tl l
  | S n => hd def l :: set_nth n x (tl l) def
  end.

Lemma set_nth_same n x l def def' : nth n (set_nth n x l def) def' = x.
Proof. revert l; induction n; simpl*. Qed.

Lemma set_nth_other n' x l def n :
  n' <> n -> nth n (set_nth n' x l def) def = nth n l def.
Proof.
revert n l; induction n'; destruct l; destruct n; simpl; intros; auto;
  try contradiction.
- now destruct n.
- rewrite IHn'. now destruct n. intro N; elim H; now rewrite N.
Qed.

Lemma length_set_nth n x l def : length l <= length (set_nth n x l def).
Proof.
  revert n; induction l; simpl; intros; auto with arith.
  destruct n; simpl; auto with arith.
Qed.
End set_nth.

Lemma extract_unique_attr K V k rvs k' rvs' a T S n Ks Us :
  binds V (Some k, rvs) K ->
  proper_instance K Ks Us ->
  nth n Us typ_def = typ_fvar V ->
  nth n Ks (None, nil) = (Some k', rvs') ->
  In (a, T) (kind_rel k) ->
  In (a, S) (kind_rel k') ->
  Cstr.unique (kind_cstr k) a = true ->
  typ_open S Us = T.
Proof.
  intros B PI nUs nKs HT HS HU.
  apply (@kind_coherent k a); auto.
  destruct PI.
  destruct (le_lt_dec (length Ks) n).
    rewrite (nth_overflow _ _ l) in nKs; discriminate.
  forward~ (list_forall2_nth (n:=n) (kind_open (Some k', rvs') nil) typ_def H0)
      as WK.
    unfold kinds_open; now rewrite map_length.
  inversions WK; clear WK.
  rewrite nUs in H1; inversions H1; clear H1.
  puts (binds_func B H2); subst.
  destruct H3. revert H1.
  unfold kinds_open; simpl.
  rewrite (nth_indep _ _ (kind_open (None, nil) Us));
    try now rewrite map_length.
  rewrite (map_nth (fun k => kind_open k Us)), nKs.
  simpl; intros [_ Erel].
  forward~ (Erel (a, typ_open S Us)).
  rewrite kind_rel_map.
  now apply (in_map_snd (fun T => typ_open T Us)).
Qed.

Lemma graph_of_tr_arrow n Ks ofs T1 T2 :
  graph_of_tree ofs (tr_arrow T1 T2) = (n, Ks) ->
  exists m1, exists Ks1, exists m2, exists Ks2,
      Ks = (Some (arrow_kind m1 m2), nil) :: Ks1 ++ Ks2 /\
      graph_of_tree (ofs+1) T1 = (m1, Ks1) /\
      graph_of_tree (ofs+length Ks1+1) T2 = (m2, Ks2).
Proof.
  simpl.
  case_eq (graph_of_tree (ofs + 1) T1); intros m1 Ks1 HT1.
  case_eq (graph_of_tree (ofs + length Ks1 + 1) T2); intros m2 Ks2 HT2 E.
  inversions E; clear E.
  now repeat esplit.
Qed.

Lemma graph_of_tr_eq n Ks ofs T1 T2 :
  graph_of_tree ofs (tr_eq T1 T2) = (n, Ks) ->
  exists m1, exists Ks1, exists m2, exists Ks2,
      Ks = (Some (eq_kind m1 m2), nil) :: Ks1 ++ Ks2 /\
      graph_of_tree (ofs+1) T1 = (m1, Ks1) /\
      graph_of_tree (ofs+length Ks1+1) T2 = (m2, Ks2).
Proof.
  simpl.
  case_eq (graph_of_tree (ofs + 1) T1); intros m1 Ks1 HT1.
  case_eq (graph_of_tree (ofs + length Ks1 + 1) T2); intros m2 Ks2 HT2 E.
  inversions E; clear E.
  now repeat esplit.
Qed.

Lemma graph_of_tree_root n Ks ofs T :
  graph_of_tree ofs T = (n, Ks) -> n = ofs.
Proof.
  induction T; simpl; try solve [introv E; inversions* E];
  try solve[ simpl;
             case_eq (graph_of_tree (ofs + 1) T1); intros n1 K1;
             case_eq (graph_of_tree (ofs + length K1 + 1) T2); intros;
             inversions* H1 ].
Qed.

End MkGraph.
