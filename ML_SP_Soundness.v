(***************************************************************************
* Preservation and Progress for mini-ML (CBV) - Proofs                     *
* Arthur Chargueraud, March 2007, Coq v8.1                                 *
* Extension to structural polymorphism                                     *
* Jacques Garrigue, October 2007 - June 2008                               *
***************************************************************************)

Set Implicit Arguments.
Require Import Arith List Metatheory
  ML_SP_Definitions ML_SP_Infrastructure.
Require Import Lia.

Module MkSound(Cstr:CstrIntf)(Const:CstIntf).

Module Infra := MkInfra(Cstr)(Const).
Import Infra.
Import Defs.

Module Mk2(Delta:DeltaIntf).
Module JudgInfra := MkJudgInfra(Delta).
Import JudgInfra.
Import Judge.

Lemma kenv_ok_concat Q K1 K2 K3 :
  kenv_ok Q (K1 & K2) -> kenv_ok Q (K1 & K3) ->
  disjoint (dom K2) (dom K3) -> kenv_ok Q (K1 & K2 & K3).
Proof.
  intros; splits*.
  intros x k B.
  destruct (in_app_or _ _ _ B).
    apply* wf_kind_weaken.
    apply* kenv_ok_wf_kind.
  apply* wf_kind_extend.
  apply* kenv_ok_wf_kind.
Qed.

Lemma ok_kinds_open_vars : forall K Ks Xs,
  ok K -> fresh (dom K) (length Ks) Xs ->
  ok (K & kinds_open_vars Ks Xs).
Proof.
  intros.
  unfold kinds_open_vars.
  apply* disjoint_ok.
  apply* ok_combine_fresh.
Qed.

Hint Resolve kenv_ok_concat ok_kinds_open_vars : core.

Lemma scheme_weaken Q K K' M :
  ok (K & K') -> scheme Q K M -> scheme Q (K & K') M.
Proof.
  intros Ok [QC SC]; split; auto; intros Xs Len.
  destruct (SC _ Len) as [? [? [L ?]]].
  splits*.
  exists (L \u dom (K & K')); intros Fr.
  forward~ H1.
  apply list_forall_imp; intros k.
  apply* wf_kind_weaken.
Qed.

Lemma env_ok_weaken Q K K' E :
  ok (K & K') -> env_ok Q K E -> env_ok Q (K & K') E.
Proof.
  intros OkK [Ok P].
  split; auto; intros X M B.
  apply* scheme_weaken.
Qed.

Lemma scheme_add_qitem Q q Q' K M :
  scheme (Q ++ Q') K M -> scheme (Q ++ q :: Q') K M.
Proof.
  intros []; split; auto.
  revert H; apply list_forall_imp; intros.
  apply* qcoherent_add_qitem.
Qed.

Lemma env_ok_add_qitem Q q Q' K E :
  env_ok (Q ++ Q') K E -> env_ok (Q ++ q :: Q') K E.
Proof.
  intros [Ok P].
  split; auto; intros X M B.
  apply* scheme_add_qitem.
Qed.

Lemma env_ok_add_qitem' q Q K E : env_ok Q K E -> env_ok (q :: Q) K E.
Proof. apply (env_ok_add_qitem nil). Qed.

Hint Resolve scheme_weaken env_ok_weaken scheme_add_qitem
     env_ok_add_qitem env_ok_add_qitem' : core.

(* ********************************************************************** *)
(** Typing is preserved by weakening *)

Lemma typing_weaken : forall gc G E F Q K t T,
   [Q ; K ; (E & G) |gc|= t ~: T] ->
   env_ok Q K (E & F & G) ->
   [Q; K ; (E & F & G) |gc|= t ~: T].
Proof.
introv Typ. gen_eq (E & G) as H. gen G.
induction Typ; introv EQ Ok; subst; auto*.
- apply* typing_var. apply* binds_weaken.
- inversions H.
  apply_fresh* (@typing_abs gc Q) as y.
  apply_ih_bind* H5.
  forward~ (H4 y).
- apply_fresh* (@typing_let gc Q M L1) as y.
    introv Fr. use (H _ Fr).
  apply_ih_bind* H2.
  forward~ (H1 y).
- apply_fresh (@typing_gc gc Q Ks) as Xs; auto.
  introv Fr.
  apply* H1.
  forward~ (H0 Xs).
- apply_fresh* (@typing_rigid gc Q) as y.
  introv Fr.
  apply* H3.
  simpl in Fr; destruct Fr as [FrR Fr].
  destruct H1 as [[Len FA1] FA2].
  rewrite <- Len in Fr.
  simpl in Fr.
  auto*.
Qed.

Lemma kenv_ok_add_qitem Q q Q' K :
  kenv_ok (Q ++ Q') K -> kenv_ok (Q ++ q :: Q') K.
Proof.
  splits*. intros r; intros.
  apply* qcoherent_add_qitem.
  use (kenv_ok_qcoherent H).
Qed.

Lemma kenv_ok_add_qitem' q Q K : kenv_ok Q K -> kenv_ok (q :: Q) K.
Proof. apply (kenv_ok_add_qitem nil). Qed.

Hint Resolve kenv_ok_add_qitem kenv_ok_add_qitem' : core.

Lemma typing_weaken_qitem gc E Q Q' q K t T :
   [Q ++ Q' ; K ; E |gc|= t ~: T] ->
   [Q ++ q :: Q'; K ; E |gc|= t ~: T].
Proof.
  intros Typ; gen_eq (Q ++ Q') as Q0.
  revert Q Q'; induction Typ; intros; subst; auto*.
  apply* typing_use.
  apply* (IHTyp2 (qeq T1 T2 :: Q0) Q').
Qed.
  
Lemma proper_instance_weaken : forall K K' Ks Us,
  ok (K & K') ->
  proper_instance K Ks Us ->
  proper_instance (K & K') Ks Us.
Proof.
  intros.
  destruct* H0 as [TM FM]; split2*.
Qed.

Lemma proper_instance_exchange K K1 K2 K' Ks Us :
  ok (K & K1 & K2 & K') ->
  proper_instance (K & K1 & K2 & K') Ks Us ->
  proper_instance (K & K2 & K1 & K') Ks Us.
Proof.
destruct 2.
constructor; auto.
apply (list_forall2_imp _ H1).
introv WK.
rewrite concat_assoc.
apply well_kinded_comm; [auto|].
rewrite <- concat_assoc.
apply* well_kinded_comm.
Qed.

Lemma wf_kind_exchange K K1 K2 K' k :
  wf_kind (K & K1 & K2 & K') k ->
  ok (K & K1 & K2 & K') ->
  wf_kind (K & K2 & K1 & K') k.
Proof.
intros WF Ok.
inversions WF; constructor.
introv Un Hin.
destruct (H _ _ Un Hin) as [k [rvs [B RV]]].
exists k; exists rvs; split; auto.
binds_cases B; auto.
Qed.

Lemma kenv_ok_exchange Q K K1 K2 K' :
  kenv_ok Q (K & K1 & K2 & K') -> kenv_ok Q (K & K2 & K1 & K').
Proof.
  destruct 1 as [Ok [AKT [QC WF]]].
  splits*.
  intros x k B.
  apply wf_kind_exchange; [| auto].
  apply* WF.
  apply* (In_exchange (x,k)).
Qed.

Lemma scheme_exchange Q K K1 K2 K' M :
  ok (K & K1 & K2 & K') ->
  scheme Q (K & K1 & K2 & K') M -> scheme Q (K & K2 & K1 & K') M.
Proof.
  intros Ok [QC SC]; split; auto; intros Xs Len.
  destruct (SC _ Len) as [? [? [L ?]]].
  splits*.
  exists (L \u dom (K & K2 & K1 & K')); intros Fr.
  forward~ H1.
  apply list_forall_imp; intros k FA.
  rewrite concat_assoc in FA.
  rewrite concat_assoc.
  apply wf_kind_exchange; auto.
  rewrite <- concat_assoc.
  apply* ok_kinds_open_vars.
  repeat rewrite dom_concat in *.
  auto.
Qed.

Lemma env_ok_exchange Q K K1 K2 K' E :
  ok (K & K1 & K2 & K') ->  
  env_ok Q (K & K1 & K2 & K') E -> env_ok Q (K & K2 & K1 & K') E.
Proof.
  intros OkK [Ok P].
  split; auto; intros X M B.
  generalize (P _ _ B).
  apply* scheme_exchange.
Qed.

Hint Resolve env_ok_exchange kenv_ok_exchange : core.

Lemma typing_exchange : forall gc Q K K1 K2 K' E t T,
  [ Q ; K & K1 & K2 & K'; E | gc |= t ~: T ] ->
  [ Q ; K & K2 & K1 & K'; E | gc |= t ~: T ].
Proof.
introv Typ. gen_eq (K & K1 & K2 & K') as H. gen K K1 K2 K'.
induction Typ; introv EQ; subst.
- apply proper_instance_exchange in H2; eauto.
- assert (Typ := typing_abs _ _ H H0 H1 H2 H3 H4).
  inversions H.
  apply_fresh* (@typing_abs gc Q) as y.
  apply binds_exchange. apply H0.
  now kenv_ok_hyps.
- apply_fresh* (@typing_let gc Q M) as y.
  introv Fr.
  rewrite concat_assoc.
  apply* (H0 Xs).
  rewrite* concat_assoc.
- assert (Typ := typing_app gc T H H0 H1 H2 Typ1 Typ2).
  apply* typing_app.
  apply* (@binds_exchange _ V (Some k, rvs)).
  now kenv_ok_hyps.
- apply* typing_cst. apply* proper_instance_exchange.
- apply* typing_gc.
  introv Fr.
  rewrite concat_assoc.
  apply* (H1 Xs).
  rewrite* concat_assoc.
- apply* typing_ann.
  apply* proper_instance_exchange.
  apply* proper_instance_exchange.
- apply* (@typing_rigid gc Q). apply* proper_instance_exchange.
  introv Fr.
  rewrite concat_assoc.
  apply* (H3 R Xs).
  now rewrite concat_assoc.
- apply* typing_use. apply* proper_instance_exchange.
- apply* typing_eq.
  apply binds_exchange in H1; auto*.
Qed.

Lemma typing_comm : forall gc Q K K1 K2 E t T,
  [ Q ; K & K1 & K2 ; E | gc |= t ~: T ] ->
  [ Q ; K & K2 & K1 ; E | gc |= t ~: T ].
Proof.
  intros.
  rewrite <- (concat_empty (K & _ & _)).
  apply* typing_exchange.
Qed.
  
Lemma tree_subst_eq_refl S t : tree_subst_eq S t t.
Proof. induction t; simpl; constructor; auto. Qed.

Lemma typing_weaken_kinds : forall gc Q K K' E t T,
  [ Q ; K; E | gc |= t ~: T ] ->
  kenv_ok Q (K & K') ->
  [ Q; K & K'; E | gc |= t ~: T ].
Proof.
introv Typ.
induction* Typ; intros.
- apply* typing_var. apply* proper_instance_weaken.
- apply_fresh* (@typing_let gc Q M (L1 \u dom(K&K'))) as y.
  intros. clear H1 H2.
  rewrite <- (concat_empty (K & _ & _)).
  apply typing_exchange.
  apply* H0; clear H0. rewrite* concat_assoc.
  forward~ (H Xs) as Typ.
  destruct (typing_regular Typ) as [[Rok [RK1 [RK2 RK3]]] _].
  destruct H3 as [Ok [ROk1 [ROk2 ROk3]]].
  rewrite <- concat_assoc.
  splits*.
  apply env_prop_concat; intros x k B.
    apply* wf_kind_extend.
  apply* wf_kind_weaken.
- apply* typing_cst. apply* proper_instance_weaken.
- apply_fresh* (@typing_gc gc Q Ks) as y.
  introv Fr.
  rewrite <- (concat_empty (K & _ & _)).
  apply typing_exchange.
  apply* (H1 Xs); clear H1.
  forward~ (H0 Xs).
- apply* typing_ann. apply* proper_instance_weaken.
  apply* proper_instance_weaken.
- apply_fresh* (@typing_rigid gc Q) as Xs.
    apply* proper_instance_weaken.
  introv Fr.
  rewrite <- (concat_empty (K & _ & _)).
  apply typing_exchange.
  apply* (H3 R Xs).
  forward~ (H2 R Xs) as Typ.
  destruct (typing_regular Typ) as [[Ok [Ok1 [Ok2 Ok3]]] _].
  destruct H4 as [Ok' [Ok1' [Ok2' Ok3']]].
  assert (Ok'': ok (K' & kinds_open_vars ((None, rvar_f R :: nil) :: Ks) Xs)).
    apply* ok_kinds_open_vars.
    simpl in Fr; destruct Fr as [_ Fr].
    destruct H1 as [[Len _] _].
    simpl in Len |- *.
    rewrite* Len.
  splits*.
  apply env_prop_concat; intros x k B. apply* wf_kind_extend.
  apply* wf_kind_weaken.
- apply* typing_use.
  apply* proper_instance_weaken.
Qed.

Lemma proper_instance_subst : forall K K' K'' Ks Us S,
  proper_instance (K & K' & K'') Ks Us ->
  well_subst (K & K' & K'') (K & map (kind_subst S) K'') S ->
  proper_instance (K & map (kind_subst S) K'') (List.map (kind_subst S) Ks)
    (List.map (typ_subst S) Us).
Proof.
  introv PI WS.
  destruct* PI.
  split. rewrite map_length. apply* typ_subst_type_list.
  rewrite* <- kinds_subst_open.
Qed.

Lemma well_subst_fresh Q K K' K'' S Ys Ks :
  well_subst (K & K' & K'') (K & map (kind_subst S) K'') S ->
  fresh (dom S) (length Ks) Ys ->
  kenv_ok Q (K & K' & K'' & kinds_open_vars Ks Ys) ->
  well_subst (K & K' & K'' & kinds_open_vars Ks Ys)
    (K & map (kind_subst S) (K'' & kinds_open_vars Ks Ys)) S.
Proof.
  intros WS Fr [Kok Kwf].
  forward~ (fresh_kinds_open_vars _ _ _ Kok) as Fr'.
  repeat rewrite dom_concat in Fr'.
  intro x; intros.
  rewrite map_concat. rewrite <- concat_assoc.
  destruct (binds_concat_inv H) as [[N B]|B]; clear H.
    apply well_kinded_extend.
      rewrite concat_assoc, <-map_concat.
      apply* ok_map.
    apply* WS.
  simpl.
  puts (binds_map (kind_subst S) B).
  rewrite var_subst_fresh by auto.
  apply (@wk_kind (kind_subst S k)).
      apply* binds_prepend.
    apply entails_refl.
  forward (wf_kind_open_subst Ks Ys {} WS) as WF.
      rewrite dom_concat, dom_map; auto.
    destruct (env_prop_concat_inv _ _ (proj33 Kwf)).
    apply (env_prop_list_forall Ys). apply H1.
      ok_solve.
    rewrite* map_length.
  rewrite kinds_subst_open_vars in H |- * by auto.
  apply (list_forall_out WF).
  use (binds_combine _ _ H).
  unfold kinds_open in H0.
  now rewrite list_map_comp in H0.
Qed.

Lemma kenv_ok_subst Q K K' K'' S :
  disjoint (dom S) (fv_in kind_fv K \u dom K) ->
  well_subst (K & K' & K'') (K & map (kind_subst S) K'') S ->
  kenv_ok Q (K & K' & K'') -> kenv_ok Q (K & map (kind_subst S) K'').
Proof.
intros Dis WS [Ok [Ok1 [Ok2 Ok3]]].
splits*; apply* env_prop_concat.
- intro; intros. destruct* (in_map_inv _ _ _ _ H) as [b [Hb B]]; subst*.
- intros x k B.
  destruct (in_map_inv _ _ _ _ B) as [k' [Hk B']].
  rewrite <- Hk.
  apply qcoherent_subst.
  apply (Ok2 x k').
  apply* in_or_concat.
- intros x k B.
  unfold well_subst in WS.
  forward~ (WS x k) as WK.
  destruct* k as [[ck|] rvs].
  assert (Hx : x \in dom K) by apply* in_dom.
  rewrite typ_subst_fresh in WK by auto*.
  rewrite kind_subst_fresh in WK.
    inversions WK.
    apply* (entails_wf_kind H1 H4).
  assert (FVk := fv_in_spec kind_fv K _ _ B).
  simpl in FVk.
  disjoint_solve.
- intros x k B.
  destruct* (in_map_inv _ _ _ _ B) as [k' [Hb B']]; subst*.
  forward~ (WS x k') as WK.
  destruct k' as [ck' rvs'].
  inversions WK.
  destruct ck'.
    apply* (entails_wf_kind H1 H4).
  constructor.
Qed.

Lemma env_ok_subst Q K K' K'' E F S :
  well_subst (K & K' & K'') (K & map (kind_subst S) K'') S ->
  disjoint (dom S) (fv_in sch_fv E) ->
  env_ok Q (K & K' & K'') (E & F) ->
  env_ok Q (K & map (kind_subst S) K'') (E & map (sch_subst S) F).
Proof.
  intros WS Dis Eok.
  split; auto*.
  intros x M B.
  destruct (in_concat_or _ _ _ B).
    destruct (in_map_inv _ _ _ _ H) as [M' []]; subst; clear B H.
    forward~ (proj2 Eok x M') as HS'.
    apply* sch_subst_type.
  forward~ (proj2 Eok x M) as HS'.
  rewrite <- (sch_subst_fresh S).
    apply* sch_subst_type.
  use (fv_in_spec sch_fv E _ _ H).
Qed.

Hint Resolve kenv_ok_subst env_ok_subst : core.

(* ********************************************************************** *)
(** Type substitution preserves typing *)

Lemma well_subst_binds K K' S V k rvs :
  well_subst K K' S -> binds V (Some k, rvs) K ->
  exists k', exists rvs',
    binds (var_subst S V) (Some k', rvs') K' /\
    entails_ckind k' (ckind_map (typ_subst S) k).
Proof.
  intros WS HB; poses WK (WS _ _ HB).
  simpl in WK; inversions WK.
  unfold entails in H1.
  destruct k' as [[k'|] rvs']; simpl in H1.
    exists* k'.
  destruct* H1.
Qed.

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

Lemma typing_typ_subst : forall gc Q F K'' S K K' E t T,
  disjoint (dom S) (env_fv E \u fv_in kind_fv K \u dom K) ->
  dom K' << dom S -> disjoint (dom K') (fv_in (fun v:var => {{v}}) S) ->
  well_subst (K & K' & K'') (K & map (kind_subst S) K'') S ->
  [Q; K & K' & K''; E & F |gc|= t ~: T] ->
  [Q; K & map (kind_subst S) K''; E & (map (sch_subst S) F) |gc|=
    t ~: (typ_subst S T)].
Proof.
introv Dis DomK' Dis' WS Typ.
gen_eq (K & K' & K'') as GK; gen_eq (E & F) as G; gen K''; gen F.
induction Typ; introv WS EQ EQ'; subst.
  (* Var *)
- rewrite~ sch_subst_open. apply* typing_var.
    binds_cases H1.
      apply* binds_concat_fresh.
      rewrite* sch_subst_fresh.
      use (fv_in_spec sch_fv _ _ _ (binds_in B)).
     auto*.
    destruct M as [T Ks]. simpl.
    apply* proper_instance_subst.
  (* Abs *)
- simpl.
  destruct (well_subst_binds WS H0) as [k' [rvs' [HB [HE HR]]]].
  inversions H.
  eapply (@typing_abs gc Q L).
  + now apply (type_fvar (var_subst S X)).
  + exact HB.
  + destruct k; simpl in *; subst.
    now apply Cstr.entails_arrow.
  + apply HR; rewrite kind_rel_map.
    now apply (in_map_snd (typ_subst S) Cstr.arrow_dom (typ_fvar X)).
  + apply HR; rewrite kind_rel_map.
    now apply (in_map_snd (typ_subst S) _ T).
  + intros.
    replace (Sch (typ_fvar (var_subst S X)) nil)
      with (sch_subst S (Sch (typ_fvar X) nil)) by auto.
    now apply_ih_map_bind H5.
  (* Let *)
- apply_fresh* (@typing_let gc Q (sch_subst S M)
                            (L1 \u dom S \u dom K \u dom K'')) as y.
   clear H1 H2. clear L2 T2 t2.
   simpl. intros Ys Fr.
   rewrite* <- sch_subst_open_vars.
   rewrite* <- kinds_subst_open_vars.
   rewrite concat_assoc. rewrite <- map_concat.
   rewrite map_length in Fr.
   apply* H0; clear H0.
     forward~ (H Ys) as Typ.
     apply* (@well_subst_fresh Q).
   rewrite* concat_assoc.
  apply_ih_map_bind* H2.
  (* App *)
- destruct (well_subst_binds WS H) as [k' [HB [HE HR]]].
  apply* (@typing_app gc).
  + destruct k; simpl in *; subst.
    apply Cstr.entails_arrow.
    apply HR; rewrite kind_rel_map.
  + apply HR; rewrite kind_rel_map.
    now apply (in_map_snd (typ_subst S) _ S0).
  + apply HR; rewrite kind_rel_map.
    now apply (in_map_snd (typ_subst S) _ T).
  (* Cst *)
- rewrite* sch_subst_open.
  assert (disjoint (dom S) (sch_fv (Delta.type c))).
    intro x. rewrite* Delta.closed.
  rewrite* sch_subst_fresh.
  apply* typing_cst.
  rewrite* <- (sch_subst_fresh S H2).
  destruct (Delta.type c) as [T Ks]; simpl.
  apply* proper_instance_subst.
  (* GC *)
- apply* (@typing_gc gc Q (List.map (kind_subst S) Ks)
                     (L \u dom S \u dom K \u dom K'')).
   rewrite map_length; intros.
   rewrite* <- kinds_subst_open_vars.
   rewrite concat_assoc. rewrite <- map_concat.
   apply* (H1 Xs); clear H1.
     forward~ (H0 Xs) as Typ.
     apply* (@well_subst_fresh Q).
  rewrite* concat_assoc.
- (* Ann *)
  rewrite <- map_nth.
  simpl.
  apply (@typing_ann gc Q _ _ _ (List.map (kind_subst S) Ks) _ _ (List.map (typ_subst S) Us)); auto*.
  + now rewrite (graph_of_tree_type_subst _ S H).
  + apply* proper_instance_subst.
  + apply* proper_instance_subst.
  + forward~ (IHTyp F K'').
    now rewrite <- map_nth.
- (* Rigid *)
  rewrite typ_subst_open.
  apply (@typing_rigid gc Q (L \u dom S) _ (List.map (kind_subst S) Ks)); auto*.
    apply (proper_instance_subst _ _ _ H1); auto.
  simpl; introv [HR Fr].
  set (kov := kinds_open_vars _ Xs).
  assert (kov = 
     map (kind_subst S) (kinds_open_vars ((None, rvar_f R :: nil) :: Ks) Xs)).
    rewrite* kinds_subst_open_vars.
  rewrite H4.
  rewrite concat_assoc, <- map_concat, typ_subst_open_vars.
  rewrite map_length in Fr.
  apply* (H3 R Xs); auto.
  + forward~ (H2 R Xs) as Typ.
    destruct (typing_regular Typ).
    apply (well_subst_fresh (Q:=qvar R :: Q)); trivial.
      destruct H1 as [[] _]; simpl in *.
      rewrite* H1.
    apply* kenv_ok_add_qitem'.
  + rewrite* concat_assoc.
  + auto.
  (* Use *)
- assert (nth n Us typ_def = typ_open (typ_bvar n) Us) by reflexivity.
  rewrite H1, typ_subst_open in IHTyp1.
  apply* (@typing_use gc n (List.map (kind_subst S) Ks)
                      (List.map (typ_subst S) Us)).
    now rewrite (graph_of_tree_type_subst _ S H).
  apply* proper_instance_subst.
  (* Eq *)
- assert (WK := WS _ _ H1).
  inversions WK.
  unfold kind_subst, kind_map in H6.
  destruct H6; simpl in H4, H6.
  destruct k' as [[k'|] rvs']; try contradiction.
  simpl in H4; destruct H4 as [_ Erel].
  apply* typing_eq; apply Erel; rewrite kind_rel_map;
    now apply (in_map_snd (typ_subst S) _ T).
Qed.

Lemma typing_typ_substs : forall gc Q K' S K E t T,
  disjoint (dom S) (env_fv E \u fv_in kind_fv K \u dom K) ->
  dom K' << dom S -> disjoint (dom K') (fv_in var_fv S) ->
  well_subst (K & K') K S ->
  [ Q; K & K'; E |gc|= t ~: T ] ->
  [ Q; K ; E |gc|= t ~: (typ_subst S T) ] .
Proof.
  intros.
  generalize (@typing_typ_subst gc Q empty empty); intro TTS.
  simpl in TTS.
  apply* TTS.
Qed.

(* ********************************************************************** *)
(** Typing schemes for expressions *)

Definition has_scheme_vars gc L Q (K:kenv) E t M := forall Xs,
  fresh L (sch_arity M) Xs ->
  [ Q; K & kinds_open_vars (sch_kinds M) Xs; E |gc|= t ~: (M ^ Xs) ].

Definition has_scheme gc Q K E t M := forall Us,
  types (sch_arity M) Us ->
  list_forall2 (well_kinded K) (kinds_open (sch_kinds M) Us) Us ->
  [ Q; K ; E |gc|= t ~: (M ^^ Us) ].

(* ********************************************************************** *)
(** Type schemes of terms can be instanciated *)

Lemma kind_subst_open_combine : forall Xs Vs Ks,
  fresh (kind_fv_list Ks) (length Vs) Xs ->
  forall k : kind,
    In k Ks ->
    kind_open k (typ_fvars Vs) =
    kind_subst (combine Xs Vs) (kind_open k (typ_fvars Xs)).
Proof.
  introv Fr. intros.
  rewrite* kind_subst_open.
  rewrite* kind_subst_fresh.
    rewrite* (fresh_subst {}).
  rewrite* dom_combine.
  use (kind_fv_fresh _ _ _ _ H Fr).
Qed.

Lemma well_subst_open_vars : forall Q (K:kenv) Vs (Ks:list kind) Xs,
  kenv_ok Q K ->
  fresh (fv_in kind_fv K) (length Ks) Xs ->
  fresh (kind_fv_list Ks) (length Vs) Xs ->
  list_forall2 (well_kinded K) (kinds_open Ks (typ_fvars Vs)) (typ_fvars Vs) ->
  well_subst (K & kinds_open_vars Ks Xs) K (combine Xs Vs).
Proof.
  introv Kok Fr Fr' WK.
  intro x; intros.
  destruct* (binds_concat_inv H) as [[N B]|B]; clear H.
    unfold kinds_open_vars in N.
    rewrite* kind_subst_fresh.
      rewrite* typ_subst_fresh.
      apply (wk_kind B); auto.
      apply* (kenv_ok_wf_kind Kok x).
    use (fv_in_spec kind_fv _ _ _ (binds_in B)).
  unfold kinds_open_vars, kinds_open in *.
  rewrite <- map_combine in B.
  destruct (binds_map_inv _ _ B) as [k0 [Hk0 Bk0]]. subst.
  puts (binds_map (kind_subst (combine Xs Vs)) B).
  simpl in H; do 2 rewrite map_combine in H.
  rewrite list_map_comp in H.
  refine (list_forall2_get (P:=well_kinded K) Xs _ H _).
    instantiate (1:=typ_fvars Vs).
    rewrite* <- (list_map_ext Ks _ _ (kind_subst_open_combine _ _ _ Fr')).
  simpl; unfold var_subst.
  case_eq (get x (combine Xs Vs)); intros.
    unfold typ_fvars. rewrite <- (map_combine typ_fvar).
    apply (binds_map typ_fvar); auto.
  elim (get_contradicts _ _ _ _ Bk0 H0); auto.
Qed.

Lemma has_scheme_from_vars gc L Q K E t M :
  kenv_ok Q K ->
  has_scheme_vars gc L Q K E t M ->
  has_scheme gc Q K E t M.
Proof.
  intros Kok H Us TV. unfold sch_open.
  destruct M as [T Ks]; simpls.
  fold kind in K. fold kenv in K.
  pick_freshes (length Ks) Xs.
  rewrite (fresh_length _ _ _ Fr) in TV.
  destruct (vars_of_types TV) as [Vs [Len]]; subst.
  fold (typ_open_vars T Vs).
  rewrite~ (@typ_subst_intro Xs Vs T).
  unfolds has_scheme_vars sch_open_vars. simpls.
  intro WK.
  apply* (@typing_typ_substs gc Q (kinds_open_vars Ks Xs)).
    rewrite* dom_kinds_open_vars.
    rewrite* fv_in_combine_vars.
    rewrite* <- (typ_fv_typ_fvars Vs).
  apply* well_subst_open_vars.
  rewrite* Len.
Qed.

(* ********************************************************************** *)
(** Typing is preserved by term substitution *)
Lemma typing_trm_subst : forall gc F M Q K E t T z u,
  [ Q ; K ; E & z ~ M & F |(gc,GcAny)|= t ~: T ] ->
  (exists L:vars, has_scheme_vars (gc,GcAny) L Q K E u M) ->
  term u ->
  [ Q ; K ; E & F |(gc,GcAny)|= (trm_subst z u t) ~: T ].
Proof.
introv Typt. intros Typu Wu.
gen_eq (E & z ~ M & F) as G. gen_eq (gc, GcAny) as gc0. gen F.
induction Typt; introv EQ1 EQ2; subst; simpl trm_subst;
  destruct Typu as [Lu Typu].
- case_var.
    binds_get H1. apply_empty* (@typing_weaken (gc,GcAny)).
      destruct H2; apply* (has_scheme_from_vars H Typu).
      binds_cases H1; apply* typing_var.
- inversions H; clear H.
  apply_fresh* (@typing_abs (gc,GcAny) Q) as y.
  rewrite* trm_subst_open_var.
  apply_ih_bind* H5.
- apply_fresh* (@typing_let (gc,GcAny) Q M0 (L1 \u dom K)) as y.
    intros; apply* H0.
    exists (Lu \u mkset Xs); intros Ys TypM.
    forward~ (Typu Ys) as Typu'; clear Typu.
    rewrite <- (concat_empty (K & _ & _)); apply typing_exchange.
    forward~ (H Xs) as Typt.
    rewrite concat_empty; apply* typing_weaken_kinds.
  rewrite* trm_subst_open_var.
  apply_ih_bind* H2.
- assert (exists L : vars, has_scheme_vars (gc,GcAny) L Q K E u M). exists* Lu.
  auto*.
- auto*.
- apply_fresh* (@typing_gc (gc,GcAny) Q Ks) as y.
  intros Xs Fr.
  apply* H1; clear H1.
  exists (Lu \u dom K \u mkset Xs); intros Ys Fr'.
  forward~ (Typu Ys) as Typu'; clear Typu.
  rewrite <- (concat_empty (K & _ & _)); apply typing_exchange.
  rewrite concat_empty; apply* typing_weaken_kinds.
  forward~ (H0 Xs).
- auto*.
- apply* (@typing_rigid (gc, GcAny) Q (L \u Lu)). intros.
  forward~ (H3 R Xs) as Typ.
    exists (L \u Lu \u mkset Xs). intro Ys; intros.
    apply* typing_comm. apply* typing_weaken_kinds.
    forward~ (Typu Ys) as Typu'.
    apply kenv_ok_concat; auto.
    forward~ (H2 R Xs).
    repeat rewrite* dom_kinds_open_vars.
    destruct H1; simpl in *; destruct H4.
    rewrite* <- (fresh_length _ _ _ H7).
  rewrite* <- trm_open_rigid_subst_comm.
- apply* typing_use.
  apply* IHTypt2.
  exists Lu. intros Xs Fr.
  apply (typing_weaken_qitem nil); auto.
- auto*.
Qed.

(* ********************************************************************** *)
(** Canonical derivations *)

(* less than 100 lines! *)

Lemma typing_gc_any gc Q K E t T :
  [ Q ; K ; E |gc|= t ~: T ] -> [ Q ; K ; E |(true,GcAny)|= t ~: T ].
Proof.
  induction 1; auto*.
  apply* typing_gc. simpl; auto.
Qed.

Lemma typing_gc_raise Q gc K E t T :
  [Q ; K ; E |gc|= t ~: T ] -> [Q ; K ; E |gc_raise gc|= t ~: T ].
Proof.
  induction 1; destruct gc; destruct g; simpl; auto*.
  apply* typing_gc. simpl; auto.
Qed.

Definition typing_gc_let Q K E t T := [Q ; K ; E |(true,GcLet)|= t ~: T ].

Lemma typing_gc_ind (P : qenv -> kenv -> env -> trm -> typ -> Prop) :
  (forall Q K E t T, [ Q; K; E |(false,GcLet)|= t ~: T ] -> P Q K E t T) ->
  (forall Ks L Q K E t T,
    (forall Xs : list var,
      fresh L (length Ks) Xs ->
      P Q (K & kinds_open_vars Ks Xs) E t T) ->
    P Q K E t T) ->
  forall Q K E t T, typing_gc_let Q K E t T -> P Q K E t T.
Proof.
  intros.
  unfold typing_gc_let in H1.
  gen_eq (true,GcLet) as gc.
  induction H1; intros; subst; try solve [apply* H].
  apply* H0.
Qed.

Lemma typing_canonize gc Q K E t T :
  [ Q ; K ; E |gc|= t ~: T ] -> [ Q ; K ; E |(true,GcLet)|= t ~: T ].
Proof.
induction 1; auto*.
  (* App *)
- clear H3 H4.
  gen H IHtyping1.
  fold (typing_gc_let Q K E t2 S) in IHtyping2.
  apply (proj2 (A:=kenv_ok Q K)).
  induction IHtyping2 using typing_gc_ind.
    split2*; intros; subst.
    gen H H3. gen_eq (typ_fvar V) as S.
    fold (typing_gc_let Q K E t1 S) in IHtyping1.
    apply (proj2 (A:=kenv_ok Q K)).
    induction IHtyping1 using typing_gc_ind.
      split2*; intros; subst.
      apply* typing_app.
    split.
      destruct (var_freshes (L \u fv_in kind_fv K) (length Ks))
        as [Xs HXs].
      destruct* (H Xs).
      apply* kenv_ok_strengthen.
      rewrite* dom_kinds_open_vars.
    intros; subst.
    apply* (@typing_gc (true,GcLet) Q Ks L).
      simpl; auto.
    intros.
    destruct* (H Xs H3); clear H.
    apply* H7.
    apply* typing_weaken_kinds.
  split.
    destruct (var_freshes (L \u fv_in kind_fv K) (length Ks)) as [Xs HXs].
    destruct* (H Xs).
    apply* kenv_ok_strengthen.
    rewrite* dom_kinds_open_vars.
  intros.
  apply (@typing_gc (true,GcLet) Q Ks (L \u dom K)); simpl; auto.
  intros.
  destruct (H Xs); auto.
  apply* H6; clear H6.
  apply* typing_weaken_kinds.
  (* GC *)
- apply* typing_gc.
  simpl; auto.
  (* Ann *)
- clear H2.
  gen_eq (nth n Us typ_def) as T0.
  assert (OkK: ok K) by auto.
  fold (typing_gc_let Q K E t T0) in IHtyping.
  apply (proj2 (A:=kenv_ok Q K)).
  induction IHtyping using typing_gc_ind.
    splits*.
    intros; subst.
    apply (typing_ann (true,GcLet) T (Ks:=Ks) (Us:=Us) (Us':=Us')); auto.
  split.
    destruct (var_freshes (L \u dom K \u fv_in kind_fv K) (length Ks0))
      as [Xs HXs].
    destruct* (H2 Xs).
        apply* proper_instance_weaken.
      apply* proper_instance_weaken.
    apply* kenv_ok_strengthen.
    rewrite* dom_kinds_open_vars.
  intros; subst.
  apply (@typing_gc (true,GcLet) Q Ks0 (L \u dom K)); simpl; auto.
  intros.
  destruct (H2 Xs); auto.
  + apply* proper_instance_weaken.
  + apply* proper_instance_weaken.
Qed.

(* End of canonical derivations *)

(* ********************************************************************** *)
(** Extra hypotheses for main results *)

Module Type SndHypIntf.
  Parameter delta_typed : forall c tl vl Q K E gc T,
    [ Q ; K ; E |(false,gc)|= const_app c tl ~: T ] ->
    [ Q ; K ; E |(false,gc)|= @Delta.reduce c tl vl ~: T ].
End SndHypIntf.

Module Mk3(SH:SndHypIntf).
Import SH.

(* ********************************************************************** *)
(** Preservation: typing is preserved by reduction *)

Lemma typ_open_vars_nil : forall T,
  type T -> typ_open_vars T nil = T.
Proof.
  induction T; unfold typ_open_vars; simpl; intros; auto*.
  inversion H.
Qed.

Lemma typing_abs_inv : forall gc Q K E V rvs k t1 t2 T1 T2,
  binds V (Some k, rvs) K ->
  kind_cstr k = Cstr.arrow ->
  In (Cstr.arrow_dom, T1) (kind_rel k) ->
  In (Cstr.arrow_cod, T2) (kind_rel k) ->
  [Q ; K ; E |(gc,GcAny)|= trm_abs t1 ~: typ_fvar V] ->
  [Q ; K ; E |(gc,GcAny)|= t2 ~: T1] ->
  [Q ; K ; E |(gc,GcAny)|= t1 ^^ t2 ~: T2].
Proof.
  introv HB Hk Hdom Hcod. intros Typ1 Typ2.
  gen_eq (gc,GcAny) as gcs.
  gen_eq (trm_abs t1) as t.
  gen_eq (typ_fvar V) as T.
  induction Typ1; intros; subst; try discriminate.
    inversions H6; inversions H7; clear H6 H7.
    puts (binds_inj H0 HB).
    inversions H6.
    assert (U = T1).
      apply* (kind_coherent k (x:=Cstr.arrow_dom)).
      rewrite H1. apply Cstr.unique_dom.
    assert (T = T2).
      apply* (kind_coherent k (x:=Cstr.arrow_cod)).
      rewrite H1. apply Cstr.unique_cod.
    subst U T.
    clear H0 H1 H2 H3 H6.
    pick_fresh x'.
    rewrite* (@trm_subst_intro x').
    apply_empty* (@typing_trm_subst gc).
    exists {}. intro. unfold kinds_open_vars, sch_open_vars; simpl.
    destruct Xs; simpl*. rewrite* typ_open_vars_nil.
  apply (@typing_gc (gc,GcAny) Q Ks L). simpl*.
  intros.
  puts (H0 Xs H2); clear H0.
  apply* H1.
  apply* typing_weaken_kinds.
Qed.

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
  case T; simpl; try solve [introv E; inversions* E];
  intros T1 T2; simpl;
  case_eq (graph_of_tree (ofs + 1) T1); intros n1 K1;
  case_eq (graph_of_tree (ofs + length K1 + 1) T2); intros;
  inversions* H1.
Qed.

Lemma value_trm_open_rigid n r t :
  value t -> value (trm_rigid_rec n r t).
Proof.
  unfold value.
  intros [m Value]. exists m. revert n r.
  induction Value; intros; simpl*.
  apply* value_abs.
  inversions H.
  apply* (@term_abs L); intros.
  rewrite trm_rigid_rec_open_var.
  apply* term_rigid_rec.
Qed.

Lemma trm_open_rigid_red t t' r :
  t --> t' ->
  trm_open_rigid t r --> trm_open_rigid t' r.
Proof.
  unfold trm_open_rigid. intros; generalize 0; revert r.
  induction H; simpl*; intros; try rewrite trm_rigid_rec_open.
  + apply red_abs.
    apply (@term_abs (trm_fv t1)).
    intros.
    rewrite trm_rigid_rec_open_var.
    apply term_rigid_rec.
    inversions* H.
    apply* value_trm_open_rigid.
  + apply red_let.
    inversions H.
    apply (@term_let L).
    apply* term_rigid_rec.
    intros. rewrite trm_rigid_rec_open_var.
    apply* term_rigid_rec.
    apply* value_trm_open_rigid.
  + admit.
  + apply* red_let_1.
    inversions H. exists x. intros.
    rewrite trm_rigid_rec_open_var.
    apply* term_rigid_rec.
  + apply* red_app_1.
    inversions H. apply* value_trm_open_rigid.
  + constructor; auto*;
    apply* term_rigid_rec.
  + constructor; auto*.
    apply* term_rigid_rec.
  + constructor; auto*; apply* term_rigid_rec.
  + constructor; auto*.
    apply* term_rigid_rec.
  + constructor.
    inversions H.
    apply* (@term_abs L); intros.
    rewrite trm_rigid_rec_open_var.
    apply* term_rigid_rec.
    apply* term_rigid_rec.
  + constructor.
    inversions H.
    apply* (@term_abs L); intros.
    rewrite trm_rigid_rec_open_var.
    apply* term_rigid_rec.
  + constructor.
    inversions H.
    apply* (@term_abs L); intros.
    rewrite trm_rigid_rec_open_var.
    apply* term_rigid_rec.
  + constructor.
    inversions H.
    apply* (@term_abs L); intros.
    rewrite trm_rigid_rec_open_var.
    apply* term_rigid_rec.
  + constructor; apply* term_rigid_rec.
Admitted.

Lemma preservation_result : preservation.
Proof.
introv Typ. gen_eq (true, GcAny) as gc. gen t'.
induction Typ; introv EQ Red; subst; inversions Red;
  try solve [apply* typing_gc];
  try (destruct (const_app_inv c tl) as [eq | [T1' [T2' eq]]];
       rewrite eq in *; discriminate).
  (* Let *)
- pick_fresh x. rewrite* (@trm_subst_intro x).
   simpl in H1.
   apply_empty* (@typing_trm_subst true).
   apply* H1.
  (* Let *)
- apply* (@typing_let (true,GcAny) Q M L1).
  (* Beta *)
- apply* typing_abs_inv.
  (* Delta *)
- assert ([Q;K;E |(true,GcAny)|= trm_app t1 t2 ~: T]) by auto*.
  use (typing_canonize H5).
  fold (typing_gc_let Q K E (trm_app t1 t2) T) in H6.
  rewrite <- H3 in *.
  clear -H6.
  gen_eq (const_app c tl) as t1.
  induction H6 using typing_gc_ind; intros; subst.
    apply* typing_gc_any.
    apply* delta_typed.
  apply* typing_gc. simpl*.
  (* App1 *)
- auto*.
  (* App2 *)
- auto*.
  (* ApplyAnn1 *)
- apply typing_canonize in Typ1.
  gen_eq (trm_ann (trm_abs t) (tr_arrow T0 U)) as t1.
  gen_eq (typ_fvar V) as T1.
  fold (typing_gc_let Q K E t1 T1) in Typ1.
  clear IHTyp1 IHTyp2.
  revert H Typ2 Red.
  apply (proj2 (A:=kenv_ok Q K)).
  induction Typ1 using typing_gc_ind.
    split2*; intros; subst.
    inversions H; try discriminate; simpl in *.
    inversions H15; try discriminate.
    assert (exists m1, exists m2,
            nth n Ks (None,nil) = (Some (arrow_kind m1 m2),nil)).
      unfold graph_of_tree_type in H9.
      destruct (graph_of_tr_arrow _ _ _ H9)
        as [m1 [Ks1 [m2 [Ks2 [HKs _]]]]].
      exists m1; exists m2.
      now rewrite (graph_of_tree_root _ _ H9), HKs.
    destruct H4 as [m1 [m2 Hn]].
    case_eq (graph_of_tree_type T0); intros m3 Ks1 GT1.
    assert (exists Us1, exists Us1',
                 proper_instance K Ks1 Us1 /\
                 proper_instance K Ks1 Us1' /\
                 nth m3 Us1 typ_def = nth m1 Us' typ_def /\
                 nth m3 Us1' typ_def = nth m1 Us typ_def).
      admit.
    destruct H4 as [Us1 [Us1' [PI1 [PI1' [Hm31 Hm31']]]]].
    apply (@typing_let _ Q (Sch (nth m1 Us typ_def) nil) (dom K) (L \u dom E));
        auto.
      simpl; introv Fr.
      destruct Xs; try contradiction; simpl.
      unfold sch_open_vars; simpl.
      rewrite typ_open_vars_nil by admit.
      rewrite <- Hm31'.
      apply (typing_ann _ _ GT1 PI1 PI1').
      rewrite Hm31.
      assert (typ_open (typ_bvar m1) Us' = S).
        clear H11.
        apply* extract_unique_attr.
        now rewrite H0, Cstr.unique_dom.
      simpl in H4; rewrite* H4.
    intros X FrX.
    unfold trm_open; simpl trm_open_rec.
    fold (trm_open t (trm_fvar X)).
    assert (typ_open (typ_bvar m2) Us' = T).
      clear H11.
      apply* extract_unique_attr.
      now rewrite H0, Cstr.unique_cod.
    rewrite <- H4; simpl typ_open.
    case_eq (graph_of_tree_type U); intros m4 Ks2 GT2.
    assert (exists Us2, exists Us2',
                 proper_instance K Ks2 Us2 /\
                 proper_instance K Ks2 Us2' /\
                 nth m4 Us2 typ_def = nth m2 Us typ_def /\
                 nth m4 Us2' typ_def = nth m2 Us' typ_def).
      admit.
    destruct H17 as [Us2 [Us2' [PI2 [PI2' [Hm42 Hm42']]]]].
    rewrite <- Hm42'.
    apply (typing_ann _ _ GT2 PI2 PI2').
    rewrite Hm42.
    assert (typ_open (typ_bvar m1) Us = U0).
      apply* extract_unique_attr.
      now rewrite H12, Cstr.unique_dom.
    simpl in H17; rewrite H17.
    assert (typ_open (typ_bvar m2) Us = T1).
      apply* extract_unique_attr.
      now rewrite H12, Cstr.unique_cod.
    simpl in H18; rewrite H18.
    eapply typing_gc_any, H21; auto.
  split.
    pick_freshes (length Ks) Xs.
    destruct* (H Xs).
    apply* kenv_ok_strengthen.
    rewrite* dom_kinds_open_vars.
  intros; subst.
  apply (typing_gc Ks (L \u dom K \u fv_in kind_fv K)).
    simpl*.
  intros.
  apply H; auto.
  apply* typing_weaken_kinds.
  destruct* (H Xs).
  (* ApplyAnn2 *)
- admit.
  (* AnnAbs1 *)
- admit.
  (* AnnAbs2 *)
- admit.
  (* Rigid *)
- apply* (@typing_rigid (true, GcAny) Q L).
  intros.
  apply* H3.
  apply* trm_open_rigid_red.
  (* AbsRigid *)
- admit.
  (* AppRigid *)
- admit.
  (* UseEq *)
- admit. (* destruct* Typ2.
  apply* (@typing_abs (true, GcAny) Q L K E U). inversion H1.
  admit. *)
  (* *)
- apply* typing_use. 
Admitted.

(* ********************************************************************** *)
(** Progress: typed terms are values or can reduce *)

Lemma value_app_const : forall t1 t2 n,
  valu n (trm_app t1 t2) ->
  exists c:Const.const, exists vl:list trm,
    length vl + n = Const.arity c /\ trm_app t1 t2 = const_app c vl /\
    list_forall value vl.
Proof.
  induction t1; intros; inversions H; try (inversion H3; fail).
    clear IHt1_2.
    destruct (IHt1_1 _ _ H3) as [c [vl [Hlen [Heq Hv]]]].
    exists c. exists (vl ++ t2 :: nil).
    split. rewrite app_length. rewrite <- Hlen. simpl. ring.
    split. rewrite Heq. unfold const_app.
      rewrite fold_left_app. simpl. auto.
    apply* list_forall_concat.
    constructor; auto. exists* n2.
  exists c. exists (t2 :: nil).
  inversions H3. rewrite H1.
  unfold const_app. simpl; auto.
  split3*. constructor; auto. exists* n2.
  admit.
  admit.
Admitted.

Lemma progress_delta : forall K t0 t3 t2 T,
  [ nil ; K; empty |(false,GcLet)|= trm_app (trm_app t0 t3) t2 ~: T ] ->
  valu 0 (trm_app t0 t3) ->
  value t2 ->
  exists t' : trm, trm_app (trm_app t0 t3) t2 --> t'.
Proof.
  intros.
  destruct (value_app_const H0) as [c [vl [Hlen [Heq Hv]]]].
  unfold const_app in *.
  rewrite Heq in *.
  change (exists t', fold_left trm_app (t2::nil) (const_app c vl) --> t').
  unfold const_app; rewrite <- fold_left_app.
  assert (list_for_n value (S(Const.arity c)) (vl ++ t2 :: nil)).
    split2*. apply* list_forall_app.
  exists (Delta.reduce H2).
  apply red_delta.
Qed.

Lemma progress_result : progress.
Proof.
  introv Typ. gen_eq (empty:env) as E. gen_eq (true,GcAny) as gc.
  poses Typ' Typ.
  induction Typ; intros; subst;
    try (pick_freshes (length Ks) Xs; apply* (H0 Xs)).
  inversions H1.
  left*. exists* 0.
  right*. pick_freshes (sch_arity M) Ys.
    destructi~ (@H0 Ys) as [[n Val1] | [t1' Red1]].
      assert (value t1). exists* n.
      exists* (t2 ^^ t1).
      exists* (trm_let t1' t2).
  destruct~ IHTyp2 as [Val2 | [t2' Red2]].
    destruct~ IHTyp1 as [Val1 | [t1' Red1]].
      use (typing_canonize Typ').
      remember (empty(A:=sch)) as E.
      remember (trm_app t1 t2) as t.
      clear Typ1 Typ2 Typ'.
      fold (typing_gc_let Q K E t T) in H3.
      apply (proj2 (A:=kenv_ok Q K)).
      induction H3 using typing_gc_ind.
        split2*; intros; subst.
        destruct Val1 as [n Val1]; inversions Val1.
        right*; exists* (t0 ^^ t2).
        case_eq (Const.arity c); intros.
          right*. rewrite H4 in Val1.
          assert (list_for_n value 1 (t2 :: nil)) by split2*.
          rewrite <- H4 in H5.
          exists (Delta.reduce H5).
          apply (red_delta H5).
        left*. exists n. rewrite H4 in Val1. destruct* Val2.
        destruct n.
          right*; apply* progress_delta.
          admit.
        left*. destruct Val2. exists* n.
        admit.
        
        inversion H13.
      destruct (var_freshes (L \u dom K) (length Ks)) as [Xs HXs].
      destruct* (H17 Xs).
      admit.
      right*; exists* (trm_app t1' t2).
    right*; exists* (trm_app t1 t2').
  left*; exists* (Const.arity c).
  destruct (var_freshes L (length Ks)) as [Xs HXs].
  apply* (H1 Xs).
Qed.

Lemma value_irreducible : forall t t',
  value t -> ~(t --> t').
Proof.
  induction t; introv HV; destruct HV as [k HV']; inversions HV';
    intro R; inversions R.
       destruct (const_app_inv c tl) as [eq | [t1' [t2' eq]]];
         rewrite eq in *; discriminate.
      inversions H2.
     destruct (value_app_const HV').
     destruct H as [vl' [Hl [He Hv]]].
     rewrite He in H0; clear He.
     destruct (const_app_eq _ _ _ _ H0). subst.
     clear -vl Hl; destruct vl.
     Lia.lia.
    elim (IHt1 t1'). exists* (S k). auto.
   elim (IHt2 t2'). exists* n2. auto.
  clear -vl H0.
  destruct vl.
  destruct (const_app_inv c0 tl) as [eq | [t1' [t2' eq]]];
    rewrite eq in *; discriminate.
Qed.

End Mk3.

End Mk2.

End MkSound.
