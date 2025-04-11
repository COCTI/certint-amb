(***************************************************************************
* Principality of unification for mini-ML with structural polymorphism     *
* Jacques Garrigue, July 2008                                              *
***************************************************************************)

Require Import Arith List Metatheory.
Require Import ML_SP_Definitions Cardinal ML_SP_Eval.
Require Omega.
Ltac omega := Omega.omega.

Set Implicit Arguments.

Module MkUnify(Cstr:CstrIntf)(Const:CstIntf).

Module MyEval := MkEval(Cstr)(Const).
Import MyEval.
Import Rename.
Import Sound.
Import Infra.
Import Defs.

(* Composition of substitutions *)
Definition compose S1 S2 : subs := S1 & map (typ_subst S1) S2.

(* Inclusion of substitutions. Very handy to use in proofs *)
Definition extends S S0 :=
  forall T, typ_subst S (typ_subst S0 T) = typ_subst S T.

Lemma extends_trans : forall S1 S2 S3,
  extends S1 S2 -> extends S2 S3 -> extends S1 S3.
Proof.
  intros; intro.
  rewrite <- H. rewrite <- (H T).
  rewrite* H0.
Qed.

(* Unifiers *)
Definition unifies S pairs :=
  forall T1 T2, In (T1, T2) pairs -> typ_subst S T1 = typ_subst S T2.

(* Subsititions should be in normal form *)
Definition is_subst (S : subs) :=
  env_prop (fun T => disjoint (dom S) (typ_fv T)) S.

Section Moregen.
  (* Here we relate extends with the more usual notional of generality *)

  Definition moregen S0 S :=
    exists S1, forall T, typ_subst S T = typ_subst S1 (typ_subst S0 T).

  (* Extends implies more general *)
  Lemma extends_moregen : forall S S0,
    extends S S0 -> moregen S0 S.
  Proof.
    intros.
    exists* S.
  Qed.

  Lemma typ_subst_idem : forall S T,
    is_subst S -> typ_subst S (typ_subst S T) = typ_subst S T.
  Proof.
    intros.
    induction T; simpl. auto.
      case_eq (get v S); intros.
        rewrite* typ_subst_fresh.
      simpl.
      rewrite* H0.
    simpl; congruence.
  Qed.

  (* For substitutions in normal form, moregeneral implies extends *)
  Lemma moregen_extends : forall S S0,
    moregen S0 S -> is_subst S0 -> extends S S0.
  Proof.
    intros; intro.
    destruct H as [S1 Heq].
    rewrite Heq.
    rewrite* typ_subst_idem.
  Qed.

End Moregen.

Fixpoint unify_kind_rel (kr kr':list(Cstr.attr*typ)) (uniq:Cstr.attr -> bool)
  (pairs:list(typ*typ)) {struct kr} :=
  match kr with
  | nil => (kr', pairs)
  | (l,T)::krem =>
    if uniq l then
      match assoc Cstr.eq_dec l kr' with
      | None => unify_kind_rel krem ((l,T)::kr') uniq pairs
      | Some T' => unify_kind_rel krem kr' uniq ((T,T')::pairs)
      end
    else unify_kind_rel krem ((l,T)::kr') uniq pairs
  end.

Fixpoint remove_env (A:Set) (E:Env.env A) (x:var) {struct E} : Env.env A :=
  match E with
  | nil => nil
  | (y,a)::E' =>
    if x == y then E' else (y,a) :: remove_env E' x
  end.

Lemma unify_coherent : forall kc kr,
  coherent kc (fst (unify_kind_rel kr nil (Cstr.unique kc) nil)).
Proof.
  intros until kr.
  set (kr' := @nil (Cstr.attr*typ)).
  set (pairs' := @nil (typ*typ)).
  assert (coherent kc kr'). intro; intros. elim H0.
  gen kr' pairs'.
  induction kr; simpl; intros. auto.
  destruct a.
  case_eq (Cstr.unique kc a); introv R.
    case_eq (assoc Cstr.eq_dec a kr'); introv R1. apply* IHkr.
    apply IHkr.
    intro; intros.
    simpl in *; destruct H1; [inversions H1|]; destruct H2. inversions* H2.
        elim (assoc_complete _ _ _ _ R1 H2).
      inversions H2; elim (assoc_complete _ _ _ _ R1 H1).
    apply* (H x).
  apply IHkr.
  intro; intros.
  simpl in *.
  destruct (Cstr.eq_dec x a).
    subst. rewrite R in H0; discriminate.
  apply* (H x). destruct* H1. inversions* H1.
  destruct* H2. inversions* H2.
Qed.

Definition unify_kinds (k1 k2:kind) : option (kind * list (typ*typ)).
  intros.
  refine (
  match k1, k2 with
  | None, _ => Some (k2, nil)
  | Some _, None => Some (k1, nil)
  | Some (@Kind kc1 kv1 kr1 kh1), Some (@Kind kc2 kv2 kr2 kh2) =>
    let kc := Cstr.lub kc1 kc2 in
    if Cstr.valid_dec kc then
      let krp := unify_kind_rel (kr1 ++ kr2) nil (Cstr.unique kc) nil in
      Some (Some (@Kind kc _ (fst krp) _), snd krp)
    else None
  end).
    auto.
  unfold krp; apply unify_coherent.
Defined.

Definition get_kind x E : kind :=
  match get x E with
  | Some k  => k
  | None => None
  end.

Lemma binds_get_kind : forall x k K,
  binds x k K -> get_kind x K = k.
Proof.
  intros.
  unfold get_kind. rewrite* H.
Qed.

Lemma get_kind_binds : forall x k K,
  get_kind x K = Some k -> binds x (Some k) K.
Proof.
  unfold get_kind; intros.
  case_rewrite R (get x K).
  subst*.
Qed.
Hint Resolve get_kind_binds : core.

Definition unify_vars (K:kenv) (x y:var) :=
  match unify_kinds (get_kind x K) (get_kind y K) with
  | Some (k, pairs) => Some (remove_env (remove_env K x) y & y ~ k, pairs)
  | None => None
  end.

Definition unify_nv (unify : kenv -> subs -> option (kenv * subs)) K S x T :=
  if S.mem x (typ_fv T) then None else
    match get_kind x K with
    | Some _ => None
    | None => unify (remove_env K x) (compose (x ~ T) S)
    end.

Fixpoint unify0 unify (h:nat) (pairs:list(typ*typ)) (K:kenv) (S:subs) {struct h}
  : option (kenv * subs) :=
  match h with 0 => None
  | S h' =>
    match pairs with
    | nil => Some (K,S)
    | (T1,T2) :: pairs' =>
      match typ_subst S T1, typ_subst S T2 with
      | typ_bvar n, typ_bvar m =>
        if n === m then unify0 unify h' pairs' K S else None
      | typ_fvar x, typ_fvar y =>
        if x == y then unify0 unify h' pairs' K S else
        match unify_vars K x y with
        | Some (K', pairs) =>
          unify (pairs ++ pairs') K' (compose (x ~ typ_fvar y) S)
        | None => None
        end
      | typ_fvar x, T =>
        unify_nv (unify pairs') K S x T 
      | T, typ_fvar x =>
        unify_nv (unify pairs') K S x T 
       | typ_arrow T11 T12, typ_arrow T21 T22 =>
        unify0 unify h' ((T11,T21)::(T12,T22)::pairs') K S
      | _, _ =>
        None
      end
    end
  end.

Section Accum.
  Variables A B : Type.
  Variables (f : A -> B) (op : B->B->B) (unit : B).

  Fixpoint accum (l:list A) {struct l} : B :=
    match l with
    | nil => unit
    | a::rem => op (f a) (accum rem)
    end.

  Variable op_assoc : forall a b c, op a (op b c) = op (op a b) c.
  Variable op_unit : forall a, op unit a = a.

  Lemma accum_app : forall l2 l1,
    accum (l1 ++ l2) = op (accum l1) (accum l2).
  Proof.
    induction l1; simpl. rewrite* op_unit.
    rewrite <- op_assoc.
    rewrite* IHl1.
  Qed.

End Accum.

Fixpoint all_types S (pairs:list(typ*typ)) {struct pairs} : list typ :=
  match pairs with
  | nil => nil
  | p::rem =>
      typ_subst S (fst p) :: typ_subst S (snd p) :: all_types S rem
  end.

Fixpoint typ_size (T : typ) : nat :=
  match T with
  | typ_arrow T1 T2 => S (typ_size T1 + typ_size T2)
  | _ => 1
  end.

Definition pairs_size S pairs := accum typ_size plus 0 (all_types S pairs).

Fixpoint unify (h:nat) (pairs:list (typ*typ)) (K:kenv) (S:subs) {struct h} :=
  match h with
  | 0 => None
  | S h' => unify0 (unify h') (pairs_size S pairs + 1) pairs K S
  end.

Lemma typ_subst_compose : forall S1 S2 T,
  typ_subst (compose S1 S2) T = typ_subst S1 (typ_subst S2 T).
Proof.
  induction T; simpl; intros; auto.
    unfold compose.
    simpl; case_eq (get v S2); intros.
      rewrite* (binds_prepend S1 (binds_map (typ_subst S1) H)).
    simpl.
    case_eq (get v S1); intros.
      rewrite* (binds_concat_fresh (map (typ_subst S1) S2) H0).
    case_eq (get v (S1 & map (typ_subst S1) S2)); intros; auto.
    destruct (binds_concat_inv H1).
      destruct H2. rewrite H3 in H0. discriminate.
    destruct (binds_map_inv _ _ H2).
    rewrite (proj2 H3) in H; discriminate.
  rewrite* IHT1.
  rewrite* IHT2.
Qed.

Lemma binds_typ_subst : forall x T S,
  binds x T S -> typ_subst S (typ_fvar x) = T.
Proof.
  intros. simpl. rewrite* H.
Qed.

Lemma disjoint_subst : forall x T L T',
  disjoint ({{x}} \u L) (typ_fv T) ->
  disjoint L (typ_fv T') ->
  disjoint ({{x}} \u L) (typ_fv (typ_subst (x ~ T) T')).
Proof.
  induction T'; simpl; intros; auto.
    destruct* (v == x).
    simpl*.
  forward~ IHT'1 as HT1.
  forward~ IHT'2 as HT2.
Qed.

Lemma add_binding_is_subst : forall S x T,
  is_subst S ->
  disjoint (dom S) (typ_fv T) ->
  x \notin (typ_fv T) ->
  is_subst (compose (x ~ T) S).
Proof.
  intros.
  unfold compose.
  intro; intros.
  rewrite dom_concat; rewrite dom_map.
  simpl. rewrite union_empty_r.
  destruct (in_app_or _ _ _ H2).
    destruct (in_map_inv _ _ _ _ H3) as [b [F B']].
    subst.
    use (H _ _ B').
    simpl in *.
    apply* disjoint_subst.
  simpl in H3. destruct* H3.
  inversions* H3.
Qed.

Hint Resolve add_binding_is_subst : core.

Lemma typ_subst_disjoint : forall S T,
  is_subst S -> disjoint (dom S) (typ_fv (typ_subst S T)).
Proof.
  intros; induction T; simpl in *; auto.
  case_eq (get v S); intros.
    use (H _ _ (binds_in H0)).
  simpl*.
Qed.

Lemma typ_subst_res_fresh : forall S T T',
  is_subst S -> typ_subst S T = T' -> disjoint (dom S) (typ_fv T').
Proof.
  intros.
  use (typ_subst_disjoint T H).
  rewrite* <- H0.
Qed.

Lemma typ_subst_res_fresh' : forall S T v,
  is_subst S -> typ_subst S T = typ_fvar v -> v # S.
Proof.
  intros.
  use (typ_subst_res_fresh _ H H0).
Qed.

Hint Resolve typ_subst_disjoint typ_subst_res_fresh typ_subst_res_fresh' : core.

Lemma binds_add_binding : forall S T0 T1 v x T,
  typ_subst S T0 = typ_fvar v ->
  binds x (typ_subst S T) S ->
  binds x (typ_subst (compose (v ~ T1) S) T) (compose (v ~ T1) S).
Proof.
  intros.
  rewrite typ_subst_compose.
  unfold compose.
  apply binds_prepend.
  apply* binds_map.
Qed.

Hint Resolve binds_add_binding : core.

Definition id := Env.empty (A:=typ).

Lemma typ_subst_id : forall T, typ_subst id T = T.
Proof.
  intro.
  apply* typ_subst_fresh.
Qed.

Lemma is_subst_id : is_subst id.
Proof.
  unfold id, is_subst. intro; intros. simpl*.
Qed.

Lemma dom_remove_env : forall (A:Set) v (K:Env.env A),
  ok K -> dom (remove_env K v) = S.remove v (dom K).
Proof.
  induction K; simpl; intros.
    apply eq_ext; intros; split; intro; auto.
  destruct a.
  inversions H.
  destruct (v == v0).
    subst v0.
    rewrite remove_union.
    rewrite remove_single. rewrite* remove_notin. rewrite* union_empty_l.
  simpl.
  rewrite remove_union.
  rewrite* IHK.
  assert (v \notin {{v0}}) by auto.
  rewrite* (remove_notin H0).
Qed.

Lemma ok_remove_env : forall (A:Set) v (E:Env.env A),
  ok E -> ok (remove_env E v).
Proof.
  induction E; simpl; intros. auto.
  destruct a.
  inversions H.
  destruct* (v == v0).
  apply* ok_cons.
  clear -H4.
  induction E; simpl. simpl in H4. auto.
  destruct a.
  simpl in H4.
  destruct* (v == v1).
  simpl. 
  apply* notin_union_l.
Qed.

Hint Resolve ok_remove_env : core.

Lemma binds_remove_env : forall (A:Set) v K x (a:A),
  binds x a K -> x <> v -> binds x a (remove_env K v).
Proof.
  unfold binds; induction K; simpl; intros. auto.
  destruct a; simpl in *.
  destruct (x == v0).
    destruct (v == v0). subst. elim H0; auto.
    simpl. destruct* (x == v0).
  destruct* (v == v0).
  simpl. destruct* (x == v0).
Qed.

Hint Resolve binds_remove_env : core.

Lemma disjoint_add_binding : forall v T S (K:kenv),
  is_subst S -> ok K ->
  disjoint (dom S) (dom K) ->
  disjoint (dom (compose (v ~ T) S)) (dom (remove_env K v)).
Proof.
  intros.
  rewrite* dom_remove_env.
  unfold compose.
  rewrite dom_concat.
  simpl; rewrite* dom_map.
Qed.

Hint Resolve disjoint_add_binding : core.

Definition kind_entails k k' :=
  match k' with
  | None => True
  | Some c' => match k with
               | Some c => entails c c'
               | None => False
               end
  end.

Lemma kind_entails_well_kinded : forall k k' K T,
  kind_entails k k' ->
  well_kinded K k T ->
  well_kinded K k' T.
Proof.
  unfold kind_entails; intros.
  inversions H0; clear H0; destruct* k'; try apply wk_any.
  apply (wk_kind H1). apply (entails_trans H2 H).
Qed.

Hint Resolve kind_entails_well_kinded : core.

Lemma neq_notin_fv : forall v v0,
  v <> v0 -> v \notin (typ_fv (typ_fvar v0)).
Proof. simpl*. Qed.

Hint Resolve neq_notin_fv : core.

Section Soundness.

Variables (K':kenv) (S':subs).

Lemma unify_ind : forall (P : kenv -> subs -> list (typ * typ) -> Prop),
  (is_subst S' -> P K' S' nil) ->
  (forall h pairs K T S v t t0,
    let S1 := compose (v ~ T) S in
    let K1 := remove_env K v in
    unify h pairs K1 S1 = Some (K', S') ->
    typ_subst S t = typ_fvar v ->
    typ_subst S t0 = T ->
    is_subst S -> is_subst S1 ->
    v \notin typ_fv T -> get_kind v K = None ->
    P K1 S1 pairs -> P K S ((t,t0)::pairs)) ->
  (forall h pairs K S v v0 k l t t0,
    let S1 := compose (v ~ typ_fvar v0) S in
    let K1 := remove_env (remove_env K v) v0 & v0 ~ k in
    unify_kinds (get_kind v K) (get_kind v0 K) = Some (k, l) ->
    unify h (l ++ pairs) K1 S1 = Some (K', S') ->
    typ_subst S t = typ_fvar v ->
    typ_subst S t0 = typ_fvar v0 ->
    is_subst S -> is_subst S1 ->
    v <> v0 ->
    P K1 S1 (l ++ pairs) -> P K S ((t,t0)::pairs)) ->
  (forall h h0 K S t t0 pairs n,
    unify0 (unify h) h0 pairs K S = Some (K', S') -> is_subst S ->
    typ_subst S t = typ_bvar n ->
    typ_subst S t0 = typ_bvar n ->
    P K S pairs -> P K S ((t,t0)::pairs)) ->
  (forall h h0 K S t t0 pairs v,
    unify0 (unify h) h0 pairs K S = Some (K', S') -> is_subst S ->
    typ_subst S t = typ_fvar v ->
    typ_subst S t0 = typ_fvar v ->
    P K S pairs -> P K S ((t,t0)::pairs)) ->
  (forall h h0 K S t t0 pairs t1 t2 t3 t4,
    unify0 (unify h) h0 ((t1,t3)::(t2,t4)::pairs) K S = Some (K',S') ->
    is_subst S ->
    typ_subst S t = typ_arrow t1 t2 ->
    typ_subst S t0 = typ_arrow t3 t4 ->
    P K S ((t1,t3)::(t2,t4)::pairs) -> P K S ((t,t0)::pairs)) ->
  (forall K S t t0 pairs,
    P K S ((t,t0)::pairs) -> P K S ((t0,t)::pairs)) ->
  forall h pairs K S,
    unify h pairs K S = Some (K', S') ->
    is_subst S ->
    P K S pairs.
Proof.
  introv Hnil Hnv Hvars Hbv Hfv. intros Harr Hsw.
  induction h; simpl; intros pairs K S HU HS.
    discriminate.
  set (h0 := pairs_size S pairs + 1) in HU. clearbody h0.
  gen pairs; induction h0; simpl; intros.
    discriminate.
  destruct pairs.
    inversions HU.
    auto.
  destruct p.
  assert (Hnv1: forall v T t t0,
    typ_subst S t = typ_fvar v -> typ_subst S t0 = T ->
    unify_nv (unify h pairs) K S v T = Some (K',S') ->
    P K S ((t,t0)::pairs)).
    unfold unify_nv; simpl. introv R1 R2 H'.
    case_rewrite R3 (S.mem v (typ_fv T)).
    fold kind in *.
    case_rewrite R4 (get_kind v K).
    apply* Hnv.
  case_rewrite R1 (typ_subst S t); case_rewrite R2 (typ_subst S t0).
        destruct (n === n0).
          subst n0.
          auto*.
        discriminate.
       rewrite <- R1 in HU.
       apply Hsw.
       apply* Hnv1.
      rewrite <- R2 in HU.
      apply* Hnv1.
     destruct (v == v0).
       subst v0. auto*.
     unfold unify_vars in HU.
     case_rewrite R3 (unify_kinds (get_kind v K) (get_kind v0 K)).
     destruct p.
     apply* Hvars.
    rewrite <- R2 in HU.
    apply* Hnv1.
   rewrite <- R1 in HU.
   apply Hsw.
   apply* Hnv1.
  apply* Harr.
Qed.

Lemma unify_keep : forall h pairs K S,
  unify h pairs K S = Some (K', S') ->
  is_subst S ->
  is_subst S' /\
  forall x T, binds x (typ_subst S T) S -> binds x (typ_subst S' T) S'.
Proof.
  intros.
  apply* (unify_ind
    (fun K S _ => is_subst S' /\
      forall x T, binds x (typ_subst S T) S -> binds x (typ_subst S' T) S'));
    clear H H0 h pairs K S; intros.
    destruct H6; split2*.
    intros. apply H7.
    apply* binds_add_binding.
  intros.
  intuition.
  apply H8. apply* binds_add_binding.
Qed.

Lemma binds_subst_idem : forall x T S,
  binds x T S -> is_subst S -> binds x (typ_subst S T) S.
Proof.
  intros.
  use (binds_typ_subst H).
  use (f_equal (typ_subst S) H1).
  rewrite typ_subst_idem in H2; auto.
  congruence.
Qed.
Hint Resolve binds_subst_idem : core.

Lemma typ_subst_extend : forall h pairs K S,
  is_subst S ->
  unify h pairs K S = Some (K', S') ->
  extends S' S.
Proof.
  intros.
  destruct* (unify_keep _ _ _ H0).
  clear H0.
  intro.
  induction T. simpl*.
    remember (typ_subst S (typ_fvar v)) as T'.
    use (f_equal (typ_subst S) HeqT').
    rewrite typ_subst_idem in H0; auto.
    simpl in H0.
    case_rewrite R (get v S).
      subst.
      use (H2 _ _ R).
      rewrite* (binds_typ_subst H0).
    simpl in HeqT'. rewrite R in HeqT'. subst*.
  simpl. congruence.
Qed.

Hint Resolve typ_subst_extend : core.

Lemma typ_size_1 : forall T, 1 <= typ_size T.
  destruct T; simpl; omega.
Qed.

Lemma pairs_size_decr : forall S t t0 pairs,
  Datatypes.S (pairs_size S pairs) < pairs_size S ((t,t0)::pairs).
Proof.
  intros.
  unfold pairs_size; simpl.
  puts (typ_size_1 (typ_subst S t)).
  puts (typ_size_1 (typ_subst S t0)).
  omega.
Qed.

Lemma unify0_unify : forall h0 h K S K' S' pairs,
  unify0 (unify h) h0 pairs K S = Some (K', S') ->
  is_subst S ->
  unify (Datatypes.S h) pairs K S = Some (K', S').
Proof.
  intros.
  simpl.
  set (h1 := pairs_size S pairs + 1).
  assert (pairs_size S pairs < h1) by (unfold h1; omega).
  clearbody h1.
  gen pairs h1; induction h0; simpl; intros. discriminate.
  destruct h1. exfalso; omega.
  simpl.
  destruct pairs. auto.
  destruct p.
  puts (pairs_size_decr S t t0 pairs).
  case_rewrite R1 (typ_subst S t); case_rewrite R2 (typ_subst S t0); auto.
      destruct* (n === n0).
    destruct* (v == v0).
  apply~ IHh0.
  clear IHh0 H H2; unfold pairs_size in *; simpl in *.
  rewrite <- (typ_subst_idem t H0) in H1.
  rewrite <- (typ_subst_idem t0 H0) in H1.
  rewrite R1 in H1; rewrite R2 in H1. simpl in H1.
  puts (typ_size_1 (typ_subst S t1)).
  puts (typ_size_1 (typ_subst S t2)).
  puts (typ_size_1 (typ_subst S t3)).
  puts (typ_size_1 (typ_subst S t4)).
  omega.
Qed.

Theorem unify_types : forall h pairs K S,
  unify h pairs K S = Some (K',S') ->
  is_subst S ->
  unifies S' pairs.
Proof.
  intros.
  apply* (unify_ind (fun _ _ => unifies S')); clear H H0 h K S pairs; intros;
    intro; simpl; intros; intuition;
    try (unfold S1 in *; inversions H8; clear H8);
    try (poses HU (unify0_unify _ _ _ _ H H0));
    try (inversions H5; clear H5; rewrite <- (typ_subst_extend _ _ _ H0 HU);
         rewrite <- (typ_subst_extend _ _ _ H0 HU T2); congruence).
        rewrite <- (typ_subst_extend _ _ _ H3 H).
        rewrite <- (typ_subst_extend _ _ _ H3 H T2).
        rewrite typ_subst_compose. rewrite H0.
        simpl. destruct* (v == v).
        rewrite typ_subst_compose.
        rewrite* (typ_subst_fresh (v ~ typ_subst S T2)).
        simpl*. disjoint_solve. intuition.
      rewrite <- (typ_subst_extend _ _ _ H4 H0).
      rewrite <- (typ_subst_extend _ _ _ H4 H0 T2).
      do 2 rewrite typ_subst_compose. rewrite H1; rewrite H2.
      simpl. destruct* (v == v). destruct* (v0 == v).
    inversions H5; clear H5.
    rewrite <- (typ_subst_extend _ _ _ H0 HU).
    rewrite <- (typ_subst_extend _ _ _ H0 HU T2).
    rewrite H2; rewrite H1.
    simpl.
    rewrite* (H3 t1 t3).
    rewrite* (H3 t2 t4).
  inversions H1.
  symmetry.
  apply* H.
Qed.

Lemma kind_subst_idem : forall S k,
  is_subst S -> kind_subst S (kind_subst S k) = kind_subst S k.
Proof.
  intros.
  destruct k as [[kc kv kr kh]|].
    simpl.
    apply* kind_pi; simpl.
    clear kh; induction kr; simpl. auto.
    rewrite IHkr.
    rewrite* typ_subst_idem.
  auto.
Qed.

Lemma kind_subst_combine : forall S S1 S2 k,
  (forall T, typ_subst S1 (typ_subst S2 T) = typ_subst S T) ->
  kind_subst S1 (kind_subst S2 k) = kind_subst S k.
Proof.
  intros.
  destruct k as [[kc kv kr kh]|].
    simpl; apply* kind_pi; simpl.
    clear kv kh.
    induction kr. auto.
    simpl. rewrite IHkr. rewrite* H.
  auto.
Qed.

Lemma binds_orig_remove_env : forall (A:Set) v x (k:A) E,
  ok E -> binds x k (remove_env E v) -> binds x k E.
Proof.
  unfold binds.
  induction E; simpl; intros. auto.
  destruct a.
  inversions H.
  destruct (v == v0); simpl in H0.
    subst.
    destruct* (x == v0).
    subst. elim (binds_fresh H0 H5).
  destruct* (x == v0).
Qed.

Lemma get_kind_subst : forall S x K,
  get_kind x (map (kind_subst S) K) = kind_subst S (get_kind x K).
Proof.
  unfold get_kind; intros.
  case_eq (get x K); introv R1.
    rewrite* (binds_map (kind_subst S) R1).
  rewrite* (map_get_none (kind_subst S) _ _ R1).
Qed.

Lemma unify_kind_rel_keep : forall kr kr' uniq pairs k' l,
  unify_kind_rel kr kr' uniq pairs = (k', l) ->
  incl kr' k' /\ incl pairs l.
Proof.
  induction kr; simpl; intros. inversions H. split2*.
  destruct a.
  case_rewrite R (uniq a).
    case_rewrite R1 (assoc Cstr.eq_dec a kr'); destruct* (IHkr _ _ _ _ _ H).
  destruct* (IHkr _ _ _ _ _ H).
Qed.

Lemma unify_kind_rel_incl : forall kr pairs uniq S kr0 kr' pairs',
  unify_kind_rel kr0 kr' uniq pairs' = (kr, pairs) ->
  unifies S pairs ->
  incl (map_snd (typ_subst S) kr0) (map_snd (typ_subst S) kr).
Proof.
  induction kr0; intros; intros T HT. elim HT.
  destruct T.
  destruct a.
  simpl in *.
  case_rewrite R (uniq a);
    try case_rewrite R1 (assoc Cstr.eq_dec a kr'); simpl in HT; destruct HT;
      try solve [apply* (IHkr0 _ _ H)]; inversions H1; clear H1;
        destruct (unify_kind_rel_keep _ _ _ _ H).
      puts (H1 _ (assoc_sound _ _ _ R1)); clear H1.
      assert (In (t0,t1) pairs) by auto*.
      use (H0 _ _ H1).
      rewrite* H4.
    apply* in_map_snd.
  apply* in_map_snd.
Qed.

Lemma unify_kinds_sound : forall k k0 k1 l S,
  unify_kinds k k0 = Some (k1, l) ->
  unifies S l ->
  kind_entails (kind_subst S k1) (kind_subst S k) /\
  kind_entails (kind_subst S k1) (kind_subst S k0).
Proof.
  unfold unify_kinds, kind_entails.
  intros.
  destruct k as [[kc kv kr kh]|]; destruct k0 as [[kc0 kv0 kr0 kh0]|]; simpl.
     destruct (Cstr.valid_dec (Cstr.lub kc kc0)); try discriminate.
     case_eq (unify_kind_rel (kr ++ kr0) nil (Cstr.unique (Cstr.lub kc kc0))
       nil); intros l0 l1 R1.
     inversions H; clear H.
     rewrite R1 in *.
     use (unify_kind_rel_incl _ _ _ _ R1 H0).
     destruct (proj2 (Cstr.entails_lub kc kc0 _) (Cstr.entails_refl _)).
     split; split2*; simpl; intros;
       rewrite R1; apply H; unfold map_snd; rewrite* map_app.
    split2*.
    inversions H; clear H.
    simpl. apply entails_refl.
   split2*.
   inversions H; clear H.
   simpl. apply entails_refl.
  auto.
Qed.

Lemma map_remove_env : forall (A:Set) x f (E:Env.env A),
  map f (remove_env E x) = remove_env (map f E) x.
Proof.
  induction E; simpl in *. auto.
  destruct a; simpl.
  destruct (x == v); simpl*.
  rewrite* IHE.
Qed.

Lemma map_map_env : forall (A:Set) f f1 f2 (E:Env.env A),
  (forall x, f x = f1 (f2 x)) -> map f E = map f1 (map f2 E).
Proof.
  intros; induction E; simpl. auto.
  destruct a; simpl.
  rewrite H.
  rewrite* IHE.
Qed.

Lemma fv_in_remove_env : forall (A:Set) (fv:A->vars) x E,
  fv_in fv (remove_env E x) << fv_in fv E.
Proof.
  induction E; simpl; intros. auto.
  destruct a. destruct* (x == v); simpl*.
Qed.

Lemma unify_kinds_subst : forall k1 k2 k3 l S,
  unify_kinds k1 k2 = Some (k3, l) ->
  unify_kinds (kind_subst S k1) (kind_subst S k2) =
  Some (kind_subst S k3,
        List.map (fun T => (typ_subst S (fst T), typ_subst S (snd T))) l).
Proof.
  intros.
  destruct k1 as [[kc1 kv1 kr1 kh1]|]; destruct k2 as [[kc2 kv2 kr2 kh2]|];
    simpl in *; try solve [inversions* H].
  destruct (Cstr.valid_dec (Cstr.lub kc1 kc2)); try discriminate.
  inversions H; clear H.
  unfold map_snd; rewrite <- map_app.
  fold (map_snd (typ_subst S) (kr1++kr2)).
  simpl.
  refine (f_equal (@Some _) _).
  set (kr:=@nil(Cstr.attr*typ)).
  set (pairs:=@nil(typ*typ)).
  assert (kr = map_snd (typ_subst S) kr) by reflexivity.
  assert (pairs =
    List.map (fun T => (typ_subst S (fst T), typ_subst S (snd T))) pairs)
    by reflexivity.
  clear kh1 kh2.
  apply injective_projections; simpl; try apply kind_pi; simpl*;
    pattern kr at 1; rewrite H;
    pattern pairs at 1; rewrite H0; clear H H0;
    gen kr pairs; induction (kr1++kr2); intros; simpl*; destruct a;
    simpl; destruct (Cstr.unique (Cstr.lub kc1 kc2) a);
    try rewrite* <- IHl;
    case_eq (assoc Cstr.eq_dec a kr); intros; rewrite <- IHl;
    try rewrite* (assoc_map _ (typ_subst S) _ _ H).
Qed.

Lemma well_subst_unify : forall k1 l v v0 S K h pairs,
  unify h (l ++ pairs) (remove_env (remove_env K v) v0 & v0 ~ k1)
    (compose (v ~ typ_fvar v0) S) = Some (K', S') ->
  unify_kinds (get_kind v K) (get_kind v0 K) = Some (k1, l) ->
  is_subst (compose (v ~ typ_fvar v0) S) ->
  v # S ->
  well_subst (remove_env (remove_env K v) v0 & v0 ~ k1)
     (map (kind_subst S') K') S' ->
  well_subst K (map (kind_subst S') K') S'.
Proof.
  intros until 1; intros HU HS1 Hv WS x; intros.
  unfold well_subst in WS.
  poses Hext (typ_subst_extend _ _ _ HS1 H).
  poses Hunif (unify_types _ _ _ H HS1). 
  assert (Hunif': unifies S' l) by (intro; intros; auto).
  clear HS1 H.
  destruct (x == v0); subst.
    destruct* (unify_kinds_sound _ _ HU Hunif') as [_ Wk].
    rewrite* <- (binds_get_kind H0).
  destruct (x == v); subst.
    assert (well_kinded (map (kind_subst S') K') (kind_subst S' k1)
               (typ_subst S' (typ_fvar v))).
      rewrite <- Hext.
      rewrite* typ_subst_compose.
      rewrite (typ_subst_fresh S); simpl*.
      destruct* (v == v).
    destruct* (unify_kinds_sound _ _ HU Hunif') as [Wk _].
    rewrite* <- (binds_get_kind H0).
  assert (x # v0 ~ k1) by simpl*.
  use (binds_concat_fresh _ (binds_remove_env (binds_remove_env H0 n0) n) H).
Qed.

Lemma unify_kinds_ok : forall h pairs K S,
  unify h pairs K S = Some (K',S') -> is_subst S ->
  ok K -> disjoint (dom S) (dom K) ->
  ok K' /\ disjoint (dom S') (dom K') /\
  well_subst K (map (kind_subst S') K') S'.
Proof.
  introv H H0.
  apply* (unify_ind (fun K S pairs =>
    ok K -> disjoint (dom S) (dom K) ->
    ok K' /\ disjoint (dom S') (dom K') /\
    well_subst K (map (kind_subst S') K') S'));
    clear H H0 h pairs K S.
      intuition.
      intro; intros.
      rewrite* typ_subst_fresh.
      destruct* k.
      use (binds_map (kind_subst S') H2).
      apply* wk_kind.
    intros until 1.
    intros R1 R2 Hs HS1 n R3 IHh HK Dis.
    subst S1 K1.
    destruct* IHh.
    intuition.
    clear -R3 H3.
    intro; intros.
    destruct (Z == v).
      subst.
      rewrite (binds_get_kind H) in R3. subst*.
    use (H3 _ _ (binds_remove_env H n)).
  intros until K1.
  intros R3 H R1 R2 HS HS1 n IHh HK Dis.
  subst S1 K1.
  destruct~ IHh.
      constructor. repeat apply ok_remove_env. auto.
      rewrite* dom_remove_env.
    simpl.
    repeat rewrite* dom_remove_env.
    unfold compose.
    rewrite dom_concat. rewrite dom_map. simpl.
    use (typ_subst_res_fresh' _ HS R2).
  intuition.
  subst; apply* well_subst_unify.
  apply* typ_subst_res_fresh'.
Qed.

End Soundness.

Lemma typ_subst_map_idem : forall S,
  is_subst S -> ok S -> map (typ_subst S) S = S.
Proof.
  intros.
  remember S as S0.
  pattern S0 at 1.
  rewrite HeqS0.
  assert (env_prop (fun T => typ_subst S T = T) S0).
    intro; intros.
    rewrite <- HeqS0.
    rewrite <- (binds_typ_subst (in_ok_binds _ _ H1 H0)).
    apply* typ_subst_idem.
  clear HeqS0 H.
  induction S0. auto.
  inversions H0.
  simpl. rewrite (H1 x a0).
    rewrite* IHS0.
    intro; intros.
    apply (H1 x0 a).
    simpl.
    destruct* (x0 == x).
  simpl*.
Qed.

Lemma typ_subst_prebind : forall v T S T1,
  typ_subst S T = typ_subst S (typ_fvar v) ->
  typ_subst S (typ_subst (v~T) T1) = typ_subst S T1.
Proof.
  induction T1; intros.
      simpl*.
    simpl. destruct (v0 == v).
      subst*.
    reflexivity.
  simpl.
  rewrite* IHT1_1. rewrite* IHT1_2.
Qed.

Section Mgu.

Variables (K':kenv) (S':subs) (HS' : is_subst S').

Definition mgu_spec K S K0 S0 pairs :=
  ok K0 ->
  extends S' S0 ->
  unifies S' pairs ->
  well_subst K0 K' S' ->
  extends S' S /\ well_subst K K' S'.

Lemma get_remove_env : forall (A:Set) v (E:Env.env A),
  ok E -> get v (remove_env E v) = None.
Proof.
  induction E; simpl; intros. auto.
  destruct a. destruct* (v == v0).
    subst v0; inversions H.
    case_eq (get v E); intros. elim (binds_fresh H0 H4). auto.
  simpl. destruct* (v == v0). inversions* H.
Qed.

Lemma kind_subst_compose : forall S1 S2 k,
  kind_subst (compose S1 S2) k = kind_subst S1 (kind_subst S2 k).
Proof.
  intros; symmetry; apply kind_subst_combine.
  intro; symmetry; apply* typ_subst_compose.
Qed.

Lemma unify_mgu_nv : forall K0 S0 pairs K S h t t0 v T,
  let S1 := compose (v ~ T) S0 in
  let K1 := remove_env K0 v in
  unify h pairs K1 S1 = Some (K, S) ->
  typ_subst S0 t = typ_fvar v ->
  typ_subst S0 t0 = T ->
  is_subst S0 ->
  get_kind v K0 = None ->
  mgu_spec K S K1 S1 pairs ->
  mgu_spec K S K0 S0 ((t, t0) :: pairs).
Proof.
  intros until K1; unfold K1, S1; clear K1 S1.
  intros HU R1 R2 HS0 R4 IHh HK0 Hext Heq WS.
  assert (BS': typ_subst S' T = typ_subst S' (typ_fvar v)).
    rewrite <- R2. rewrite Hext. rewrite* <- (Heq t t0).
    rewrite <- R1. rewrite* Hext.
  assert (Hv: v # S0) by apply* typ_subst_res_fresh'.
  assert (Dis: disjoint (dom (v ~ T)) (dom S0)) by simpl*.
  assert (Sv: extends S' (v ~ T)).
    intro.
    induction T0; simpl. auto.
      destruct (v0 == v). subst. rewrite BS'. reflexivity.
      reflexivity.
    congruence.
  destruct* IHh.
      intro. rewrite* typ_subst_compose.
      rewrite Sv. apply Hext.
    intro; intros. apply* Heq.
  intro; intros.
  destruct (Z == v).
    subst.
    elim (binds_fresh H).
    fold S.elt in v.
    rewrite* dom_remove_env.
  apply WS.
  apply* binds_orig_remove_env.
Qed.

Lemma unify_kinds_complete : forall k k0 k' S,
  kind_entails k' (kind_subst S k) ->
  kind_entails k' (kind_subst S k0) ->
  exists k1, exists l,
    unify_kinds k k0 = Some (k1, l) /\
    unifies S l /\ kind_entails k' (kind_subst S k1).
Proof.
  unfold unify_kinds, unifies.
  intros.
  destruct k as [[kc kv kr kh]|]; destruct k0 as [[kc0 kv0 kr0 kh0]|];
    simpl in *;
    try solve [esplit; esplit; intuition; elim H1].
  destruct k' as [[kc' kv' kr' kh']|]; try contradiction.
  destruct H. destruct H0.
  simpl in H, H0.
  destruct (Cstr.entails_lub kc kc0 kc').
  use (H3 (conj H H0)).
  use (Cstr.entails_valid H5 kv').
  destruct* (Cstr.valid_dec (Cstr.lub kc kc0)).
  esplit. esplit. split. reflexivity.
  (* poses Huniq (Cstr.entails_unique H5). *)
  clear H H0 H3 H4 H6.
  simpl in H1, H2. clear kv kv0 kh kh0.
  set (pairs := nil(A:=typ*typ)).
  set (krs := nil(A:=Cstr.attr*typ)).
  assert (forall T,
          In T (map_snd (typ_subst S) ((kr ++ kr0) ++ krs)) -> In T kr').
    intros.
    unfold map_snd in H; repeat rewrite map_app in H.
    destruct (in_app_or _ _ _ H).
      destruct* (in_app_or _ _ _ H0).
    elim H0.
  clear H1 H2.
  assert (Hunif: unifies S pairs) by (intros T1 T2 HE; elim HE).
  unfold kind_entails, entails; simpl.
  intros; gen pairs krs; induction (kr++kr0); simpl; intros. auto.
  destruct a.
  case_eq (Cstr.unique (Cstr.lub kc kc0) a); introv R.
    puts (Cstr.entails_unique H5 R).
    case_eq (assoc Cstr.eq_dec a krs); [intros t0 R1|intros R1].
      assert (unifies S ((t,t0)::pairs)).
        intro; simpl; intros.
        destruct H1; [|auto*].
        inversions H1; clear H1.
        apply* (kh' a).
        apply H.
        right*.
        unfold map_snd; rewrite map_app.
        use (in_map_snd (typ_subst S) _ _ _ (assoc_sound _ _ _ R1)).
      intuition.
        refine (proj1 (IHl _ _ _ _) _ _ H2); auto.
      refine (proj2 (proj2 (IHl _ _ _ _)) _ H2); auto.
    intuition;
      [ refine (proj1 (IHl _ _ _ _) _ _ H1)
      | refine (proj2 (proj2 (IHl _ _ _ _)) _ H1)];
      auto; simpl; intros;
      unfold map_snd in *;
      repeat rewrite map_app in *; apply H; apply* in_app_mid.
  unfold map_snd in *.
  intuition;
  [ refine (proj1 (IHl _ _ _ _) _ _ H0)
  | refine (proj2 (proj2 (IHl _ _ _ _)) _ H0)];
  auto; simpl; intros;
  repeat rewrite map_app in *; apply H; apply* in_app_mid.
Qed.

Lemma well_kinded_get_kind : forall K x,
  well_kinded K (get_kind x K) (typ_fvar x).
Proof.
  intros.
  case_eq (get_kind x K); intros; auto*.
Qed.

Lemma well_subst_get_kind : forall K K' S x,
  well_subst K K' S ->
  well_kinded K' (kind_subst S (get_kind x K)) (typ_subst S (typ_fvar x)).
Proof.
  intros.
  case_eq (get_kind x K); intros.
    apply H. apply* get_kind_binds.
  apply wk_any.
Qed.

Lemma unify_mgu_vars : forall K0 S0 pairs K S h t t0 v v0 k l,
  let S1 := compose (v ~ typ_fvar v0) S0 in
  let K1 := remove_env (remove_env K0 v) v0 & v0 ~ k in
  unify_kinds (get_kind v K0) (get_kind v0 K0) = Some (k, l) ->
  unify h (l ++ pairs) K1 S1 = Some (K, S) ->
  typ_subst S0 t = typ_fvar v ->
  typ_subst S0 t0 = typ_fvar v0 ->
  is_subst S0 -> is_subst S1 -> v <> v0 ->
  mgu_spec K S K1 S1 (l ++ pairs) -> mgu_spec K S K0 S0 ((t, t0) :: pairs).
Proof.
  intros until K1; unfold S1; clear S1.
  intros R4 HU R1 R2 HS0 HS1 n IHh HK0 Hext Heq WS.
  assert (BS': typ_subst S' (typ_fvar v0) = typ_subst S' (typ_fvar v)).
    rewrite <- R1; rewrite <- R2.
    repeat rewrite Hext.
    symmetry; apply* Heq.
  assert (Hv: v # S0) by apply* typ_subst_res_fresh'.
  assert (Hv0: v0 # S0) by apply* typ_subst_res_fresh'.
  assert (Dis: disjoint (dom (v ~ typ_fvar v0)) (dom S0))
    by (clear -Hv; simpl*).
  assert (Sv: extends S' (v ~ typ_fvar v0)).
    intro. induction T; simpl. auto.
      destruct (v1 == v). subst. rewrite BS'. reflexivity.
      reflexivity.
    congruence.
  assert (HK1: ok K1).
    unfold K1.
    assert (ok (remove_env K0 v)) by auto.
    apply (@ok_push _ _ v0 k (ok_remove_env v0 H)).
    rewrite* dom_remove_env.
  poses Wk (well_subst_get_kind v WS).
  rewrite <- Sv in Wk.
  simpl typ_subst in Wk. destruct* (v == v). clear e.
  poses Wk0 (well_subst_get_kind v0 WS).
  assert (Hke: forall v1, typ_subst S' (typ_fvar v0) = typ_fvar v1 ->
               let k' := get_kind v1 K' in
               let gk x := kind_subst S' (get_kind x K0) in
               kind_entails k' (gk v) /\ kind_entails k' (gk v0)).
    intros.
    split; [inversions Wk | inversions Wk0]; simpl*; unfold k', gk;
      try (rewrite <- H2; simpl* );
      rewrite <- H0; simpl in H; rewrite H in H1; inversions H1;
      rewrite* (binds_get_kind H3).
  assert (Hk: k = None /\ l = nil \/
              exists v1, typ_subst S' (typ_fvar v0) = typ_fvar v1).
    case_rewrite R5 (typ_subst S' (typ_fvar v0));
    case_rewrite R6 (get_kind v0 K0);
    simpl in Wk0 ; inversion_clear Wk0;
    case_rewrite R7 (get_kind v K0);
    simpl in Wk; inversion_clear Wk;
    simpl in R4; inversion* R4.
  destruct* IHh.
      intro.
      rewrite* typ_subst_compose.
      rewrite Sv. rewrite* Hext.
    intro; intros.
    destruct (in_app_or _ _ _ H); clear H; try solve [apply* Heq].
    destruct Hk as [[_ Hl]|[v1 R5]]. subst; elim H0.
    destruct* (Hke v1); clear Hke.
    destruct (unify_kinds_complete _ _ _ _ H H1) as [k3 [l3 [HU1 [HU2 HU3]]]].
    rewrite R4 in HU1.
    clearbody K1.
    inversions HU1; clear HU1.
    apply* HU2.
  intro; intros.
  destruct (Z == v0).
    subst.
    unfold binds in H; simpl in H; destruct* (v0 == v0).
    clearbody K1.
    inversions H; clear e H.
    destruct Hk as [[Hk _]|[v1 R5]]. subst*.
    rewrite R5.
    destruct* (Hke v1); clear Hke.
    destruct (unify_kinds_complete _ _ _ _ H H0) as [k3 [l3 [HU1 [HU2 HU3]]]].
    rewrite R4 in HU1.
    inversions HU1; clear HU1.
    apply* kind_entails_well_kinded.
    apply* well_kinded_get_kind.
  destruct* k0.
  unfold K1 in H.
  unfold binds in H; simpl in H. destruct* (Z == v0). clear n1.
  use (binds_orig_remove_env _ (ok_remove_env v HK0) H).
  use (binds_orig_remove_env _ HK0 H0).
Qed.

Lemma unifies_tl : forall S p pairs,
  unifies S (p::pairs) -> unifies S pairs.
Proof.
  intros; intro; intros; apply* H.
Qed.

Hint Resolve unifies_tl : core.

Lemma unify_mgu0 : forall h pairs K0 S0 K S,
  unify h pairs K0 S0 = Some (K,S) -> is_subst S0 ->
  mgu_spec K S K0 S0 pairs.
Proof.
  intros.
  apply* (unify_ind (K':=K) (S':=S) (mgu_spec K S));
    clear H H0 K0 S0 pairs h.
        unfold mgu_spec; auto*.
       intros; unfold K1, S1 in *; apply* unify_mgu_nv.
      intros; unfold K1, S1 in *; apply* unify_mgu_vars.
     unfold mgu_spec; intros; apply* H3.
    unfold mgu_spec; intros; apply* H3.
   unfold mgu_spec; intros. apply* H3.
   assert (Heq: typ_subst S' t = typ_subst S' t0).
     apply* H6.
   rewrite <- (H5 t) in Heq.
   rewrite <- (H5 t0) in Heq.
   rewrite H1 in Heq; rewrite H2 in Heq; simpl in Heq.
   inversions Heq.
   intro; intros.
   destruct H8. inversions* H8.
   destruct* H8. inversions* H8.
  unfold mgu_spec; intros.
  apply* H.
  intro; intros.
  destruct* H4.
  inversions H4. symmetry; apply* H2.
Qed.

Theorem unify_mgu : forall h T1 T2 K0 K S,
  unify h ((T1,T2)::nil) K0 id = Some (K, S) ->
  ok K0 ->
  typ_subst S' T1 = typ_subst S' T2 ->
  well_subst K0 K' S' ->
  (forall T3 T4,
    typ_subst S T3 = typ_subst S T4 -> typ_subst S' T3 = typ_subst S' T4) /\
  well_subst K K' S'.
Proof.
  intros.
  destruct* (unify_mgu0 _ H is_subst_id).
      intro. rewrite* typ_subst_id.
    intro; simpl; intros.
    destruct* H3.
    inversions* H3.
  split2*.
  intros.
  rewrite <- (H3 T3).
  rewrite <- (H3 T4).
  rewrite* H5.
Qed.

End Mgu.

Definition all_fv S pairs :=
  accum typ_fv S.union {} (all_types S pairs).

Definition really_all_fv S K pairs :=
  fv_in kind_fv (map (kind_subst S) K) \u all_fv S pairs.

Definition size_pairs S K pairs :=
  S.cardinal (really_all_fv S K pairs).

Lemma typ_fv_decr : forall v T S T1,
  v # S -> disjoint (typ_fv T) ({{v}} \u dom S) ->
  typ_fv (typ_subst (compose (v ~ T) S) T1) <<
  S.remove v (typ_fv T \u typ_fv (typ_subst S T1)).
Proof.
  intros.
  rewrite* typ_subst_compose.
  induction (typ_subst S T1); simpl in *; disjoint_solve.
  destruct* (v0 == v).
Qed.

Lemma kind_fv_decr : forall v T S k,
  v # S -> disjoint (typ_fv T) ({{v}} \u dom S) ->
  kind_fv (kind_subst (compose (v ~ T) S) k) <<
  S.remove v (typ_fv T \u kind_fv (kind_subst S k)).
Proof.
  intros.
  unfold kind_fv.
  destruct k as [[kc kv kr kh]|]; simpl*.
  clear kc kv kh.
  induction kr; simpl*.
  sets_solve.
  use (typ_fv_decr _ _ _ H H0 H1).
Qed.

Lemma fv_in_decr : forall (A:Set) v T S (E:Env.env A) fv (sub:subs -> A -> A),
  v # S -> disjoint (typ_fv T) ({{v}} \u dom S) ->
  (forall a,
    fv (sub (compose (v ~ T) S) a) << S.remove v (typ_fv T \u fv (sub S a))) ->
  fv_in fv (map (sub (compose (v ~ T) S)) E) <<
  S.remove v (typ_fv T \u fv_in fv (map (sub S) E)).
Proof.
  intros.
  induction E; simpl*; intros.
  destruct a.
  simpl.
  use (H1 a).
Qed.

Lemma all_fv_decr : forall v T S pairs,
  v # S -> disjoint (typ_fv T) ({{v}} \u dom S) ->
  all_fv (compose (v ~ T) S) pairs <<
  S.remove v (all_fv S ((typ_fvar v, T) :: pairs)).
Proof.
  unfold all_fv.
  induction pairs; intros; simpl*.
  rewrite* get_notin_dom.
  sets_solve.
    puts (typ_fv_decr _ _ _ H H0 H1).
    rewrite* (@typ_subst_fresh S T).
   puts (typ_fv_decr _ _ _ H H0 H2).
   rewrite* (@typ_subst_fresh S T).
  use (IHpairs H H0 _ H2).
  simpl in H1.
  rewrite get_notin_dom in H1; auto.
Qed.

Lemma really_all_fv_decr : forall S K pairs v T,
  v # S -> disjoint (typ_fv T) ({{v}} \u dom S) -> ok K ->
  really_all_fv (compose (v ~ T) S) K pairs <<
  S.remove v (really_all_fv S K ((typ_fvar v, T) :: pairs)).
Proof.
  intros until T. intros Hv Dis HK.
  unfold really_all_fv.
  sets_solve.
    unfold all_fv; simpl. rewrite* get_notin_dom.
    repeat rewrite union_assoc.
    rewrite* typ_subst_fresh.
    forward~ (fv_in_decr _ _ K kind_fv kind_subst Hv Dis); intros.
        apply* kind_fv_decr.
      apply H.
    auto*.
  use (all_fv_decr _ _ _ Hv Dis H).
Qed.

Lemma cardinal_decr : forall v T S K pairs,
  v # S -> disjoint (typ_fv T) ({{v}} \u dom S) -> ok K ->
  S.cardinal (really_all_fv (compose (v ~ T) S) (remove_env K v) pairs) <
  S.cardinal (really_all_fv S K ((typ_fvar v, T) :: pairs)).
Proof.
  intros.
  puts (really_all_fv_decr (pairs:=pairs) _ _ H H0 H1).
  puts (PeanoNat.le_lt_n_Sm _ _ (cardinal_subset H2)).
  rewrite cardinal_remove in H3.
    eapply Nat.le_lt_trans; try apply H3.
    apply cardinal_subset.
    unfold really_all_fv. rewrite map_remove_env.
    sets_solve.
    apply S.union_2. refine (fv_in_remove_env _ _ _ H4).
    auto.
  unfold really_all_fv, all_fv; simpl.
  rewrite* get_notin_dom.
Qed.

Lemma size_pairs_decr : forall v T K S pairs,
  v # S -> ok K ->
  disjoint (typ_fv T) ({{v}} \u dom S) ->
  size_pairs (compose (v ~ T) S) (remove_env K v) pairs <
  size_pairs S K ((typ_fvar v,T)::pairs).
Proof.
  intros.
  unfold size_pairs.
  apply* cardinal_decr.
Qed.

Lemma size_pairs_comm : forall S K T1 T2 pairs,
  size_pairs S K ((T1,T2)::pairs) = size_pairs S K ((T2,T1)::pairs).
Proof.
  intros; unfold size_pairs, really_all_fv, all_fv; simpl.
  rewrite (union_assoc (typ_fv (typ_subst S T1))).
  rewrite (union_comm (typ_fv (typ_subst S T1))).
  repeat rewrite union_assoc. auto.
Qed.

Lemma size_pairs_decr' : forall S0 K0 t t0 pairs h v,
  is_subst S0 -> ok K0 ->
  S.mem v (typ_fv (typ_subst S0 t0)) = false ->
  size_pairs S0 K0 ((t, t0) :: pairs) < S h ->
  typ_subst S0 t = typ_fvar v ->
  size_pairs (compose (v ~ typ_subst S0 t0) S0) (remove_env K0 v) pairs < h.
Proof.
  intros.
  puts (typ_subst_res_fresh' _ H H3).
  puts (typ_subst_disjoint t0 H).
  eapply Nat.lt_le_trans.
    apply* size_pairs_decr.
  replace (size_pairs S0 K0 ((typ_fvar v, typ_subst S0 t0) :: pairs))
    with (size_pairs S0 K0 ((t, t0) :: pairs)).
    omega.
  unfold size_pairs, really_all_fv, all_fv; simpl.
  rewrite* get_notin_dom.
  rewrite H3.
  rewrite* typ_subst_idem.
Qed.

Lemma all_types_app : forall S l1 l2,
  all_types S (l1 ++ l2) = all_types S l1 ++ all_types S l2.
Proof.
  intros; induction l1; simpl. auto.
  rewrite* <- IHl1.
Qed.

Lemma get_kind_fv_in : forall S v K,
  kind_fv (kind_subst S (get_kind v K)) << fv_in kind_fv (map (kind_subst S) K).
Proof.
  induction K; simpl. apply subset_refl.
  unfold get_kind; simpl.
  destruct a. destruct (v == v0).
    simpl*.
  fold (get_kind v K).
  simpl*.
Qed.

Lemma in_typ_fv : forall t l,
  In t l -> typ_fv t << typ_fv_list l.
Proof.
  induction l; simpl; intros H x Hx. elim H.
  destruct* H.
  subst; simpl*.
Qed.

Lemma unify_kinds_fv : forall k k0 k1 l S,
  unify_kinds k k0 = Some (k1, l) ->
  kind_fv (kind_subst S k1) \u all_fv S l <<
  kind_fv (kind_subst S k) \u kind_fv (kind_subst S k0).
Proof.
  unfold unify_kinds; intros.
  destruct k as [[kc kv kr kh]|].
    destruct k0 as [[kc0 kv0 kr0 kh0]|].
      destruct (Cstr.valid_dec (Cstr.lub kc kc0)); try discriminate.
      inversions H; clear H.
      simpl.
      unfold kind_fv; simpl.
      repeat rewrite list_snd_map_snd.
      rewrite <- fv_list_map.
      unfold list_snd; rewrite <- map_app.
      set (pairs := nil(A:=typ*typ)).
      set (kr' := nil(A:=Cstr.attr*typ)).
      intros x Hx.
      rewrite <- union_empty_r.
      replace {} with (typ_fv_list (List.map (typ_subst S) (list_snd kr')))
        by reflexivity.
      rewrite <- union_empty_r.
      replace {} with (all_fv S pairs) by reflexivity.
      clearbody pairs kr'.
      rewrite <- map_app.
      gen pairs kr'; induction (kr ++ kr0); simpl; intros.
        now rewrite <- union_assoc, union_empty_l.
      destruct a; simpl in *.
      case_rewrite R (Cstr.unique (Cstr.lub kc kc0) a).
        case_rewrite R1 (assoc Cstr.eq_dec a kr');
          poses Hsub (IHl _ _ Hx); clear -Hsub R1.
          unfold all_fv in *; simpl in *.
          sets_solve.
          puts (assoc_sound _ _ _ R1).
          puts (in_map_snd (typ_subst S) _ _ _ H0).
          rewrite <- combine_fst_snd in H1.
          puts (in_combine_r _ _ _ _ H1).
          rewrite list_snd_map_snd in H2.
          use (in_typ_fv _ _ H2 H).
        simpl in Hsub. auto.
      poses Hsub (IHl _ _ Hx); clear -Hsub.
      simpl in Hsub; auto.
    inversions H.
    unfold kind_fv, all_fv; simpl*.
  inversions H.
  unfold kind_fv, all_fv; simpl*.
Qed.

Lemma all_fv_app : forall S l1 l2,
  all_fv S (l1 ++ l2) = all_fv S l1 \u all_fv S l2.
Proof.
  intros.
  unfold all_fv.
  induction l1; simpl. rewrite* union_empty_l.
  rewrite IHl1.
  repeat rewrite union_assoc. auto.
Qed.

Lemma size_pairs_decr_vars : forall S0 K0 t t0 pairs h v v0 x0 l,
  is_subst S0 -> ok K0 ->
  size_pairs S0 K0 ((t, t0) :: pairs) < S h ->
  typ_subst S0 t = typ_fvar v ->
  typ_subst S0 t0 = typ_fvar v0 ->
  v <> v0 ->
  unify_kinds (get_kind v K0) (get_kind v0 K0) = Some (x0, l) ->
  size_pairs (compose (v ~ typ_fvar v0) S0)
    (remove_env (remove_env K0 v) v0 & v0 ~ x0) (l ++ pairs) < h.
Proof.
  intros.
  puts (typ_subst_res_fresh' _ H H3).
  poses Hv (typ_subst_res_fresh' _ H H2).
  puts (typ_subst_disjoint t0 H).
  eapply Nat.lt_le_trans; [| apply (PeanoNat.lt_n_Sm_le _ _ H1)].
  clear H1.
  unfold size_pairs.
  assert (v \in really_all_fv S0 K0 ((t,t0)::pairs)).
    unfold really_all_fv, all_fv.
    simpl. rewrite H2. simpl*.
  rewrite <- (cardinal_remove H1). clear H1.
  simpl.
  set (S := compose (v ~ typ_fvar v0) S0).
  poses Hfv (unify_kinds_fv _ _ S H5).
  apply PeanoNat.le_lt_n_Sm.
  apply cardinal_subset.
  sets_solve.
  replace (really_all_fv S0 K0 ((t, t0) :: pairs))
    with (really_all_fv S0 K0 ((typ_fvar v, typ_fvar v0) :: pairs)).
    apply* really_all_fv_decr.
    fold S.
    unfold really_all_fv in *.
    simpl in *.
    rewrite all_fv_app in Hy.
    do 2 rewrite map_remove_env in Hy.
    sets_solve; try use (get_kind_fv_in _ _ _ H1).
    apply S.union_2.
    refine (fv_in_remove_env _ v _ _); auto.
    refine (fv_in_remove_env _ v0 _ _); auto.
  unfold really_all_fv, all_fv.
  rewrite <- H2; rewrite <- H3.
  simpl.
  repeat rewrite* typ_subst_idem.
Qed.

Lemma typ_subst_no_cycle : forall v S T,
  v \in typ_fv T ->
  1 < typ_size T ->
  typ_size (typ_subst S (typ_fvar v)) < typ_size (typ_subst S T).
Proof.
  induction T; intros. elim (in_empty H).
    simpl in H0. omega.
  simpl in H.
  clear H0.
  assert (forall T, v \in typ_fv T -> T = T1 \/ T = T2 ->
             typ_size (typ_subst S (typ_fvar v)) <
             typ_size (typ_subst S (typ_arrow  T1 T2))).
    intros.
    case_eq (typ_size T); intros. destruct T; discriminate.
    destruct n. destruct T. elim (in_empty H0).
        rewrite (S.singleton_1 H0) in H1.
        destruct H1; subst; simpl; omega.
      destruct T3; simpl in H2; omega.
    assert (typ_size (typ_subst S (typ_fvar v)) < typ_size (typ_subst S T)).
      assert (1 < typ_size T) by omega.
      destruct H1; subst*.
    destruct H1; subst; simpl in *; omega.
  destruct (S.union_1 H); apply* (H0 _ H1).
Qed.

Section Completeness.

Variables (K:kenv) (S:subs).

Definition complete_spec S0 K0 pairs h :=
  is_subst S0 -> ok K0 ->
  extends S S0 ->
  unifies S pairs ->
  well_subst K0 K S ->
  size_pairs S0 K0 pairs < h ->
  unify h pairs K0 S0 <> None.

Lemma unify_complete_nv : forall pairs K0 S0 v T h t t0,
  typ_subst S0 t = typ_fvar v ->
  typ_subst S0 t0 = T ->
  size_pairs S0 K0 ((t,t0)::pairs) < Datatypes.S h ->
  is_subst S0 -> ok K0 ->
  well_subst K0 K S ->
  (forall K0 S0, complete_spec K0 S0 pairs h) ->
  extends S S0 ->
  unifies S ((t, t0) :: pairs) ->
  (forall x, T <> typ_fvar x) ->
  unify_nv (unify h pairs) K0 S0 v T <> None.
Proof.
  intros until t0; intros R1 R2 Hsz HS0 HK0 WS IHh Hext Heq HT.
  unfold unify_nv.
  assert (In (t,t0) ((t,t0)::pairs)) by simpl*.
  puts (Heq _ _ H); clear H.
  rewrite <- Hext in H0; rewrite R1 in H0.
  rewrite <- (Hext t0) in H0; rewrite R2 in H0.
  case_eq (S.mem v (typ_fv T)); intros.
    exfalso.
    puts (S.mem_2 H).
    clear -H0 H1 HT.
    destruct T. elim (in_empty H1).
      elim (HT v); rewrite* (S.singleton_1 H1).
    assert (1 < typ_size (typ_arrow T1 T2)).
      destruct T1; simpl; omega.
    puts (typ_subst_no_cycle S _ H1 H).
    rewrite H0 in H2; omega.
  intro.
  case_rewrite R3 (get_kind v K0).
    poses Wk (WS _ _ (get_kind_binds _ _ R3)).
    rewrite H0 in Wk.
    simpl in Wk; inversions Wk.
    clear -H3 HT.
    destruct (typ_subst S0 t0); try discriminate.
    elim (HT v). auto.
  rewrite <- R2 in H.
  puts (size_pairs_decr' HS0 HK0 H Hsz R1).
  rewrite R2 in H2.
  puts (typ_subst_res_fresh' _ HS0 R1).
  rewrite R2 in H.
  revert H1; apply* IHh; clear IHh.
      intro. rewrite* typ_subst_compose.
      rewrite typ_subst_prebind. apply Hext. congruence.
    intro; auto*.
  clear H0.
  intro; intros.
  destruct k; try (simpl; apply wk_any).
  destruct (v == Z).
    elim (binds_fresh H0).
    rewrite* dom_remove_env. apply* S.remove_1.
  apply WS.
  apply* binds_orig_remove_env.
Qed.

Lemma well_kinded_kind_entails: forall K k x,
  well_kinded K k (typ_fvar x) -> kind_entails (get_kind x K) k.
Proof.
  intros; unfold kind_entails.
  inversions H. auto.
  rewrite* (binds_get_kind H1).
Qed.

Lemma unify_complete_vars : forall h t t0 pairs K0 S0 v v0,
  is_subst S0 -> ok K0 ->
  extends S S0 ->
  unifies S ((t, t0) :: pairs) ->
  well_subst K0 K S ->
  size_pairs S0 K0 ((t, t0) :: pairs) < Datatypes.S h ->
  typ_subst S0 t = typ_fvar v ->
  typ_subst S0 t0 = typ_fvar v0 ->
  v <> v0 ->
  (forall pairs K0 S0, complete_spec S0 K0 pairs h) ->
  match unify_vars K0 v v0 with
  | Some (pair K' pairs0) =>
    unify h (pairs0 ++ pairs) K' (compose (v ~ typ_fvar v0) S0)
  | None => None (A:=kenv * subs)
  end <> None.
Proof.
  intros until v0; intros HS0 HK0 Hext Heq WS Hsz R1 R2 n IHh.
  unfold unify_vars.
  poses Hv (typ_subst_res_fresh' _ HS0 R1).
  poses Wk (well_subst_get_kind v WS).
  poses Wk0 (well_subst_get_kind v0 WS).
  set (S0' := compose (v ~ typ_fvar v0) S0) in *.
  assert (HS0': is_subst S0') by (unfold S0'; auto*).
  assert (HK0': forall y, ok (remove_env (remove_env K0 v) v0 & v0 ~ y)).
    puts (ok_remove_env v HK0).
    constructor. apply* ok_remove_env.
    rewrite* dom_remove_env.
  assert (Hext': forall T, typ_subst S (typ_subst S0' T) = typ_subst S T).
    intros. unfold S0'. rewrite* typ_subst_compose.
    rewrite typ_subst_prebind. apply Hext.
    rewrite <- R1; rewrite <- R2.
    symmetry; repeat rewrite Hext; apply* Heq.
  assert (Sv_Sv0 : typ_subst S (typ_fvar v) = typ_subst S (typ_fvar v0)).
    rewrite <- R1; rewrite <- R2.
    repeat rewrite Hext. apply* Heq.
  assert (get_kind v K0 = None /\ get_kind v0 K0 = None \/
        exists v1, typ_subst S (typ_fvar v0) = typ_fvar v1
          /\ kind_entails (get_kind v1 K) (kind_subst S (get_kind v K0))
          /\ kind_entails (get_kind v1 K) (kind_subst S (get_kind v0 K0))).
    case_rewrite R3 (get_kind v0 K0).
      inversions Wk0. right*; exists x. rewrite H0; split2*.
      simpl in Wk0; rewrite <- H0 in Wk0.
      rewrite Sv_Sv0 in Wk; simpl in Wk; rewrite <- H0 in Wk.
      split; apply* well_kinded_kind_entails.
    case_rewrite R4 (get_kind v K0).
      inversions Wk. right*; exists x.
      rewrite <- Sv_Sv0; rewrite H0.
      split2*.
      split; apply well_kinded_kind_entails.
      rewrite* H0.
      apply wk_any.
    left*.
  destruct H as [[G G0]|[v1 [Hv1 [KEv KEv0]]]].
    rewrite G; rewrite G0.
    simpl unify_kinds. lazy iota beta.
    apply~ IHh.
        intro; auto*.
      intro; intros.
      binds_cases H.
        puts (binds_orig_remove_env _ (ok_remove_env v HK0) B).
        destruct (Z == v).
          subst. elim (binds_fresh H).
          rewrite dom_remove_env. apply S.remove_1. reflexivity. auto.
        use (binds_orig_remove_env _ HK0 H).
      subst. apply wk_any.
    unfold S0'. apply* size_pairs_decr_vars.
    rewrite G; rewrite G0; reflexivity.
  destruct (unify_kinds_complete _ _ _ _ KEv KEv0)
    as [k1 [l [HU [Heql KEk1]]]].
  rewrite HU.
  apply~ IHh.
      intro; intros. destruct* (in_app_or _ _ _ H).
    intro; intros.
    binds_cases H.
      apply WS.
      apply* binds_orig_remove_env.
      apply* binds_orig_remove_env.
    subst.
    rewrite Hv1.
    case_rewrite R3 (get_kind v1 K).
      destruct* k1.
    destruct* (kind_subst S k1).
  unfold S0'; apply* size_pairs_decr_vars.
Qed.

Lemma size_pairs_tl : forall S K t t0 pairs,
  size_pairs S K pairs <= size_pairs S K ((t,t0)::pairs).
Proof.
  unfold size_pairs, really_all_fv, all_fv; simpl.
  intros. apply* cardinal_subset.
Qed.

Lemma unify_complete0 : forall h pairs K0 S0,
  complete_spec S0 K0 pairs h.
Proof.
  induction h.
    intros; intro; intros; exfalso; omega.
  intros; intros HS0 HK0 Hext Heq WS Hsz.
  simpl.
  set (h0 := pairs_size S0 pairs + 1).
  assert (Hsz0: pairs_size S0 pairs < h0) by (unfold h0; omega).
  clearbody h0.
  gen pairs; induction h0; intros.
    exfalso; omega.
  destruct pairs.
    intro; discriminate.
  destruct p.
  simpl unify0.
  assert (Heq0: unifies S pairs) by (intro; auto*).
  case_eq (typ_subst S0 t); introv R1; case_eq (typ_subst S0 t0); introv R2.
          destruct (n === n0).
           subst.
           apply~ (IHh0 pairs).
             puts (size_pairs_tl S0 K0 t t0 pairs). omega.
           puts (pairs_size_decr S0 t t0 pairs). omega.
          assert (In (t,t0) ((t,t0)::pairs)) by simpl*.
          poses Ht (Heq _ _ H).
          rewrite <- Hext in Ht; rewrite R1 in Ht.
          rewrite <- (Hext t0) in Ht; rewrite R2 in Ht.
          simpl in Ht. inversions* Ht.
         rewrite size_pairs_comm in Hsz.
         apply~ (unify_complete_nv R2 R1 Hsz).
           intro; simpl; intros. destruct H; subst.
             inversions H; symmetry; apply* Heq.
           apply* Heq.
         intros x Hx; discriminate.
        assert (In (t,t0) ((t,t0)::pairs)) by simpl*.
        poses Ht (Heq _ _ H).
        rewrite <- Hext in Ht; rewrite R1 in Ht.
        rewrite <- (Hext t0) in Ht; rewrite R2 in Ht.
        simpl in Ht; inversions Ht.
       apply~ (unify_complete_nv R1 R2 Hsz).
       intros x Hx; discriminate.
      destruct (v == v0).
       subst.
       apply~ (IHh0 pairs).
         puts (size_pairs_tl S0 K0 t t0 pairs). omega.
       puts (pairs_size_decr S0 t t0 pairs). omega.
      apply* unify_complete_vars.
     apply~ unify_complete_nv; eauto.
     intro; discriminate.
    assert (In (t,t0) ((t,t0)::pairs)) by auto*.
    poses E (Heq _ _ H).
    rewrite <- (Hext t) in E. rewrite R1 in E.
    rewrite <- (Hext t0) in E. rewrite R2 in E.
    discriminate.
   rewrite size_pairs_comm in Hsz.
   apply~ unify_complete_nv; eauto.
     intro; simpl; intros. destruct H; subst.
       inversions H; symmetry; apply* Heq.
     apply* Heq.
   intro; discriminate.
  apply~ IHh0.
    clear IHh Hsz; intro; intros.
    assert (In (t,t0) ((t,t0)::pairs)) by auto*.
    puts (Heq _ _ H0).
    rewrite <- (Hext t) in H1.
    rewrite <- (Hext t0) in H1.
    rewrite R1 in H1; rewrite R2 in H1.
    simpl in H1; inversions H1.
    simpl in H; destruct H. inversions* H.
    destruct H. inversions* H.
    apply* Heq.
   eapply Nat.le_lt_trans; [|apply Hsz].
   unfold size_pairs, really_all_fv, all_fv.
   simpl.
   rewrite <- (typ_subst_idem t HS0).
   rewrite <- (typ_subst_idem t0 HS0).
   rewrite R1; rewrite R2; simpl.
   rewrite (union_assoc (typ_fv (typ_subst S0 t3))).
   rewrite (union_comm (typ_fv (typ_subst S0 t3))).
   repeat rewrite union_assoc. 
   omega.
  eapply Nat.lt_le_trans; [|apply PeanoNat.lt_n_Sm_le, Hsz0].
  unfold pairs_size; simpl.
  rewrite <- (typ_subst_idem t HS0).
  rewrite <- (typ_subst_idem t0 HS0).
  rewrite R1; rewrite R2; simpl.
  omega.
Qed.

Theorem unify_complete : forall T1 T2 K0,
  ok K0 -> well_subst K0 K S ->
  typ_subst S T1 = typ_subst S T2 ->
  unify (1 + size_pairs id K0 ((T1,T2)::nil)) ((T1,T2)::nil) K0 id <> None.
Proof.
  intros.
  apply* unify_complete0.
      apply is_subst_id.
    intro; rewrite* typ_subst_id.
  intro; intros; simpl in H2; destruct* H2.
  inversions* H2.
Qed.

End Completeness.

End MkUnify.
