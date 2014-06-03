
(** Proof of correctness of a persistent union-find data structure.
    See http://www.lri.fr/~filliatr/puf/ *)

(** 1. Persistent arrays *)

Set Implicit Arguments.
Unset Standard Proposition Elimination Names.
Require Export Wf_nat.
Require Export ZArith.
Open Scope Z_scope.

(** Polymorphic pointer map for the memory model *)

Parameter pointer : Set.

Module PM.
  Parameter t : Set -> Set.
  Parameter find : forall a, t a -> pointer -> option a.
  Parameter add : forall a, t a -> pointer -> a -> t a.
  Parameter new : forall a, t a -> pointer.

  Axiom find_add_eq : 
    forall a, forall m:t a, forall p:pointer, forall v:a,
    find (add m p v) p = Some v.
  Axiom find_add_neq : 
    forall a, forall m:t a, forall p p':pointer, forall v:a,
    ~p'=p -> find (add m p v) p' = find m p'.
  Axiom find_new :
    forall a, forall m:t a, find m (new m) = None.

End PM.

Lemma old_is_not_new : 
  forall a, forall m:PM.t a, forall p, PM.find m p <> None -> p <> PM.new m.
Proof.
  intros a m p hp1 hp2.
  generalize (PM.find_new m); subst p; assumption.
Qed.

(** memory model for datatypes t = data ref and data = ... *)
Inductive data : Set :=
  | Array : data
  | Diff  : Z -> Z -> pointer -> data.

Record mem : Set := { ref : PM.t data; arr : Z->Z }.

Definition upd (f:Z->Z) (i:Z) (v:Z) := 
  fun j => if Z_eq_dec j i then v else f j.
Axiom upd_ext : forall f g:Z->Z, (forall i, f i = g i) -> f=g.

Lemma upd_eq : forall f i j v, i=j -> upd f i v j = v.
Proof.
  intros; unfold upd; case (Z_eq_dec j i); auto.
  intro; absurd (i=j); auto.
Qed.
Ltac upd_eq := rewrite upd_eq; auto.

Lemma upd_neq : forall f i j v, i<>j -> upd f i v j = f j.
Proof.
  intros; unfold upd; case (Z_eq_dec j i); auto.
  intro; absurd (i=j); auto.
Qed.
Ltac upd_neq := rewrite upd_neq; auto.

(* the property of being a well-formed persistent array:
   from a given pointer, there is a finite Diff chain ending on Array *)
Inductive pa_valid (m: mem) : pointer -> Prop :=
  | array_pa_valid :
     forall p, PM.find (ref m) p = Some Array -> pa_valid m p
  | diff_pa_valid :
     forall p i v p', PM.find (ref m) p = Some (Diff i v p') ->
     pa_valid m p' -> pa_valid m p.

Inductive pa_model (m: mem) : pointer -> (Z -> Z) -> Prop :=
  | pa_model_array :
     forall p, PM.find (ref m) p = Some Array -> pa_model m p (arr m)
  | pa_model_diff :
     forall p i v p', PM.find (ref m) p = Some (Diff i v p') ->
     forall f, pa_model m p' f -> pa_model m p (upd f i v).

Lemma pa_model_pa_valid :
  forall m p f, pa_model m p f -> pa_valid m p.
Proof.
  induction 1.
  apply array_pa_valid; auto.
  apply diff_pa_valid with (i:=i) (v:=v) (p':=p'); auto.
Qed.
Hint Resolve pa_model_pa_valid.

Lemma pa_valid_pa_model :
  forall m p, pa_valid m p -> exists f, pa_model m p f.
Proof.
  induction 1.
  exists (arr m); apply pa_model_array; auto.
  destruct IHpa_valid.
  exists (upd x i v); apply pa_model_diff with (i:=i) (v:=v) (p':=p'); auto.
Qed.

(** auxiliary lemmas to circumvent Coq deficiencies *)
Lemma array_pa_valid_2 :
  forall m, forall p:pointer, forall a,
  PM.find m p = Some Array -> pa_valid (Build_mem m a) p. 
Proof.
  intros m p a pr; exact (array_pa_valid (Build_mem m a) pr).
Qed.

Lemma pa_model_array_2 :
  forall m, forall p:pointer, forall a,
  PM.find m p = Some Array -> pa_model (Build_mem m a) p a. 
Proof.
  intros m p a pr; exact (pa_model_array (Build_mem m a) pr).
Qed.

Lemma pa_model_diff_2 :
  forall m, forall p:pointer, forall i v p', forall f f',
  PM.find m p = Some (Diff i v p') -> 
  pa_model (Build_mem m f) p' f' ->
  f = upd f' i v ->
  pa_model (Build_mem m f) p f. 
Proof.
  intros m p i v p' f f' pr1 pr2 pr3. 
  subst f; 
  apply pa_model_diff with (p':=p'); auto.
Qed.

Lemma pa_model_function :
  forall m p f1, pa_model m p f1 -> forall f2, pa_model m p f2 -> f1=f2.
Proof.
  induction 1; induction 1; intuition.
  rewrite H in H0; discriminate H0.
  rewrite H in H1; discriminate H1.
  rewrite H in H1; injection H1; intros; subst; auto.
  generalize (IHpa_model f0 H2); intro; subst; auto.
Qed.

(** main separation lemma *)
Lemma pa_valid_sep : 
  forall m, forall p, forall d,
  pa_valid m p ->
  pa_valid (Build_mem (PM.add (ref m) (PM.new (ref m)) d) (arr m)) p.
Proof.
  induction 1; simpl.
  apply array_pa_valid_2.
  rewrite PM.find_add_neq; trivial.
  apply old_is_not_new; rewrite H; discriminate.
  apply diff_pa_valid with (i:=i) (v:=v) (p':=p').
  simpl; rewrite PM.find_add_neq; trivial.
  apply old_is_not_new; rewrite H; discriminate.
  trivial.
Qed.

(** the same, for [pa_model] *)
Lemma pa_model_sep : 
  forall m, forall p, forall d, forall f,
  pa_model m p f->
  pa_model (Build_mem (PM.add (ref m) (PM.new (ref m)) d) (arr m)) p f.
Proof.
  induction 1; simpl.
  apply pa_model_array_2.
  rewrite PM.find_add_neq; trivial.
  apply old_is_not_new; rewrite H; discriminate.
  apply pa_model_diff with (p':=p').
  simpl; rewrite PM.find_add_neq; trivial.
  apply old_is_not_new; rewrite H; discriminate.
  trivial.
Qed.

(** We have a well-founded order relation on pointers, as soon as they point
    to valid persistent arrays. This is simply the usual order on the 
    lengths to the immediate array i.E. the number of [Diff]s to follow to 
    reach [Array]. *)

Inductive dist (m:PM.t data) : pointer -> nat -> Prop :=
  | dist_zero : forall p, PM.find m p = Some Array -> dist m p O
  | dist_succ : forall p p' i v n, 
                PM.find m p = Some (Diff i v p') -> 
                dist m p' n -> dist m p (S n). 

Lemma dist_function : forall m, forall p n1,
  dist m p n1 -> forall n2, dist m p n2 -> n1=n2.
Proof.
  induction 1.
  destruct 1; auto.
  rewrite H0 in H; discriminate H.
  induction 1; auto.
  rewrite H in H1; discriminate H1.
  rewrite H in H1; injection H1.
  intros; subst.
  generalize (IHdist n0 H2); auto.
Qed.

Definition lt_dist (m:PM.t data) (p1 p2 : pointer) : Prop :=
  exists n1:nat,
  exists n2:nat,
  dist m p1 n1 /\ dist m p2 n2 /\ (n1 < n2)%nat.

Lemma lt_dist_wf : forall m, well_founded (lt_dist m).
Proof.
intro m.
apply well_founded_inv_lt_rel_compat with
 (F := fun (x:pointer) (n:nat) => dist m x n).
unfold lt_dist, inv_lt_rel.
intros p1 p2 (n1, (n2, (h1,(h2,h3)))).
exists n1.
assumption.
intros n3 hn3; generalize (dist_function h2 hn3).
intros; subst; auto.
Qed.

Lemma lt_dist_diff :
  forall m p, pa_valid m p ->
  forall i v p',
  PM.find (ref m) p = Some (Diff i v p') -> lt_dist (ref m) p' p.
Proof.
  unfold lt_dist; induction 1; intros.
  rewrite H0 in H; discriminate H.
  rewrite H1 in H; injection H; intros; subst.
  inversion H0.
  exists O; exists (S O); intuition.
  apply dist_zero; auto.
  apply dist_succ with (i:=i) (v:=v) (p':=p'); auto.
  apply dist_zero; auto.
  generalize (IHpa_valid i0 v0 p'0 H2).
  intros (n1,(n2,(h1,(h2,h3)))).
  exists (S n1); exists (S n2); intuition.
  apply dist_succ with (i:=i0) (v:=v0) (p':=p'0); auto.
  apply dist_succ with (i:=i) (v:=v) (p':=p'); auto.
Qed.

Lemma mem_inv :
  forall m p,
  { d:data | PM.find (ref m) p = Some d }+
  { PM.find (ref m) p = None }.
Proof.
  intros m p; destruct (PM.find (ref m) p).
  left; exists d; auto.
  right; auto.
Defined.

Lemma pa_inversion :
  forall m p, pa_valid m p ->
  { p':pointer & { i:Z & { v:Z | 
    PM.find (ref m) p = Some (Diff i v p') /\ pa_valid m p' }}}
+ { PM.find (ref m) p = Some Array}.
Proof.
  intros m p h.
  elim (mem_inv m p).
  intros (d,hp). destruct d.
  right; auto.
  left; exists p0; exists z; exists z0; intuition.
  inversion h; rewrite H in hp.
  discriminate hp.
  injection hp; intros; subst; auto.
  intro; elimtype False. 
  inversion h; rewrite H in b; discriminate b.
Defined.

(** The function [get] *)
(* ***************************************************************************
 let rec get t i = match !t with
  | Array a -> a.(i)
  | Diff (j, v, t') -> if i == j then v else get t' i
*************************************************************)

Definition get : 
  forall m, forall p, pa_valid m p -> 
  forall i, { v:Z | forall f, pa_model m p f -> v = f i }.
Proof.
  intros m; induction p using (well_founded_induction (lt_dist_wf (ref m))).
  intros h i.
  elim (pa_inversion h).
  (* Diff j v p' *)
  intros (p',(j,(v,(h1,h2)))).
  case (Z_eq_dec i j); intro hij.
  exists v; intros.
  inversion H0; rewrite H1 in h1.
  discriminate h1.
  injection h1; intros; subst.
  unfold upd; case (Z_eq_dec j j); simpl; auto. 
  intros; absurd (j<>j); auto. 
  assert (hp': lt_dist (ref m) p' p).
  apply lt_dist_diff with j v; auto.
  elim (H p' hp' h2 i); intros.
  exists x; intuition.
  inversion H0; rewrite H1 in h1. discriminate h1.
  injection h1; intros; subst.
  unfold upd; case (Z_eq_dec i j); intuition.
  (* Array *)
  intro; exists (arr m i); intros.
  inversion H0; auto.
  rewrite H1 in b; discriminate b.
Defined.
Implicit Arguments get [].

(* ************************************************************
let set t i v = match !t with
  | Array a as n ->
      let old = a.(i) in
      a.(i) <- v;
      let res = ref n in
      t := Diff (i, old, res);
      res
  | Diff _ ->
      ref (Diff (i, v, t))
***************************************************************)

(** The function [set] *)
(* set : mem -> pointer -> Z -> Z -> pointer * mem *)

Definition set_code (m:mem) (p:pointer) (i v : Z) :=
  match PM.find (ref m) p with
  | Some Array => 
      let old := arr m i in
      let arrm := upd (arr m) i v in
      let res := PM.new (ref m) in
      let refm := PM.add (ref m) res Array in
      let refm := PM.add refm p (Diff i old res) in
      (res, Build_mem refm arrm) 
  | Some (Diff _ _ _) =>
      let p' := PM.new (ref m) in
      let refm := PM.add (ref m) p' (Diff i v p) in
      (p', Build_mem refm (arr m))
  | None => 
      (* absurd *) (p,m)
  end.

Lemma set_correct :
  forall m:mem, forall p:pointer, forall i v:Z,
  forall f, pa_model m p f ->
  let (p',m') := set_code m p i v in
  pa_model m' p f /\ 
  pa_model m' p' (upd f i v).
Proof.
  unfold set_code; destruct 1; simpl.
  rewrite H; simpl. 
  split.
  set (res := PM.new (ref m)).
  pattern (arr m) at 3.
  replace (arr m) with (upd (upd (arr m) i v) i (arr m i)).
  apply pa_model_diff with (p':=res).
  simpl.
  rewrite PM.find_add_eq; trivial.
  apply pa_model_array_2.
  rewrite PM.find_add_neq.
  rewrite PM.find_add_eq; trivial.
  red; intro; generalize (PM.find_new (ref m)).
  unfold res in *|-*; subst p.
  rewrite H; discriminate.
  apply upd_ext; intro i0.
  unfold upd; case (Z_eq_dec i0 i); simpl; intros; subst; auto.
  set (res := PM.new (ref m)).
  apply pa_model_array_2.
  rewrite PM.find_add_neq.
  rewrite PM.find_add_eq; trivial.
  red; intro; generalize (PM.find_new (ref m)).
  unfold res in *|-*; subst p.
  rewrite H; discriminate.
(* Diff *)
  rewrite H; simpl.
  split.
  apply pa_model_diff with (p':=p').
  simpl; rewrite PM.find_add_neq; trivial.
  apply old_is_not_new; rewrite H; discriminate.
  apply pa_model_sep; trivial.
  apply pa_model_diff with (p':=p); simpl.
  rewrite PM.find_add_eq; trivial.
  apply pa_model_diff with (p':=p'); simpl.
  rewrite PM.find_add_neq; trivial.
  apply old_is_not_new; rewrite H; discriminate.
  apply pa_model_sep; trivial.
Qed.

Definition set :
  forall m:mem, forall p:pointer, forall i v:Z,
  forall f:Z->Z, pa_model m p f ->
  { p':pointer & { m':mem | pa_model m' p f /\ 
                            pa_model m' p' (upd f i v) } }.
Proof.
  intros m p i v f h.
  generalize (set_correct i v h).
  destruct (set_code m p i v).  
  intros (h1,h2); exists p0; exists m0; intuition.
Defined.

(* or, equivalently *)
Definition set2 :
  forall m:mem, forall p:pointer, forall i v:Z,
  pa_valid m p ->
  { p':pointer & { m':mem | 
    forall f, pa_model m p f ->
       pa_model m' p f /\ 
       pa_model m' p' (upd f i v) } }.
Admitted.


(** 2. Persistent union-find *)

Parameter N : Z.

Inductive repr (f: Z->Z)  : Z->Z->Prop :=
  | repr_zero : 
      forall i, f i = i -> repr f i i 
  | repr_succ : 
      forall i j r, f i = j -> 0<=j<N -> ~j=i -> repr f j r -> repr f i r.

Lemma repr_below_N :
  forall f i r, 0<=i<N -> repr f i r -> 0<=r<N.
Proof.
  induction 2; auto.
Qed.
Hint Resolve repr_below_N.

(* *
Definition is_puf (m:mem2) (p:pointer) (fc:Z->Z) (f:Z->Z) := 
  pa_valid (c m) p fc /\ pa_valid (father m) p f
 /\ forall i, 0<=i<N -> exists j, repr f i j.
**)

Definition reprf (f:Z->Z) := 
  (forall i, 0<=i<N -> 0<=f i<N) /\
  (forall i, 0<=i<N -> exists j, repr f i j).

Definition uf_valid (m:mem) (p:pointer) :=
  pa_valid m p /\
  forall f, pa_model m p f -> reprf f.

Inductive distr (f : Z->Z) : Z -> nat -> Prop :=
  | distr_zero : forall i, f i = i -> distr f i O
  | distr_succ : forall i j n,
                 j = f i -> j <> i ->
                 distr f j n -> distr f i (S n). 

Lemma distr_function : forall f, forall i n1,
  distr f i n1 -> forall n2, distr f i n2 -> n1=n2.
Proof.
  induction 1.
  destruct 1; auto with *.
  induction 1; auto with *.
  intros; subst.
  generalize (IHdistr n0 H4); auto.
Qed.

Definition lt_distr (m:mem) (p : pointer) (i1 i2 : Z) : Prop :=
  exists n1:nat,
  exists n2:nat,
  exists f, pa_model m p f /\
  distr f i1 n1 /\ distr f i2 n2 /\ (n1 < n2)%nat.

Require Export Wf_nat.

Lemma lt_distr_wf : forall m p, well_founded (lt_distr m p).
Proof.
intros m p.
apply well_founded_inv_lt_rel_compat with
 (F := fun (i:Z) (n:nat) => exists f, pa_model m p f /\ distr f i n).
unfold lt_distr, inv_lt_rel.
intros i1 i2 (n1, (n2, (f,(h1,(h2,(h3,h4)))))).
exists n1.
exists f; intuition.
intros n3 (f1,(hf1a,hf1b)).
assert (f1=f). apply pa_model_function with m p; auto.
subst f1.
generalize (distr_function h3 hf1b).
intros; subst; auto.
Qed.

(* **
  let rec find_aux f i = 
    let fi = A.get f i in
    if fi == i then 
      f, i
    else 
      let f, r = find_aux f fi in 
      let f = A.set f i r in
      f, r
      
  let find h x = 
    let f,rx = find_aux h.father x in h.father <- f; rx
***)

(* f1 and f2 define the same representatives *)
Definition same_reprs f1 f2 :=
  forall i, 0<=i<N -> forall j, repr f1 i j <-> repr f2 i j.

Lemma same_reprs_repr :
  forall f1 f2, same_reprs f1 f2 -> 
  forall x rx, 0<=x<N -> repr f1 x rx -> repr f2 x rx.
Proof.
  unfold same_reprs; intros.
  assert (0<=rx<N).
  eauto.
  generalize (H x H0 rx); intuition.
Qed.
Hint Resolve same_reprs_repr.

(* x and y are in the same class *)
Definition equiv f x y :=
  forall rx ry, repr f x rx -> repr f y ry -> rx=ry.

(* x and y are not in the same class *)
Definition disjoint f x y :=
  forall rx ry, repr f x rx -> repr f y ry -> ~rx=ry.

Lemma repr_function : 
  forall f x r1, repr f x r1 -> forall r2, repr f x r2 -> r1=r2.
Proof.
  induction 1.
  induction 1; auto.
  assert (eqij: i=j).
  omega.
  rewrite eqij; apply IHrepr; rewrite <- eqij; assumption.
  induction 1; auto.
  absurd (i=j); auto with *.
  assert (j=j0). omega. subst.
  eauto.
Qed.
Hint Resolve repr_function.

Lemma repr_fixpoint :
  forall f i r, repr f i r -> f r = r.
Proof.
  induction 1; auto.
Qed.
Hint Resolve repr_fixpoint.

(** equiv is an equivalence relation *)
Lemma equiv_refl :
  forall f a, equiv f a a.
Proof.
  unfold equiv; eauto.
Qed.

Lemma equiv_trans : 
  forall f, reprf f -> 
  forall a b c, 0<=a<N -> 0<=b<N -> 0<=c<N ->
  equiv f a b -> equiv f b c -> equiv f a c.
Proof.
  unfold equiv; intuition.
  unfold reprf in H.
  destruct H.
  elim (H10 b).
  intros rb hrb.
  transitivity rb; auto.
  auto.
Qed.

Lemma equiv_sym :
  forall f a b, equiv f a b -> equiv f b a.
Proof.
  unfold equiv; intuition.
  symmetry; auto.
Qed.

Hint Resolve equiv_refl equiv_sym equiv_trans.

Lemma same_reprs_refl :
  forall f, same_reprs f f.
Proof.
  unfold same_reprs; intuition.
Qed.

Lemma same_reprs_sym :
  forall f1 f2, same_reprs f1 f2 -> same_reprs f2 f1.
Proof.
  unfold same_reprs; intuition; firstorder.
Qed.

Lemma same_reprs_trans :
  forall f1 f2 f3, same_reprs f1 f2 -> same_reprs f2 f3 ->
  same_reprs f1 f3.
Proof.
  unfold same_reprs; intros.
  generalize (H i H1 j) (H0 i H1 j); intuition.
Qed.
Hint Resolve same_reprs_refl same_reprs_sym same_reprs_trans.

Lemma reprf_distr :
  forall f, reprf f ->
  forall x, 0<=x<N -> exists n, distr f x n.
Proof.
  unfold reprf; intros.
  destruct H; destruct (H1 x H0).
  induction H2.
  exists O; auto.
  apply distr_zero; auto.
  elim (IHrepr H3); intros n hn. 
  exists (S n).
  apply distr_succ with j; auto.
Qed.

Ltac case_eq x y :=
  case (Z_eq_dec x y); intro; [subst x | idtac].

Lemma path_compression :
  forall f, reprf f ->
  forall x, 0<=x<N ->
  forall r, repr f x r ->
  reprf (upd f x r).
Proof.
  unfold reprf; intros.
  destruct H.
  split; intros.
  unfold upd; case (Z_eq_dec i x); intro.
  apply repr_below_N with f x; auto.
  auto.
  destruct (H2 i H3) as [j hj].
  induction hj.
  case_eq x i.
  exists r. 
  assert (i=r).
  inversion H1; auto.
  absurd (i<>j); auto with *.
  subst i; apply repr_zero.  
  upd_eq.
  exists i; apply repr_zero; auto.
  upd_neq.
  case_eq i x.
  exists r.
  case_eq x r.
  apply repr_zero; auto.
  upd_eq.
  apply repr_succ with r; auto.
  upd_eq.
  apply repr_below_N with f x; auto.
  apply repr_zero; auto.
  upd_neq.
  apply repr_fixpoint with x; auto.
  destruct (IHhj H5) as [j0 hj0].
  exists j0; apply repr_succ with j; auto.
  upd_neq.
Qed.

Lemma path_compression_2 :
  forall f, reprf f ->
  forall x, 0<=x<N ->
  forall r, repr f x r ->
  same_reprs f (upd f x r).
Proof.
  intros; unfold same_reprs; split.
  induction 1.
  case (Z_eq_dec i x); intro.
  apply repr_zero; auto.
  upd_eq.
  assert (repr f i i). apply repr_zero; auto.
  subst i; apply repr_function with f x; auto.
  apply repr_zero; auto.
  upd_neq.
  generalize (IHrepr H4); intro h; clear IHrepr.
  case (Z_eq_dec i x); intro.
  assert (repr f i r0).
  apply repr_succ with j; auto.
  assert (r=r0).
  subst i; apply repr_function with f x; auto.
  subst i r0.
  case_eq x r.
  apply repr_zero; auto.
  upd_eq.
  apply repr_succ with r; auto.
  upd_eq.
  apply repr_below_N with f x; auto.
  apply repr_zero; auto.
  upd_neq.
  apply repr_fixpoint with x; auto.
  apply repr_succ with j; auto.
  upd_neq.
(* upd f -> f *)
  induction 1.
  case_eq i x.
  rewrite upd_eq in H3; auto.
  subst x; apply repr_zero; auto.
  apply repr_fixpoint with r; auto.
  rewrite upd_neq in H3; auto.
  apply repr_zero; auto.
  generalize (IHrepr H4); clear IHrepr; intro h.
  case_eq i x.
  rewrite upd_eq in H3; auto.
  subst j.
  assert (repr (upd f x r) r r).
  apply repr_zero; auto.
  upd_neq.
  apply repr_fixpoint with x; auto.
  assert (r=r0).
  apply repr_function with (upd f x r) r; auto.
  subst r0. assumption.
  rewrite upd_neq in H3; auto.
  apply repr_succ with j; auto.
Qed.

Definition find :
  forall (m:mem), forall p, uf_valid m p ->
  forall x, 0<=x<N ->
  { r:Z & { p':pointer & { m':mem | 
    (*(forall p, uf_valid m p -> uf_valid m' p) /\ *)
    uf_valid m' p' /\
    forall f, pa_model m p f -> repr f x r /\
    forall f', pa_model m' p' f' -> same_reprs f f' } } }.
Proof.
  intros m p h; induction x using (well_founded_induction (lt_distr_wf m p)).
  intros hx.
   (* let x0 = get m p x *) 
  destruct h.
  destruct (get m p H0 x).
  case (Z_eq_dec x0 x); intro.
  (* x0 = x *)
  subst x0; exists x; exists p; exists m; intuition.
  unfold uf_valid; intuition.
  apply repr_zero; symmetry; intuition.
  assert (f'=f). apply pa_model_function with m p; auto.
  subst f'; auto.
  (* x0 <> x *)
  (* let r,p',m' = find x0 *)
  destruct (H x0) as [r (p0,(m0,(h1,h2)))]; clear H.
  elim (pa_valid_pa_model H0); intros f hf.
  generalize (H1 f hf); clear H1; intro H1.
  generalize (e f hf); clear e; intro e.
  unfold lt_distr.
  assert (Ix0: 0<=x0<N). unfold reprf in H1. subst x0; firstorder.
  destruct (reprf_distr H1 Ix0).
  exists x1; exists (S x1); exists f; intuition.
  apply distr_succ with x0; auto.
  elim (pa_valid_pa_model H0); intros f hf.
  generalize (e f hf); clear e; intro e.
  generalize (H1 f hf); clear H1; intro H1.
  unfold reprf in H1. subst x0; firstorder.
  (* let p1,m1 = set2 m0 p0 x r *)
  destruct h1.
  destruct (set2 x r H) as [p1 (m1,h3)]. 
  exists r; exists p1; exists m1.
  elim (pa_valid_pa_model H0); intros f hf.
  generalize (H1 f hf); clear H1; intro H1.
  generalize (e f hf); clear e; intro e.
  elim (pa_valid_pa_model H); intros f0 hf0.
  generalize (H2 f0 hf0); clear H2; intro H2.
  destruct (h2 f hf) as [h4 h5]; clear h2.
  generalize (h5 f0 hf0); clear h5; intro h5.
  generalize (h3 f0 hf0); clear h3; intros (h6,h7).
  split.
  unfold uf_valid. split. eauto.
  intros f2 hf2. assert (f2 = upd f0 x r). 
  eapply pa_model_function; eauto.
  subst f2.
  assert (repr f x r).
  apply repr_succ with x0; auto.
  unfold reprf in H1. destruct H1. subst x0.
  apply H1; auto.
  assert (repr f0 x r).
  unfold same_reprs in h5. 
  destruct (h5 x hx r).
  auto.
  apply path_compression; auto.
  intros f1 hf1.
  assert (f1=f).
  apply pa_model_function with m p; auto.
  subst f1; clear hf1.
  split.
  apply repr_succ with x0; auto.
  unfold reprf in H1. destruct H1. subst x0.
  apply H1; auto.
  intros f' hf'.
  assert (f' = upd f0 x r).
  apply pa_model_function with m1 p1; auto.
  subst f'; clear hf'.
  assert (repr f x r).
  apply repr_succ with x0; auto.
  unfold reprf in H1. destruct H1. subst x0.
  apply H1; auto.
  assert (repr f0 x r).
  unfold same_reprs in h5. 
  destruct (h5 x hx r).
  auto.
  apply same_reprs_trans with f0; auto.
  apply path_compression_2; auto.
Defined.

(* TODO: reroot *)

(* ** simpler version not using the ranks:
 
  let union h x y = 
    let rx = find h x in
    let ry = find h y in
    if rx != ry then begin
      { h with father = A.set h.father ry rx }
    end else
      h
***)

Lemma same_reprs_equiv :
  forall f1 f2 x y, 0<=x<N -> 0<=y<N ->
  same_reprs f1 f2 -> equiv f1 x y -> equiv f2 x y.
Proof.
  unfold same_reprs,equiv; intros.
  generalize (H1 x H rx) (H1 y H0 ry) (H2 rx ry); intuition.
Qed.

Lemma same_reprs_equiv_2 :
  forall f1 f2 x y r, 0<=x<N -> 0<=y<N ->
  same_reprs f1 f2 -> repr f1 x r -> repr f2 y r -> equiv f2 x y.
Proof.
  unfold same_reprs, equiv; intros.
  generalize (H1 x H r) (H1 y H0 r); intuition.
  assert (r=rx); eauto. 
  assert (r=ry); eauto.
  subst; auto.
Qed.
Hint Resolve same_reprs_equiv same_reprs_equiv_2.

Lemma repr_snoc :
  forall f x rx ry, 0<=rx<N -> rx<>ry -> repr f x rx ->
  forall y, repr f y ry -> repr (upd f ry rx) y rx.
Proof.
  induction 4.  
  apply repr_succ with rx; auto.
  upd_eq.
  generalize (repr_fixpoint H1).
  intro; apply repr_zero; auto.
  upd_neq.
  case (Z_eq_dec i r); intro.
  subst i.
  apply repr_succ with rx; auto.
  upd_eq.
  apply repr_zero; auto.
  generalize (repr_fixpoint H1).
  intro; upd_neq.
  apply repr_succ with j; intuition. 
  upd_neq.
Qed.
Hint Resolve repr_snoc.


Lemma repr_main_lemma :
  forall f,
  reprf f ->
  forall x y rx ry,
  0 <= x < N -> 0 <= y < N -> rx <>ry ->
  repr f x rx ->
  repr f y ry ->
  reprf (upd f ry rx).
Proof.
  red; intros.
  unfold reprf in H; destruct H.
  assert (0 <= rx < N).
  apply repr_below_N with f x; auto.
  split; intros.
  unfold upd; case_eq i ry; auto.
  assert (repr (upd f ry rx) y rx).
  apply repr_snoc with x; auto.
  destruct (H5 i H7) as [j hj]. 
  case_eq i ry.
  exists rx.
  apply repr_succ with rx; auto.
  upd_eq.
  apply repr_zero; auto.
  upd_neq.
  apply repr_fixpoint with x; auto.
  induction hj.
  exists i.
  apply repr_zero; auto.
  upd_neq.
  case_eq j ry.
  exists rx.
  apply repr_succ with ry; auto.
  upd_neq.
  apply repr_below_N with f y; auto.
  apply repr_succ with rx; auto.
  upd_eq.
  apply repr_zero; auto.
  upd_neq.
  apply repr_fixpoint with x; auto.
  assert (0 <= j < N).
  subst j; apply H; auto.
  destruct (IHhj H12 n0) as [r0 hr0].
  exists r0.
  apply repr_succ with j; auto.
  upd_neq.
Qed.

Lemma repr_x_inv_upd :
  forall f rx ry x,
  repr f x rx -> repr (upd f ry rx) x rx.
Proof.
  induction 1.
  apply repr_zero.
  unfold upd; case (Z_eq_dec i ry); auto.
  case (Z_eq_dec i ry); auto.
  intro; subst i. 
  case (Z_eq_dec r ry); auto.
  intro; subst; apply repr_zero; auto.
  upd_eq.
  intro; apply repr_succ with r; auto.
  upd_eq.
  apply repr_below_N with f j; auto.
  apply repr_zero; auto.
  upd_neq.
  apply repr_fixpoint with j; auto.
  intro; apply repr_succ with j; auto.
  upd_neq.
Qed.
Hint Resolve repr_x_inv_upd.


Hint Resolve pa_model_function.

Lemma equiv_def :
  forall f a b, equiv f a b ->
  forall ra rb, repr f a ra -> repr f b rb -> ra=rb.
Proof.
  unfold equiv; intuition.
Qed.
Hint Resolve equiv_def.

Lemma equiv_inv :
  forall f a b r, repr f a r -> repr f b r -> equiv f a b.
Proof.
  unfold equiv; intuition.
  assert (r=rx). apply repr_function with f a; auto.
  assert (r=ry). apply repr_function with f b; auto.
  subst; auto.
Qed.
Hint Resolve equiv_inv.

Lemma repr_idem :
  forall f x rx, repr f x rx -> repr f rx rx.
Proof.
  induction 1; auto.
  apply repr_zero; auto.
Qed.

Lemma union_lemma_1 :
  forall x y,
  0 <= x < N -> 0 <= y < N ->
  forall rx ry, rx <> ry ->
  forall (f : Z -> Z), reprf f ->
  repr f x rx -> repr f y ry -> 
  forall a, 0 <= a < N -> 
  repr (upd f ry rx) a rx -> (repr f a rx \/ repr f a ry).
Proof.
  intros.
  induction H6; subst rx0.
  case_eq i ry.
  left; apply repr_zero; auto.
  apply repr_fixpoint with y; auto.
  rewrite upd_neq in H6; auto.
  left; apply repr_zero; auto.
  generalize (IHrepr H7); clear IHrepr; intro hj.
  case_eq i ry.
  right; apply repr_idem with y; auto.
  rewrite upd_neq in H6; auto.
  destruct hj; [left | right]; apply repr_succ with j; auto.
Qed.

Lemma union_lemma_2 :
  forall x y,
  0 <= x < N -> 0 <= y < N ->
  forall rx ry, rx <> ry ->
  forall (f : Z -> Z), reprf f ->
  repr f x rx -> repr f y ry -> 
  forall a ra, 0 <= a < N -> repr (upd f ry rx) a ra -> ra<>rx ->
  repr f a ra.
Proof.
  intros.
  induction H6.
  case_eq i ry.
  rewrite upd_eq in H6; auto.
  absurd (rx=ry); auto with *.
  apply repr_zero; auto.
  rewrite upd_neq in H6; auto.
  generalize (IHrepr H8 H7); clear IHrepr; intro hjr.
  case_eq i ry.
  rewrite upd_eq in H6; auto.
  subst j.
  assert (repr (upd f ry rx) rx rx).
  apply repr_zero; auto.
  upd_neq.
  apply repr_fixpoint with x; auto.
  absurd (r=rx); auto.
  apply repr_function with (upd f ry rx) rx; auto.
  apply repr_succ with j; auto.
  rewrite upd_neq in H6; auto.
Qed.

Lemma repr_inv_upd : 
  forall x y,
  0 <= x < N -> 0 <= y < N ->
  forall rx ry, rx <> ry ->
  forall (f : Z -> Z), reprf f ->
  repr f x rx -> repr f y ry -> 
  forall a ra, 0 <= a < N -> repr f a ra -> ra<>ry ->
  repr (upd f ry rx) a ra.
Proof.
  intros.
  induction H6.
  apply repr_zero; auto.
  upd_neq.
  case_eq ry j.
  assert (repr f j j).
  apply repr_idem with y; auto.
  assert (j=r). apply repr_function with f j; auto.
  absurd (j=r); auto with *.
  case_eq i ry.
  assert (f ry = ry). apply repr_fixpoint with y; auto.
  absurd (f ry = ry); auto with *.
  apply repr_succ with j; auto.
  upd_neq.
Qed.

Lemma union_main_lemma :
  forall x y,
  0 <= x < N -> 0 <= y < N ->
  forall rx ry, rx <> ry ->
  forall (f : Z -> Z), reprf f ->
  repr f x rx -> repr f y ry -> 
  forall a b, 0 <= a < N -> 0 <= b < N -> 
  (equiv (upd f ry rx) a b <->
   (equiv f a b \/ ((equiv f a x /\ equiv f b y) \/ 
                    (equiv f b x /\ equiv f a y)))).
Proof.
  intros.
  assert (rrx: repr (upd f ry rx) x rx).
  apply repr_x_inv_upd; auto.
  assert (Irx: 0 <= rx < N).
  apply repr_below_N with f x; auto.
  assert (rry: repr (upd f ry rx) y rx).
  apply repr_snoc with x; auto.
  assert (reprf_updf: reprf (upd f ry rx)).
  apply repr_main_lemma with x y; auto.
  split; intros.
  destruct reprf_updf.
  destruct (H9 a H5) as [ra hra].
  destruct (H9 b H6) as [rb hrb].
  assert (ra=rb). eauto.
  subst rb.
  case_eq ra rx.
  assert (repr f a rx \/ repr f a ry).
  apply union_lemma_1 with x y; auto.
  assert (repr f b rx \/ repr f b ry).
  apply union_lemma_1 with x y; auto.
  destruct H10; destruct H11.
  left; eauto.
  right; left; eauto.
  right; right; eauto.
  left; eauto.
  left.
  assert (repr f a ra). apply (union_lemma_2 H H0 H1); auto.
  assert (repr f b ra). apply (union_lemma_2 H H0 H1); auto.
  eauto.
  (* <- *)
  destruct H2.
  destruct (H8 a H5) as [ra hra].
  destruct (H8 b H6) as [rb hrb].
  destruct H7.
  assert (ra=rb). eauto. subst rb.
  case_eq ra ry.
  assert (repr (upd f ry rx) a rx).
  apply repr_snoc with x; auto.
  assert (repr (upd f ry rx) b rx).
  apply repr_snoc with x; auto.
  eauto.
  assert (repr (upd f ry rx) a ra).
  apply repr_inv_upd with x y; auto.
  red; auto.
  assert (repr (upd f ry rx) b ra).
  apply repr_inv_upd with x y; auto.
  red; auto.
  eauto.
  destruct H7; destruct H7 as [h1 h2].
  assert (repr (upd f ry rx) a rx).
  assert (ra=rx). eauto. subst ra.
  apply repr_inv_upd with x y; auto.
  red; auto.
  assert (rb=ry). eauto. subst rb.
  assert (repr (upd f ry rx) b rx).
  apply repr_snoc with x; auto.
  eauto.
  assert (ra=ry). eauto. subst ra.
  assert (repr (upd f ry rx) a rx).
  apply repr_snoc with x; auto.
  assert (rb=rx). eauto. subst rb.
  assert (repr (upd f ry rx) b rx).
  apply repr_inv_upd with x y; auto.
  red; auto.
  eauto.
Qed.

Definition union :
  forall (m:mem), forall p, uf_valid m p ->
  forall x y, 0<=x<N -> 0<=y<N ->
  { p':pointer & { p1:pointer & { m':mem | 
       uf_valid m' p1 /\ uf_valid m' p'  /\ 
       forall f1, pa_model m p f1 -> 
       ((forall f2, pa_model m' p1 f2 -> same_reprs f1 f2) /\
        (forall f', pa_model m' p' f' ->
         (*equiv f' x y /\*)
         forall a b, 0<=a<N -> 0<=b<N ->
            (equiv f' a b <-> 
             (equiv f1 a b \/ ((equiv f1 a x /\ equiv f1 b y) \/
                               (equiv f1 b x /\ equiv f1 a y))))))
        }}}.
Proof.
  intros m p hpuf x y Ix Iy.
  elim (find hpuf Ix); intros rx (p0,(m0,(uf_m0_p0,hrx))).
  elim (find uf_m0_p0 Iy); intros ry (p1,(m1,(uf_m1_p1,hry))).
  case (Z_eq_dec rx ry); intro.

  (* rx = ry *)
  exists p1; exists p1; exists m1.
  split. assumption. split. assumption.
  intros f1 hf1.
  destruct uf_m0_p0.
  elim (pa_valid_pa_model H); intros f1m0 hf1m0.
  generalize (hrx f1 hf1); clear hrx; intros (h1,hrx).
  generalize (hrx f1m0 hf1m0); clear hrx; intros h2.
  split.
  intros f2 hf2. 
  generalize (hry f1m0 hf1m0); clear hry; intros (h3,hry).
  generalize (hry f2 hf2); clear hry; intros h4.
  eauto.
  intros f' hf'.
  assert (equiv f' x y).
  generalize (hry f1m0 hf1m0); clear hry; intros (h3,hry).
  generalize (hry f' hf'); clear hry; intros h4.
  apply same_reprs_equiv with f1m0; auto.
  apply same_reprs_equiv_2 with f1 rx; subst; auto.
  generalize (hry f1m0 hf1m0); clear hry; intros (h3,hry).
  generalize (hry f' hf'); clear hry; intros h4.
  generalize (H0 f1m0 hf1m0); clear H0; intro.
  intros a b; split.
  intros hab.
  assert (equiv f1m0 a b). eauto.
  assert (equiv f1 a b); eauto.
  assert (reprf f').   red in uf_m1_p1; intuition.
  assert (equiv f1 x y). eauto.
  assert (same_reprs f1 f'). eauto.
  intuition eauto.
  assert (equiv f' a x). eauto.
  assert (equiv f' b y); eauto.
  apply equiv_trans with x; eauto.
  apply equiv_trans with y; auto.
  assert (equiv f' a y). eauto.
  assert (equiv f' b x); eauto.
  apply equiv_trans with y; eauto.
  apply equiv_trans with x; auto.

  (* rx <> ry: father = set ry rx *)
  destruct uf_m1_p1.
  elim (set2 ry rx H); intros p' (m2,hm2).
  exists p'; exists p1; exists m2.
  destruct hpuf.
  elim (pa_valid_pa_model H1); intros f hf.
  generalize (H2 f hf); clear H2; intro reprf_f.
  destruct uf_m0_p0.
  elim (pa_valid_pa_model H2); intros f0 hf0.
  generalize (H3 f0 hf0); clear H3; intro reprf_f0.
  generalize (hrx f hf); clear hrx; intros (h1,h2).
  generalize (h2 f0 hf0); clear h2; intro h2.
  elim (pa_valid_pa_model H); intros f1 hf1.
  generalize (H0 f1 hf1); clear H0; intro reprf_f1.
  generalize (hry f0 hf0); clear hry; intros (h3,h4).
  generalize (h4 f1 hf1); clear h4; intro h4.
  generalize (hm2 f1 hf1); clear hm2; intros (h5,h6).
  split.
  unfold uf_valid; simpl; intuition eauto.
  assert (f2 = f1). eauto. subst f2; auto.
  split.
  unfold uf_valid; simpl; intuition eauto.
  assert (f2 = upd f1 ry rx). eauto. 
  subst f2; apply repr_main_lemma with x y; eauto.
  intros.
  assert (f2 = f). eauto. subst f2. 
  split; intros.
  assert (f2 = f1). eauto. subst f2. 
  eauto.
  assert (f' = upd f1 ry rx). eauto. subst f'; clear H0 H3. 
  assert (repr f1 x rx). eauto.
  assert (repr f1 y ry). eauto.
  assert (equiv f a b <-> equiv f1 a b). split; eauto.
  assert (equiv f a x <-> equiv f1 a x). split; eauto.
  assert (equiv f a y <-> equiv f1 a y). split; eauto.
  assert (equiv f b x <-> equiv f1 b x). split; eauto.
  assert (equiv f b y <-> equiv f1 b y). split; eauto.
  generalize (union_main_lemma Ix Iy n reprf_f1 H0 H3 H4 H5).
  intuition.
Defined.









