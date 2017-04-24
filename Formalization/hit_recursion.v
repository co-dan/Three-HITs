Require Import HoTT.
Require Import polynomial hit_structure.


Arguments hit_point {_} _ _ _.
Arguments hit_path {_} _ _ _.
Arguments hit_ind {_} _ _ _ _ _.

(** Going from polynomial actions to polynomial 
    liftings of constant type families*)
Section PolyFamConst.
(** [C] is an [I]-indexed family of polynomials describing 
    point constructors*)
Variable I : Type.
Variable C : I -> polynomial.
(** [A] is a type that we are eliminate into *)
Variable A : Type.
(** [B] is an arbitrary type that we are going to use for indexing *)
Variable B : Type.
(** .. to obtain a phony type family [Fconst]. *)
Definition Fconst := fun (_:B) => A. 
(** The type [B] must contain point constructors *)
Variable c : forall i, poly_act (C i) B -> B. 
(** And [f] is the image of this constructors in [A] *)
Variable f : forall i, poly_act (C i) A -> A. 

(** poly_fam_const : 
  forall (y : P[B]) (h : \bar{P}(\x:B.A) y) : P[A] 
  converting an element of the constant family into an 
  element of P[A] *)
Definition poly_fam_const (P : polynomial) 
  y (H : poly_fam P Fconst y) : poly_act P A.
Proof.
  induction P; simpl in *.
  - apply H.
  - apply H.
  - destruct y as [y1 y2]. destruct H as [H1 H2].
    simpl in *.
    split. 
    apply (IHP1 y1 H1).
    apply (IHP2 y2 H2).
  - destruct y as [y | y].
    {  left. apply (IHP1 y H). }
    { right. apply (IHP2 y H). }
Defined.


Lemma poly_fam_const_inj P y H H':
poly_fam_const P y H = poly_fam_const P y H' ->
H = H'.
Proof.
induction P; simpl; try apply idmap.
- destruct H as [H1 H2]; destruct H' as [H1' H2']; simpl.
destruct y as [y1 y2]; simpl. 
intro Heq. 
assert (poly_fam_const P1 y1 H1 = poly_fam_const P1 y1 H1').
{ apply (ap fst Heq). }
assert (poly_fam_const P2 y2 H2 = poly_fam_const P2 y2 H2').
{ apply (ap snd Heq). }
apply path_prod; simpl; [apply IHP1 | apply IHP2]; assumption.
- destruct y as [y | y]; simpl in *; intro Heq.
  + apply IHP1. eapply path_sum_inl. exact Heq.
  + apply IHP2. eapply path_sum_inr. exact Heq.
Defined.

Lemma poly_fam_const_inj_var y y' H H':
poly_fam_const poly_var y H = poly_fam_const poly_var y' H' ->
H = H'.
Proof.
simpl. exact idmap.
Qed.

Definition f' :
  forall i (x : poly_act (C i) B), poly_fam (C i) Fconst x 
   -> A.
Proof.
  intros i x h.
  apply (f i).
  apply (poly_fam_const (C i) x h).
Defined.

(** [poly_fam_const] commutes with endpoint actions *)
Lemma cowd (P Q : polynomial) 
  (e : @endpoint I C P Q) 
  (x : poly_act P B)
  (h : poly_fam P Fconst x):
endpoint_act f e (poly_fam_const P x h) =
poly_fam_const Q (endpoint_act c e x) (endpoint_dact c f' e x h).
Proof.
  induction e; simpl; try (rewrite IHe); try reflexivity.
  { rewrite IHe1. rewrite IHe2. reflexivity. }
Qed.

(* If [h] commutes with constructors, then it commutes with all endpoints. *)
Fixpoint endpoint_act_compute
  (P Q : polynomial)
  (e : endpoint C P Q)
  h x
  {struct e}
:
  (forall i u, h (c i u) = f i (poly_map (C i) h u)) ->
  poly_map Q h (endpoint_act c e x) = endpoint_act f e (poly_map P h x).
Proof.
  intro H.
  destruct e; simpl; try reflexivity.
  (* endpoint_constr *)
  - etransitivity. apply H. f_ap. apply endpoint_act_compute. apply H.
  (* endpoint_fst *)
  - apply (ap fst (endpoint_act_compute _ _ e _ _ H)).
  - apply (ap snd (endpoint_act_compute _ _ e _ _ H)).
  (* endpoint_pair *)
  - apply path_prod ; apply endpoint_act_compute, H.
  (* endpoint_inl *)
  - f_ap. apply endpoint_act_compute, H. 
  (* endpoint_inr *)
  - f_ap. apply endpoint_act_compute, H. 
Defined.

End PolyFamConst.

Section NonDepRec.
Variable Σ : hit_signature.

(** For non-dependent recursion *)
Definition point_in
  {H : Type} (* the carrier type *)
  (F : Type)
  (c : forall i, poly_act (sig_point Σ i) H -> H) (* point constructors *)
  (p : forall j u, endpoint_act c (sig_path_lhs Σ j) u =
              endpoint_act c (sig_path_rhs Σ j) u) (* path constructors *)
  :=
  forall i, poly_act (sig_point Σ i) F -> F.

Definition path_in
  {H : HIT Σ}
  (Y : Type)
  (c : point_in Y (hit_point H) (hit_path H))
  :=
  forall j
    (x : poly_act (sig_path_param Σ j) Y),
    endpoint_act c (sig_path_lhs Σ j) x =
    endpoint_act c (sig_path_rhs Σ j) x.

Definition point_in_over (H : HIT Σ) {U : Type}
  (c : point_in U (hit_point H) (hit_path H)) :
  point_over Σ (fun (_ : H) => U) (hit_point H) (hit_path H).
Proof.
  intros i u h. 
  apply (c i).
  apply (poly_fam_const _ _ (sig_point Σ i) u h).
Defined.

Definition path_in_over (H : HIT Σ) {F : Type} 
  (c : point_in F (hit_point H) (hit_path H))
  (p : path_in F c) :
  path_over Σ (point_in_over H c).
Proof.
intros i u h. simpl.
etransitivity.
- apply transport_const.
- specialize (p i).
  pose (Gek:=(poly_fam_const  _ _ (sig_path_param Σ i) u h)).
  specialize (p Gek). unfold Gek in p.
  assert (point_in_over H c = (f' (sig_point_index Σ) (sig_point Σ) F H c)) as Moo.
  { unfold point_in_over. unfold f'. reflexivity. }
  assert (poly_fam_const F H poly_var
       (endpoint_act (hit_point H) (sig_path_lhs Σ i) u)
       (endpoint_dact (hit_point H)
          (f' (sig_point_index Σ) (sig_point Σ) F H c)
          (sig_path_lhs Σ i) u h)
  = poly_fam_const F H poly_var
       (endpoint_act (hit_point H) (sig_path_rhs Σ i) u)
       (endpoint_dact (hit_point H)
          (f' (sig_point_index Σ) (sig_point Σ) F H c)
          (sig_path_rhs Σ i) u h)) as COWEQ.
  { etransitivity. symmetry.
    apply (cowd (sig_point_index Σ) (sig_point Σ) F H (hit_point H) c _ _ (sig_path_lhs Σ i) u h).
    rewrite p. 
    apply (cowd (sig_point_index Σ) (sig_point Σ) F H (hit_point H) c _ _ (sig_path_rhs Σ i) u h). }
  rewrite <- Moo in COWEQ. 
  simpl in COWEQ. apply COWEQ.
Defined.

Definition hit_rec (H : HIT Σ) :
  forall (F : Type)
         (c : point_in F (hit_point H) (hit_path H))
         (p : path_in F c)
         (x : H), F := fun F c p x =>
    hit_ind H (fun _ => F) (point_in_over H c) (path_in_over H c p) x.

Lemma poly_fam_const_dmap H F (f : H -> F) (P : polynomial) 
 (t : poly_act P H) :
poly_fam_const F H P t (poly_dmap P f t) =
poly_map P f t.
Proof.
induction P; simpl; try reflexivity.
- destruct t as [t t']. simpl.
  apply path_prod; simpl.
  + apply IHP1.
  + apply IHP2.
- destruct t as [t | t]; simpl; f_ap.
Qed.

Theorem hit_rec_point_beta (H : HIT Σ) (F : Type)
         (c : point_in F (hit_point H) (hit_path H))
         (p : path_in F c) i (t : poly_act (sig_point Σ i) H) :
         hit_rec H F c p (hit_point H i t) =
          c i (poly_map (sig_point Σ i) (hit_rec H F c p) t).
Proof.
unfold hit_rec. 
rewrite hit_point_beta.
unfold point_in_over.
f_ap. apply poly_fam_const_dmap.
Qed.


Definition hit_rec_path_beta_type (H : HIT Σ) (F : Type)
         (c : point_in F (hit_point H) (hit_path H))
         (p : path_in F c) (i : sig_path_index Σ) 
         (u : poly_act (sig_path_param Σ i) H) : Type.
Proof.
pose (α := ap (hit_rec H F c p) (hit_path H i u)).
pose (β := p i (poly_map (sig_path_param Σ i) (hit_rec H F c p) u)).
assert (qlhs : hit_rec H F c p
      (endpoint_act (hit_point H) (sig_path_lhs Σ i) u)
       = endpoint_act c (sig_path_lhs Σ i)
      (poly_map (sig_path_param Σ i) (hit_rec H F c p) u)).
{ apply (endpoint_act_compute _ _ F H (hit_point H) c _ _ (sig_path_lhs Σ i) (hit_rec H F c p) u).
  apply hit_rec_point_beta. }
assert (qrhs : hit_rec H F c p
      (endpoint_act (hit_point H) (sig_path_rhs Σ i) u)
       = endpoint_act c (sig_path_rhs Σ i)
      (poly_map (sig_path_param Σ i) (hit_rec H F c p) u)).
{ apply (endpoint_act_compute _ _ F H (hit_point H) c _ _ (sig_path_rhs Σ i) (hit_rec H F c p) u).
  apply hit_rec_point_beta. }
symmetry in qlhs.
pose (β' := transport (fun z =>
              z = endpoint_act c (sig_path_rhs Σ i)
      (poly_map (sig_path_param Σ i) (hit_rec H F c p) u)) qlhs β).
simpl in β'.
symmetry in qrhs.
pose (β'' := transport (fun z =>
              hit_rec H F c p (endpoint_act (hit_point H) (sig_path_lhs Σ i) u) 
                  = z) qrhs β').
simpl in β''.
exact (α = β'').
Defined.

Theorem hit_rec_path_beta (H : HIT Σ) (F : Type)
         (c : point_in F (hit_point H) (hit_path H))
         (p : path_in F c) i u :
   hit_rec_path_beta_type H F c p i u.
Proof.
About apD_const.
Abort.
End NonDepRec.