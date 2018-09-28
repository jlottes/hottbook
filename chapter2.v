Require Import prelude.

Class InverseFunction `(f:A → B) := inv_fun : B → A.
Arguments inv_fun {_ _} f {_}.
Notation "f ⁻¹" := (inv_fun f) : function_scope.
Hint Extern 2 (InverseFunction (@id ?A)) => eexact (@id A) : typeclass_instances.
Hint Extern 2 (InverseFunction (inv_fun ?f)) => eexact f : typeclass_instances.

Delimit Scope path_scope with path.
Bind Scope path_scope with Id.
Local Open Scope path_scope.

Definition inverse `(p : a = b :> A) : b = a
:= match p with refl => refl end.
Arguments inverse : simpl nomatch.

Definition concat {A:𝓤} {a b c : A} (p : a = b) (q : b = c) : a = c
:= match p,q with refl,refl => refl end.
Arguments concat : simpl nomatch.

Notation "1" := refl : path_scope.
Notation "p ⁻¹" := (inverse p) : path_scope.
Notation "p · q" := (concat p q) : path_scope.
Notation "( p ·)" := (λ q, concat p q) (format "( p  ·)") : path_scope.
Notation "(· q )" := (λ p, concat p q) (format "(·  q )") : path_scope.

(* Section 2.1: Types are Higher Groupoids *)

(* Names (and proofs) from
   https://github.com/HoTT/HoTT/blob/master/theories/Basics/PathGroupoids.v *)

(* Lemma 2.1.4 i *)
Definition concat_1p `(p : x = y :> A) : 1 · p = p
:= match p with refl => refl end.

Definition concat_p1 `(p : x = y :> A) : p · 1 = p
:= match p with refl => refl end.

(* Lemma 2.1.4 ii *)
Definition concat_pV `(p : x = y :> A) : p · p⁻¹ = 1
:= match p with refl => refl end.

Definition concat_Vp `(p : x = y :> A) : p⁻¹ · p = 1
:= match p with refl => refl end.

(* Lemma 2.1.4 iii *)
Definition inv_V `(p : x = y :> A) : p⁻¹⁻¹ = p
:= match p with refl => 1 end.

(* Lemma 2.1.4 iv *)
Definition concat_p_pp {A:𝓤} {x y z t : A} (p : x = y) (q : y = z) (r : z = t) :
  p · (q · r) = (p · q) · r
:= match r with refl =>
     match q with refl =>
       match p with refl => refl
       end end end.

Definition concat_pp_p {A:𝓤} {x y z t : A} (p : x = y) (q : y = z) (r : z = t) :
  (p · q) · r = p · (q · r)
:= match r with refl =>
     match q with refl =>
       match p with refl => refl
       end end end.

(* Horizontal composition of 2-dimensional paths *)
Definition concat2 {A:𝓤} {a b c : A} {p q : a = b} {r s : b = c} (α : p = q) (β : r = s)
  : p · r = q · s
:= match α, β with refl, refl => refl end.
Arguments concat2 : simpl nomatch.
Notation "p ∗ q" := (concat2 p q) : path_scope.

Definition whiskerL {A:𝓤} {x y z : A} (p : x = y)
  {q r : y = z} (h : q = r) : p · q = p · r
:= 1 ∗ h.
Notation "p ·ₗ α" := (whiskerL p α) : path_scope.

Definition whiskerR {A:𝓤} {x y z : A} {p q : x = y}
  (h : p = q) (r : y = z) : p · r = q · r
:= h ∗ 1.
Notation "α ·ᵣ p" := (whiskerR α p) : path_scope.

Definition concat_V_pp {A:𝓤} {x y z : A} (p : x = y) (q : y = z) :
  p⁻¹ · (p · q) = q
:= concat_p_pp _ _ _ · (concat_Vp _ ·ᵣ _) · concat_1p _.

Definition concat_p_Vp {A:𝓤} {x y z : A} (p : x = y) (q : x = z) :
  p · (p⁻¹ · q) = q
:= concat_p_pp _ _ _ · (concat_pV _ ·ᵣ _) · concat_1p _.

Definition concat_pp_V {A:𝓤} {x y z : A} (p : x = y) (q : y = z) :
  (p · q) · q⁻¹ = p
:= concat_pp_p _ _ _ · (_ ·ₗ concat_pV _) · concat_p1 _.

Definition concat_pV_p {A:𝓤} {x y z : A} (p : x = z) (q : y = z) :
  (p · q⁻¹) · q = p
:= concat_pp_p _ _ _ · (_ ·ₗ concat_Vp _) · concat_p1 _.

Definition cancelL {A:𝓤} {x y z : A} (p : x = y) (q r : y = z) :
  p · q = p · r → q = r
:= λ h, (concat_V_pp p q)⁻¹ · (p⁻¹ ·ₗ h) · concat_V_pp p r.

Definition cancelR {A:𝓤} {x y z : A} (p q : x = y) (r : y = z) :
  p · r = q · r → p = q
:= λ h, (concat_pp_V _ _)⁻¹ · (h ·ᵣ r⁻¹) · concat_pp_V _ _.

(* Section 2.2: Functions are functors *)

Definition ap `(f : A → B) `(p:a = b :> A) : f a = f b :=
  match p with refl => refl end.
Arguments ap : simpl nomatch.

Definition ap2 `(f : A → B → C) `(p:a = a' :> A) `(q:b = b' :> B) : f a b = f a' b' :=
  match p, q with refl, refl => refl end.
Arguments ap2 : simpl nomatch.

(* Lemma 2.2.2 i : Functorality of functions *)
Definition ap_1 {A B : 𝓤} (x : A) (f : A → B) : ap f 1 = 1 :> (f x = f x)
:= refl.

Definition ap_pp {A B : 𝓤} (f : A → B) {x y z : A} (p : x = y) (q : y = z) :
  ap f (p · q) = (ap f p) · (ap f q)
:= match q with refl => match p with refl => refl end end.

(* Lemma 2.2.2 ii *)
Definition inverse_ap {A B : 𝓤} (f : A → B) {x y : A} (p : x = y) :
  (ap f p)⁻¹ = ap f p⁻¹
:= match p with refl => refl end.

Definition ap_V {A B : 𝓤} (f : A → B) {x y : A} (p : x = y) :
  ap f p⁻¹ = (ap f p)⁻¹
:= match p with refl => refl end.

(* Lemma 2.2.2 iv, iii : Functorality of ap *)
Definition ap_id {A : 𝓤} {x y : A} (p : x = y) : ap id p = p
:= match p with refl => refl end.

Definition ap_compose {A B C : 𝓤} (f : A → B) (g : B → C) {x y : A} (p : x = y) :
  ap (g ∘ f) p = ap g (ap f p)
:= match p with refl => refl end.

Definition ap_compose' {A B C : 𝓤} (f : A → B) (g : B → C) {x y : A} (p : x = y) :
  ap (λ a, g (f a)) p = ap g (ap f p)
:= match p with refl => refl end.


(* Section 2.3: Type families are fibrations *)

Definition transport `(C : A → 𝓤) `(p : x = y :> A) : C x → C y
:= λ u, match p with refl => u end.
Arguments transport : simpl nomatch.
Notation "p # x" := (transport _ p x) (right associativity, at level 65, only parsing) : path_scope.

Definition lift `{P:A → 𝓤} `(u : P x) `(p : x = y) : (x;u) = (y;(p#u))
:= match p with refl => refl end.
Arguments lift : simpl nomatch.

Definition apd `{P:A → 𝓤} (f : Π x, P x) `(p : x = y) : p # f x = f y
:= match p with refl => refl end.
Arguments apd : simpl nomatch.

Definition transport_const {A B:𝓤} `(p : x = y :> A) (b:B) : transport (λ _, B) p b = b
:= match p with refl => refl end.
Arguments transport_const : simpl nomatch.

(* Lemma 2.3.8 *)
Definition apd_nondep `(f:A → B) `(p : x = y :> A) : apd f p = transport_const p (f x) · ap f p
:= match p with refl => refl end.

Definition transport_1 `(P : A → 𝓤) `(u : P x) : 1 # u = u := refl.

(* Lemma 2.3.9 *)
Definition transport_pp `(P : A → 𝓤) {x y z : A} (p : x = y) (q : y = z) (u : P x) :
  p · q # u = q # p # u
:= match q with refl =>
     match p with refl => refl end
   end.

Definition transport_pV `(P : A → 𝓤) `(p : x = y) (z : P y)
  : p # p⁻¹ # z = z
:= (transport_pp P p⁻¹ p z)⁻¹ · ap (λ r, transport P r z) (concat_Vp p).

Definition transport_Vp `(P : A → 𝓤) `(p : x = y) (z : P x)
  : p⁻¹ # p # z = z
:= (transport_pp P p p⁻¹ z)⁻¹ · ap (λ r, transport P r z) (concat_pV p).

(* Lemma 2.3.10 *)
Definition transport_compose {A B:𝓤} (P : B → 𝓤) (f : A → B) `(p : x = y) (z : P (f x))
  : transport (P ∘ f) p z  =  transport P (ap f p) z
:= match p with refl => refl end.

(* Lemma 2.3.11 *)
Definition transport_fun_family {A:𝓤} (P Q : A → 𝓤) (f : Π x, P x → Q x) `(p : x = y)
  (u : P x) : transport Q p (f x u) = f y (transport P p u)
:= match p with refl => refl end.


(* Section 2.4: Homotopies and Equivalences *)

Definition Homotopy `{P:A → 𝓤} (f g : Π x, P x) := Π x, f x = g x.
Notation "f ~ g" := (Homotopy f g) (at level 70, no associativity) : type_scope.
Delimit Scope homotopy_scope with hom.
Bind Scope homotopy_scope with Homotopy.

(* Lemma 2.4.2 *)
Section homotopy_is_an_equivalence.
  Context `{P:A → 𝓤}.

  Definition hom_refl (f : Π x, P x) : f ~ f := λ x, refl.
  Definition hom_inverse {f g : Π x, P x} : f ~ g → g ~ f := λ H x, (H x)⁻¹.
  Definition hom_concat {f g h : Π x, P x} : f ~ g → g ~ h → f ~ h := λ F G x, F x · G x.
End homotopy_is_an_equivalence.

Notation "1" := (hom_refl _) : homotopy_scope.
Notation "p ⁻¹" := (hom_inverse p) : homotopy_scope.
Notation "p · q" := (hom_concat p q) : homotopy_scope.

(* Lemma 2.4.3 *)
Definition hom_natural {A B : 𝓤} {f g : A → B} (H:f ~ g) `(p: x = y :> A) :
  H x · ap g p = ap f p · H y.
Proof. destruct p. simpl. exact (concat_p1 _ · (concat_1p _)⁻¹). Defined.

(* Corollary 2.4.4 *)
Definition hom_id_natural `{f:A → A} (H:f ~ id) (x:A) :
  H (f x) = ap f (H x).
Proof.
  apply cancelR with (H x).
  exact ((H (f x) ·ₗ (ap_id _)⁻¹) · hom_natural H (H x)).
Defined.

Definition hom_compose {A B C:𝓤} {f g : A → B} {h k : B → C} : h ~ k → f ~ g → h ∘ f ~ k ∘ g
  := λ β α x, β _ · ap k (α _).
Notation "β ∗ α" := (hom_compose β α) : homotopy_scope.

Definition hom_compose_alt {A B C:𝓤} {f g : A → B} {h k : B → C} : h ~ k → f ~ g → h ∘ f ~ k ∘ g
  := λ β α x, ap h (α _) · β _.


Local Open Scope homotopy_scope.

Definition hom_compose_natural {A B C:𝓤} {f g : A → B} {h k : B → C} (β:h ~ k) (α:f ~ g)
  : β ∗ α ~ hom_compose_alt β α
  := λ x, hom_natural β (α x).

Definition hom_whiskerR {A B C : 𝓤} {g h : B → C} (β : g ~ h) (f : A → B)
  : g ∘ f ~ h ∘ f := β ∗ 1.
Notation "β ∘ᵣ f" := (hom_whiskerR β f) : homotopy_scope.

Definition hom_whiskerL {A B C : 𝓤} (h : B → C) {f g : A → B} (α : f ~ g)
  : h ∘ f ~ h ∘ g := 1 ∗ α.
Notation "h ∘ₗ α" := (hom_whiskerL h α) : homotopy_scope.


Definition qinv `(f:A → B) := Σ (g:B → A), (f ∘ g ~ id) × (g ∘ f ~ id).

Definition qinv_fun {A B} {f:A → B} : qinv f → B → A := pr₁.
Coercion qinv_fun : qinv >-> Funclass.

Definition qinv_id A : qinv (@id A) := (id; ((λ x, refl), (λ x, refl))).

Definition qinv_inverse `{f:A → B} (g:qinv f) : qinv g.
Proof. destruct g as [g[α β]]. exact (f;(β,α)). Defined.

Definition qinv_compose {A B C} {h:B → C} {f:A → B} : qinv f → qinv h → qinv (h ∘ f).
Proof. intros [g[α β]] [k[γ δ]]. exists (g ∘ k). split.
+ exact ((h ∘ₗ α ∘ᵣ k) · γ).
+ exact ((g ∘ₗ δ ∘ᵣ f) · β).
Defined.

Definition isequiv {A B} (f:A → B) := (Σ (g:B → A), f ∘ g ~ id) × (Σ (h:B → A), h ∘ f ~ id).
Existing Class isequiv.

Definition qinv_to_isequiv `{f:A → B} (g:qinv f) : isequiv f.
Proof. destruct g as [g[α β]]. exact ((g;α),(g;β)). Defined.
Coercion qinv_to_isequiv : qinv >-> isequiv.
Hint Extern 10 (isequiv ?f) => match goal with g : qinv f |- _ => eexact (qinv_to_isequiv g) end : typeclass_instances.

Definition isequiv_to_qinv `{f:A → B} (e:isequiv f) : qinv f.
Proof. destruct e as [[g α][h β]].
  pose proof (β ∘ᵣ g)⁻¹ · (h ∘ₗ α) : g ~ h as γ.
  pose proof (γ ∘ᵣ f) · β : g ∘ f ~ id as β'.
  exact (g;(α,β')).
Defined.
Coercion isequiv_to_qinv : isequiv >-> qinv.

Local Close Scope homotopy_scope.
Local Close Scope path_scope.

Definition id_isequiv A : isequiv (@id A) := ((id; λ x, refl), (id; λ x, refl)).
Hint Extern 2 (isequiv (@id ?A)) => eexact (id_isequiv A) : typeclass_instances.

Instance inverse_from_isequiv `(f:A → B) {e:isequiv f} : InverseFunction f := (e:qinv f).
Definition isequiv_inverse {A B} (f:A → B) {e:isequiv f} : isequiv f⁻¹ := qinv_inverse e.
Hint Extern 2 (isequiv (@inv_fun _ _ _ (inverse_from_isequiv _))) => eapply @isequiv_inverse : typeclass_instances.

Definition compose_isequiv {A B C} (f:A → B) (g:B → C) : isequiv f → isequiv g → isequiv (g ∘ f)
:= λ e1 e2, qinv_compose e1 e2.
Hint Extern 2 (isequiv (_ ∘ _)) => eapply @compose_isequiv : typeclass_instances.

Definition equiv_linv_hom `(f:A → B) {e:isequiv f} : f⁻¹ ∘ f ~ id := π₂ (e:qinv f).2 .
Definition equiv_rinv_hom `(f:A → B) {e:isequiv f} : f ∘ f⁻¹ ~ id := π₁ (e:qinv f).2 .

Definition Equiv (A B : 𝓤) := sig (@isequiv A B).
Notation "A ≃ B" := (Equiv A B) (at level 75, no associativity) : type_scope.
Delimit Scope equiv_scope with equiv.
Bind Scope equiv_scope with Equiv.

Definition Equiv_fun {A B} : A ≃ B → A → B := pr₁.
Coercion Equiv_fun : Equiv >-> Funclass.
Hint Extern 0 (isequiv (Equiv_fun ?f)) => eexact (f.2) : typeclass_instances.

Definition eqv `(f:A → B) {e:isequiv f} : A ≃ B := (f; e).

Definition Equiv_from_qinv `(f:A → B) (g:qinv f) : A ≃ B := (f; _).

Definition Equiv_from_qinv_alt `(f:A → B) (g:B → A) (α: f ∘ g ~ id) (β: g ∘ f ~ id)
  : A ≃ B := (f;((g;α),(g;β))).

(* Lemma 2.4.12 *)
Section Equiv_is_an_equivalence.
  Definition equiv_id A : A ≃ A := (id; _).
  Definition equiv_inverse {A B} : A ≃ B → B ≃ A := λ f, (f⁻¹; _).
  Definition equiv_concat {A B C} : A ≃ B → B ≃ C → A ≃ C := λ f g, (g ∘ f; _).
End Equiv_is_an_equivalence.

Notation "1" := (equiv_id _) : equiv_scope.
Notation "p ⁻¹" := (equiv_inverse p) : equiv_scope.
Notation "p · q" := (equiv_concat p q) : equiv_scope.

Local Open Scope equiv_scope.

Definition equiv_concat2 {A B C} {f g:A ≃ B} {h k:B ≃ C} : f = g → h = k → f · h = g · k
:= λ p q, ap2 equiv_concat p q.
Notation "p ∗ q" := (equiv_concat2 p q) : equiv_scope.

Definition equiv_whiskerL {A B C} (f : A ≃ B) {h k : B ≃ C} (p: h = k) : f · h = f · k
:= (refl f ∗ p)%equiv.
Notation "f ·ₗ p" := (equiv_whiskerL f p) : equiv_scope.

Definition equiv_whiskerR {A B C} {f g : A ≃ B} (p: f = g) (h : B ≃ C) : f · h = g · h
:= (p ∗ refl h)%equiv.
Notation "p ·ᵣ h" := (equiv_whiskerR p h) : equiv_scope.

Local Close Scope equiv_scope.

Local Open Scope path_scope.

Definition path_precomp_isequiv `(p:x = y :> A) z : isequiv (λ (q:y = z), p · q) .
Proof.
  apply qinv_to_isequiv. exists (p⁻¹ ·).
  split; intros q; [ exact (concat_p_Vp _ _) | exact (concat_V_pp _ _) ].
Defined.
Hint Extern 2 (isequiv (_ ·)) => eapply @path_precomp_isequiv : typeclass_instances.

Definition path_postcomp_isequiv `(q:y = z :> A) x : isequiv (λ (p:x = y), p · q) .
Proof.
  apply qinv_to_isequiv. exists (· q⁻¹).
  split; intros p; [ exact (concat_pV_p _ _) | exact (concat_pp_V _ _) ].
Defined.
Hint Extern 2 (isequiv (· _)) => eapply @path_postcomp_isequiv : typeclass_instances.

Definition transport_isequiv `(B:A → 𝓤) `(p:x = y :> A) : isequiv (transport B p).
Proof.
  apply qinv_to_isequiv. exists (transport B p⁻¹).
  split; intros z; [ exact (transport_pV _ _ _) | exact (transport_Vp _ _ _) ].
Defined.
Hint Extern 2 (isequiv (transport _ _)) => eapply @transport_isequiv : typeclass_instances.


(* Section 2.6: Cartesian product types *)
Definition pair_eq_intro {A B} (x y : A × B) : (π₁ x = π₁ y) × (π₂ x = π₂ y) → x = y.
Proof. destruct x as [a b], y as [a' b']. simpl. intros [[] []]. exact refl. Defined.
Notation "pair⁼" := (pair_eq_intro _ _) : path_scope.

Definition pair_unique {A B} (x : A × B) : x = (π₁ x, π₂ x)
  := pair_eq_intro x (π₁ x, π₂ x) (refl, refl).

Definition pair_eq_compute {A B} {x y : A × B} :
  (λ r, (ap π₁ r, ap π₂ r)) ∘ pair_eq_intro x y ~ id.
Proof. destruct x as [a b], y as [a' b']. intros [p q]. simpl in p,q. destruct p,q. exact refl. Defined.

Definition pair_eq_compute1 {A B} {x y : A × B} (p:π₁ x = π₁ y) q
  : ap π₁ (pair⁼ (p,q)) = p
:= ap π₁ (pair_eq_compute (p,q)).

Definition pair_eq_compute2 {A B} {x y : A × B} (p:π₁ x = π₁ y) q
  : ap π₂ (pair⁼ (p,q)) = q
:= ap π₂ (pair_eq_compute (p,q)).

Definition pair_eq_unique {A B} {x y : A × B} (r: x = y) :
  r = pair⁼ (ap π₁ r, ap π₂ r).
Proof. destruct r, x as [a b]. exact refl. Defined.

(* Theorem 2.6.2 *)
Definition pair_eq_equiv {A B} (x y : A × B) : x = y ≃ (π₁ x = π₁ y) × (π₂ x = π₂ y)
:= (Equiv_from_qinv (λ r, (ap π₁ r, ap π₂ r)) (pair⁼; (pair_eq_compute, pair_eq_unique⁻¹)%hom)).

Definition pair_eq_inverse {A B} {x y : A × B} (p:π₁ x = π₁ y) q
  : (pair⁼ (p,q))⁻¹ = pair⁼ (p⁻¹,q⁻¹).
Proof. destruct x as [a b], y as [a' b']. simpl in p,q. destruct p,q. exact refl. Defined.

Definition pair_eq_concat {A B} {x y z: A × B} (p:π₁ x = π₁ y) q (p':π₁ y = π₁ z) q'
  : pair⁼ (p,q) · pair⁼ (p',q') = pair⁼ (p · p', q · q').
Proof. destruct x as [a b], y as [a' b'], z as [a'' b''].
  simpl in p,q,p',q'. destruct p,q,p',q'. exact refl.
Defined.

(* Theorem 2.6.4 *)
Definition pair_transport {Z} (A B: Z → 𝓤) {z w} (p:z = w :> Z) (x:A z × B z)
  : transport (λ z, A z × B z) p x = (transport A p (π₁ x), transport B p (π₂ x)).
Proof. destruct p. simpl. exact (pair_unique x). Defined.

(* Theorem 2.6.5 *)
Section pair_ap.
  Context {A B A' B' : 𝓤} (g:A → A') (h:B → B').
  Let f z := (g (π₁ z), h (π₂ z)).

  Definition pair_ap {x y : A × B} (p:π₁ x = π₁ y) (q:π₂ x = π₂ y)
  : ap f (pair⁼ (p,q)) = pair_eq_intro (f x) (f y) (ap g p, ap h q).
  Proof. destruct x as [a b], y as [a' b']. simpl in p,q. destruct p,q. exact refl. Defined.
End pair_ap.


(* Section 2.7: Σ-types *)
Definition sig_apd
 `{P: A → 𝓤} `{f:sig P → B} `{Q:B → Type} (g:Π x:sig P, Q (f x))
  {x y : sig P} (p:x = y)
  : ap f p # g x = g y
:= (transport_compose Q f p (g x))⁻¹ · apd g p.

Definition sig_eq_elim `{B: A → 𝓤} {x y : sig B}
  : x = y → Σ (p:pr₁ x = pr₁ y), p # pr₂ x = pr₂ y
:= λ p, (ap pr₁ p; sig_apd pr₂ p).

Definition sig_eq_intro `{B: A → 𝓤} (x y : sig B)
  :  (Σ (p:pr₁ x = pr₁ y), p # pr₂ x = pr₂ y) → x = y.
Proof. destruct x as [a b], y as [a' b']; simpl.
  intros [p q]. destruct p. simpl in q. destruct q. exact refl.
Defined.
Arguments sig_eq_intro : simpl nomatch.
Notation "sig⁼" := (sig_eq_intro _ _) : path_scope.

(* Corollary 2.7.3 *)
Definition sig_unique `{B: A → 𝓤} (x : sig B) : x = (pr₁ x; pr₂ x)
:= sig_eq_intro x (pr₁ x; pr₂ x) (refl; refl).

Definition sig_eq_compute `{B: A → 𝓤} {x y : sig B} :
  sig_eq_elim (x:=x) (y:=y) ∘ sig⁼ ~ id.
Proof. destruct x as [a b], y as [a' b']. intros [p q]. simpl in p,q.
  destruct p. simpl in q. destruct q. exact refl.
Defined.

Definition sig_eq_compute1 `{B: A → 𝓤} {x y : sig B} (p:pr₁ x = pr₁ y) q
  : ap pr₁ (sig⁼ (p;q)) = p
:= ap pr₁ (sig_eq_compute (p;q)).

Definition sig_eq_unique `{B: A → 𝓤} {x y : sig B} (r: x = y) :
  r = sig⁼ (ap pr₁ r; sig_apd pr₂ r).
Proof. destruct r, x as [a b]. exact refl. Defined.

(* Theorem 2.7.2 *)
Definition sig_eq_equiv `{B: A → Type} (x y : sig B)  : x = y ≃ Σ (p:pr₁ x = pr₁ y), p # pr₂ x = pr₂ y
:= (Equiv_from_qinv sig_eq_elim (sig⁼; (sig_eq_compute, sig_eq_unique⁻¹)%hom)).

Section sig_transport.
  Context `{P: A → 𝓤} (Q: sig P → 𝓤).
  Let R x := Σ (u: P x), Q (x; u).

  Definition sig_transport `(p : x = y :> A) (u: P x) (z : Q (x; u))
  : transport R p (u; z) = (p # u; transport Q (lift u p) z).
  Proof. destruct p. exact refl. Defined.
End sig_transport.

Definition apd2 `(f:A → B) `{P: A → 𝓤} `{Q:B → 𝓤} (g:Π (x:A), P x → Q (f x))
  `(p:x = y) {u:P x} {v: P y} (q:p # u = v) : ap f p # g x u = g y v
:= (transport_compose Q f p (g x u))⁻¹ · transport_fun_family P (Q ∘ f) g p u · ap (g y) q.

Section ap_sig_eq.
  Context `(f:A → B) `{P: A → 𝓤} `{Q:B → 𝓤} (g:Π (x:A), P x → Q (f x)).
  Let h z : sig Q := (f z.1; g z.1 z.2).

  Definition ap_sig_eq {x y : sig P} (p:x.1 = y.1) (q:p # x.2 = y.2) :
    ap h (sig⁼(p; q)) = sig_eq_intro (h x) (h y) (ap f p; apd2 f g p q).
  Proof. destruct x as [a u], y as [b v].
    simpl in p. destruct p.
    simpl in q. destruct q.
    exact refl.
  Defined.
End ap_sig_eq.


(* Section 2.8: The unity type *)

Definition unit_eq_intro {x y : 𝟏} : x = y.
Proof. destruct x,y. exact refl. Defined.
Notation "unit⁼" := unit_eq_intro : path_scope.

Definition unit_unique x : x = ★ := unit⁼.

Definition unit_eq_unique {x y : 𝟏} (p:x = y) : p = unit⁼.
Proof. destruct p, x. exact refl. Defined.

(* Theorem 2.8.1 *)
Definition unit_eq_equiv (x y : 𝟏) : x = y ≃ 𝟏
:= (Equiv_from_qinv_alt (λ _, ★) (λ _, unit⁼) (λ _, unit⁼) unit_eq_unique⁻¹)%hom.


(* Section 2.9: Π-types and the function extensionality axiom *)
Definition happly `{P:A → 𝓤} {f g : Π x, P x} (p:f = g) : f ~ g
:= match p with refl => hom_refl _ end.
Arguments happly : simpl nomatch.

Class StrongFunext := strong_funext : Π `{P:A → 𝓤} (f g : Π x, P x), isequiv (happly (f:=f) (g:=g)).
Hint Extern 2 (isequiv happly) => eapply @strong_funext : typeclass_instances.

Section StrongFunext_props.
  Context {SF:StrongFunext} `{P:A → 𝓤}.

  Definition funext_equiv (f g : Π x, P x) : (f = g) ≃ (f ~ g) := (happly; _).

  Context {f g : Π x, P x}.

  Definition funext (H:f ~ g) : f = g := (inv_fun happly) H.
  Definition funext_compute (H:f ~ g) : happly (funext H) = H := equiv_rinv_hom happly H.
  Definition funext_unique (p:f = g) : p = funext (happly p) := (equiv_linv_hom happly p)⁻¹.
End StrongFunext_props.

Class Funext := weak_funext : Π `{P:A → 𝓤} {f g : Π x, P x}, f ~ g → f = g.

Instance StrongFunext_from_weak : Funext → StrongFunext.
Proof. intros WF A P f g. apply qinv_to_isequiv.
  exists (λ H, (weak_funext 1%hom)⁻¹ · weak_funext H). split.
+ intro H. pose (H' := λ x, (g x; H x)).
  change g with (λ x, (H' x).1).
  change H with (λ x, (H' x).2).
  clearbody H'. clear H g.
  assert ((λ x, (f x; 1)) = H') as [].
  * apply WF. intro x. destruct (H' x) as [_ []]. exact refl.
  * exact (ap happly (concat_Vp (weak_funext (hom_refl f)))).
+ intros []. exact (concat_Vp _).
Defined.

Definition funext_id `{!StrongFunext} `{P:A → 𝓤} (f : Π x, P x) : funext 1%hom = refl f
  := (funext_unique 1)⁻¹.

Definition funext_concat {SF:StrongFunext} `{P:A → 𝓤} {f g h: Π x, P x} (G:f ~ g) (H:g ~ h)
   : funext (G · H) = funext G · funext H.
Proof.
  refine ((ap funext (ap2 hom_concat (funext_compute G) (funext_compute H)))⁻¹ · _).
  set (p := funext G). set (q := funext H). clearbody p q. destruct p, q. exact (funext_id f).
Defined.

Definition funext_inverse {SF:StrongFunext} `{P:A → 𝓤} {f g: Π x, P x} (H:f ~ g)
   : funext H⁻¹ = (funext H)⁻¹.
Proof.
  refine (ap (λ x, funext x⁻¹) (funext_compute H)⁻¹ · _).
  set (p := funext H). clearbody p. destruct p. exact (funext_id f).
Defined.


(* Section 2.10: Universes and the univalence axiom *)

Definition transport_id_isequiv {A B: Type} (p:A = B) : isequiv (transport id p)
  := match p with refl => _ : isequiv id end.
Arguments transport_id_isequiv : simpl nomatch.
Hint Extern 2 (isequiv (transport (@id Type) ?p)) => eexact (transport_id_isequiv p) : typeclass_instances.

(* Lemma 2.10.1 *)
Definition idtoeqv {A B:Type} (p:A = B) : A ≃ B := (transport id p; _).

Class Univalence := idtoeqv_isequiv : Π A B, isequiv (idtoeqv (A:=A) (B:=B)).
Hint Extern 2 (isequiv idtoeqv) => eapply @idtoeqv_isequiv : typeclass_instances.

Section Univalence_props.
  Context {U:Univalence}.

  Definition univalence A B : (A = B) ≃ (A ≃ B) := (idtoeqv; _).

  Context {A B : 𝓤}.

  Definition ua : A ≃ B → A = B := inv_fun idtoeqv.
  Definition ua_compute (f:A ≃ B) : idtoeqv (ua f) = f := equiv_rinv_hom idtoeqv f.
  Definition ua_unique (p:A = B) : p = ua (idtoeqv p) := (equiv_linv_hom idtoeqv p)⁻¹.
End Univalence_props.

Definition ua_id `{!Univalence} (A:𝓤) : ua 1%equiv = refl A
  := (ua_unique (refl A))⁻¹.

Definition ua_concat `{!Univalence} {A B C: 𝓤} (f:A ≃ B) (g:B ≃ C) : ua (f · g) = ua f · ua g.
Proof.
  refine ((ap ua (ua_compute f ∗ ua_compute g)%equiv)⁻¹ · _).
  set (p := ua f). set (q := ua g). clearbody p q. clear f g.
  destruct p, q. exact (ua_id _).
Defined.

Definition ua_inverse `{!Univalence} {A B: 𝓤} (f:A ≃ B) : ua f⁻¹ = (ua f)⁻¹.
Proof.
  refine ((ap (λ h, ua h⁻¹) (ua_compute f))⁻¹ · _).
  set (p := ua f). clearbody p. clear f. destruct p. exact (ua_id _).
Defined.

(* Lemma 2.10.5 *)
Definition transport_to_idtoeqv `{B: A → 𝓤} `(p:x = y :> A) (u:B x) :
  transport B p u = idtoeqv (ap B p) u
:= transport_compose id B p u.


(* Section 2.11: Identity type *)

Definition hom_inv_natural `{f:A → B} {g:B → A} (H: g ∘ f ~ id) `(p:x = y :> A)
  : H x · p = ap g (ap f p) · H y
:= (_ ·ₗ (ap_id _)⁻¹) · hom_natural H p · (ap_compose _ _ _ ·ᵣ _).

(* Theorem 2.11.1 *)
Definition ap_isequiv `(f:A → B) {e:isequiv f} (a a':A) : isequiv (ap f (a:=a) (b:=a')).
Proof.
  destruct (e : qinv f) as [g[α β]]; clear e.
  apply qinv_to_isequiv. exists (λ (p:f a = f a'), (β _)⁻¹ · ap g p · β _).
  split; unfold compose, id; intros p.
+ refine ((concat_V_pp (α _) _)⁻¹ · (_ ·ₗ _) · _).
  refine (hom_inv_natural α (ap f _) · (ap (ap f) _ ·ᵣ _)).
  refine ((ap_compose f g _)⁻¹ · _).
  refine ((concat_pp_V _ (β _))⁻¹ · _).
  refine ( ((hom_natural β _)⁻¹ · (_ ·ₗ ap_id _)) ·ᵣ _ · _) .
  refine (_ ·ᵣ _ · _).
  refine (concat_p_pp _ _ _ · (_ ·ᵣ _)).
  refine (concat_p_pp _ _ _ · (concat_pV _ ·ᵣ _)).
  refine (concat_pp_p _ _ _ · (concat_1p _ ∗ concat_pV _)).
  refine (_ ·ₗ _ · _).
  refine (ap (ap f) (concat_p1 _) ·ᵣ _ · (hom_inv_natural α p)⁻¹).
  exact (concat_V_pp _ _).
+ exact (concat_pp_p _ _ _ · (_ ·ₗ (hom_inv_natural β p)⁻¹) · concat_V_pp _ _).
Defined.
Hint Extern 2 (isequiv (ap _)) => eapply @ap_isequiv : typeclass_instances.

Definition concat_1p1 `(p:a = b :> A) : 1 · p · 1 = p
:= concat_p1 _ · concat_1p _.

(* Lemma 2.11.2 *)
Definition transport_Id_ax `(a:A) `(p:x₁ = x₂) (q:a = x₁) : transport (λ x, a = x) p q = q · p.
Proof. destruct p. exact (concat_p1 _)⁻¹. Defined.

Definition transport_Id_xa `(a:A) `(p:x₁ = x₂) (q:x₁ = a) : transport (λ x, x = a) p q = p⁻¹ · q.
Proof. destruct p. exact (concat_1p _)⁻¹. Defined.

Definition transport_Id_xx `(p:x₁ = x₂ :> A) (q:x₁ = x₁) : transport (λ x, x = x) p q = p⁻¹ · q · p.
Proof. destruct p. exact (concat_1p1 _)⁻¹. Defined.

(* Theorem 2.11.3 *)
Definition transport_Id {A B} (f g: A → B) `(p:a = a') (q:f a = g a)
  : transport (λ x, f x = g x) p q = (ap f p)⁻¹ · q · (ap g p).
Proof. destruct p. exact (concat_1p1 _)⁻¹. Defined.

(* Theorem 2.11.4 *)
Definition transport_Id_dep `{B:A → 𝓤} (f g: Π x, B x) `(p:a = a') (q:f a = g a)
  : transport (λ x, f x = g x) p q = (apd f p)⁻¹ · ap (transport B p) q · (apd g p).
Proof. destruct p. simpl. destruct q. exact refl. Defined.

(* Theorem 2.11.5 *)
Definition transport_Id_equiv `(p:a = a' :> A) (q:a = a) (r:a' = a')
  : (transport (λ x, x = x) p q = r) ≃ (q · p = p · r).
Proof. destruct p. exact (eqv (((concat_p1 _) ·) ∘ (· (concat_1p _)⁻¹))). Defined.


(* Section 2.12: Coproducts *)
Section coproducts.
  Context {A B:𝓤}.
  Section inl.
    Context (a₀:A).
    Let code (x : A + B) : 𝓤 := match x with inl a => a₀ = a | _ => 𝟎 end.
    Let encode (x : A + B) (p:inl a₀ = x) : code x := transport code p (refl a₀).
    Let decode (x : A + B) (c:code x) : inl a₀ = x.
    Proof. destruct x; [ exact (ap inl c) | destruct c]. Defined.

    Let β (x : A + B) : decode x ∘ encode x ~ id.
    Proof. intros []. exact refl. Defined.

    Let α (x : A + B) : encode x ∘ decode x ~ id.
    Proof. destruct x.
    + intros c.
      refine ((transport_compose code inl c _)⁻¹ · _).
      refine (transport_Id_ax _ _ _ · _).
      exact (concat_1p _).
    + intros [].
    Defined.

    Definition coproduct_inl_equiv_code (x : A + B) : (inl a₀ = x) ≃ code x
      := Equiv_from_qinv_alt (encode x) (decode x) (α x) (β x).
  End inl.

  Section inr.
    Context (b₀:B).
    Let code (x : A + B) : Type := match x with inr b => b₀ = b | _ => 𝟎 end.
    Let encode (x : A + B) (p:inr b₀ = x) : code x := transport code p (refl b₀).
    Let decode (x : A + B) (c:code x) : inr b₀ = x.
    Proof. destruct x; [ destruct c | exact (ap inr c) ]. Defined.

    Let β (x : A + B) : decode x ∘ encode x ~ id.
    Proof. intros []. exact refl. Defined.

    Let α (x : A + B) : encode x ∘ decode x ~ id.
    Proof. destruct x.
    + intros [].
    + intros c.
      refine ((transport_compose code inr c _)⁻¹ · _).
      refine (transport_Id_ax _ _ _ · _).
      exact (concat_1p _).
    Defined.

    Definition coproduct_inr_equiv_code (x : A + B) : (inr b₀ = x) ≃ code x
      := Equiv_from_qinv_alt (encode x) (decode x) (α x) (β x).
  End inr.

  Definition coproduct_inl_equiv a₁ a₂ : (@inl A B a₁ = inl a₂) ≃ (a₁ = a₂)
  := coproduct_inl_equiv_code _ _.

  Definition coproduct_inr_equiv b₁ b₂ : (@inr A B b₁ = inr b₂) ≃ (b₁ = b₂)
  := coproduct_inr_equiv_code _ _.

  Definition coproduct_inl_inr_equiv a b : (@inl A B a = inr b) ≃ 𝟎
  := coproduct_inl_equiv_code _ _.
  Definition coproduct_inr_inl_equiv b a : (@inr A B b = inl a) ≃ 𝟎
  := coproduct_inr_equiv_code _ _.

  Definition inl_eq_intro {a₁ a₂} : (a₁ = a₂) → (inl a₁ = inl a₂) := (coproduct_inl_equiv _ _)⁻¹.
  Definition inr_eq_intro {b₁ b₂} : (b₁ = b₂) → (inr b₁ = inr b₂) := (coproduct_inr_equiv _ _)⁻¹.
End coproducts.
Notation "inl⁼" := inl_eq_intro.
Notation "inr⁼" := inr_eq_intro.

Section sum_ap.
  Context {A B A' B' : 𝓤} (g:A → A') (h:B → B').
  Let f (z:A + B) := match z with
  | inl a => inl (g a)
  | inr b => inr (h b)
  end.

  Definition inl_ap `(p: x = y :> A) : ap f (inl⁼ p) = inl⁼ (ap g p)
  := match p with refl => refl end.

  Definition inr_ap `(q: x = y :> B) : ap f (inr⁼ q) = inr⁼ (ap h q)
  := match q with refl => refl end.
End sum_ap.

Local Open Scope bool_scope.

Definition bool_equiv_coproduct : 𝟐 ≃ 𝟏 + 𝟏.
Proof. apply (Equiv_from_qinv_alt
                (λ b, match b with 0 => inl ★ | 1 => inr ★ end)
                (λ x, match x with inl _ => 0 | inr _ => 1 end) ).
+ intros [[]|[]]; exact refl.
+ intros [|]; exact refl.
Defined.

Definition bool_0_eq_0_equiv : 0 = 0 ≃ 𝟏 :=
  (eqv (A:= 0 = 0) (ap bool_equiv_coproduct) · coproduct_inl_equiv _ _ · unit_eq_equiv _ _)%equiv.
Definition bool_1_eq_1_equiv : 1 = 1 ≃ 𝟏 :=
  (eqv (A:= 1%bool = 1%bool) (ap bool_equiv_coproduct) · coproduct_inr_equiv _ _ · unit_eq_equiv _ _)%equiv.
Definition bool_0_ne_1 : 0 = 1 ≃ 𝟎 :=
  (eqv (A:= 0 = 1%bool) (ap bool_equiv_coproduct) · coproduct_inl_inr_equiv _ _)%equiv.
Definition bool_1_ne_0 : 1 = 0 ≃ 𝟎 :=
  (eqv (A:= 1%bool = 0) (ap bool_equiv_coproduct) · coproduct_inr_inl_equiv _ _)%equiv.

Local Close Scope bool_scope.

(* Section 2.13: Natural numbers *)
Local Open Scope nat_scope.
Section naturals.
  Let code : ℕ → ℕ → 𝓤₀ := fix F (a b:ℕ) := match a, b with
  | 0, 0 => 𝟏
  | succ m, 0 => 𝟎
  | 0, succ n => 𝟎
  | succ m, succ n => F m n
  end.
  Let r : Π a, code a a := fix F (a:ℕ) := match a with
  | 0 => ★
  | succ n => F n
  end.

  Let encode m n (p:m = n) : code m n := transport (code m) p (r m).

  Let decode : Π m n, (code m n) → m = n := fix F (a b:ℕ) := match a, b with 
  | 0, 0 => λ c, refl
  | succ m, 0 => λ c, match c with end
  | 0, succ n => λ c, match c with end
  | succ m, succ n => λ c, ap succ (F m n c)
  end.

  Let β (m n : ℕ) : decode m n ∘ encode m n ~ id.
  Proof. intros []. change (decode m m (r m) = refl). induction m.
  + exact refl.
  + exact (ap (ap succ) IHm · ap_1 _ _).
  Defined.

  Let α : Π m n, encode m n ∘ decode m n ~ id.
  Proof. refine (fix F (a b:ℕ) := match a, b with 
  | 0, 0 => _
  | succ m, 0 => λ c, match c with end
  | 0, succ n => λ c, match c with end
  | succ m, succ n => λ c, _
  end).
  + intros []. exact refl.
  + unfold compose, id; simpl. unfold encode.
    refine ((transport_compose (code (succ m)) succ _ _)⁻¹ · _).
    change (transport (code m) (decode m n c) (r m) = c).
    change (encode m n (decode m n c) = c).
    exact (F m n c).
  Defined.

  Definition nat_eq_equiv_code m n : (m = n) ≃ code m n
  := Equiv_from_qinv_alt (encode m n) (decode m n) (α m n) (β m n).
End naturals.
Definition nat_eq_equiv_S0 m : (succ m = 0) ≃ 𝟎  := nat_eq_equiv_code _ _.
Definition nat_eq_equiv_0S m : (0 = succ m) ≃ 𝟎  := nat_eq_equiv_code _ _.
Definition nat_eq_equiv_SS m n : (succ m = succ n) ≃ (m = n)
:= (nat_eq_equiv_code (succ m) (succ n) · (nat_eq_equiv_code m n)⁻¹)%equiv.
Definition nat_discrete : Π (n:ℕ), (n = n) ≃ 𝟏 := fix F (a:ℕ) := match a with
| 0 => nat_eq_equiv_code 0 0
| succ n => (nat_eq_equiv_SS n n · F n)%equiv
end.
Definition nat_decidable : Π m n : ℕ, ((m = n) ≃ 𝟏) + ((m = n) ≃ 𝟎)
:= fix F (a:ℕ) := match a with
| 0 => λ b, match b with
       | 0 => inl (nat_discrete 0)
       | succ m => inr (nat_eq_equiv_0S _)
       end
| succ n => λ b, match b with
       | 0 => inr (nat_eq_equiv_S0 _)
       | succ m => match F n m with
                   | inl E => inl (nat_eq_equiv_SS _ _ · E)%equiv
                   | inr E => inr (nat_eq_equiv_SS _ _ · E)%equiv
                   end
       end
end.
