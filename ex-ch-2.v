Require Import prelude chapter2.

Local Open Scope path_scope.

(*
Exercise 2.1. Show that the three obvious proofs of Lemma 2.1.2 [concatenation of paths] are pairwise equal.
*)
Section ex_2_1.
  Local Definition concat1 {A} {x y z : A} : x = y → y = z → x = z := λ p q, (match p with refl => id end) q.
  Local Definition concat2 {A} {x y z : A} : x = y → y = z → x = z := λ p q, (match q with refl => id end) p.
  Local Definition concat3 {A} {x y z : A} (p:x = y) (q:y = z) : x = z := match p, q with refl, refl => refl end.

  Context {A} {x y z : A} .
  Local Definition concat1_eq_concat2 : Π (p:x = y) (q:y = z), concat1 p q = concat2 p q.
  Proof. refine (path_ind (λ x y p, Π (q:y = z), concat1 p q = concat2 p q) _ x y). clear x y.
         refine (λ x, path_ind (λ x z q, concat1 1 q = concat2 1 q) _ x z).
         exact (λ _, refl).
  Defined.
  Local Definition concat2_eq_concat3 (p:x = y) (q:y = z) : concat2 p q = concat3 p q.
  Proof. destruct p, q. exact refl. Defined.
  Local Definition concat1_eq_concat3 (p:x = y) (q:y = z) : concat1 p q = concat3 p q.
  Proof. destruct p, q. exact refl. Defined.
End ex_2_1.

(*
Exercise 2.2. Show that the three equalities of proofs constructed in the previous exercise form a
commutative triangle. In other words, if the three definitions of concatenation are denoted by
 (p ·₁ q), (p ·₂ q), and (p ·₃ q),
then the concatenated equality
 (p ·₁ q) = (p ·₂ q) = (p ·₃ q)
is equal to the equality
 (p ·₁ q) = (p ·₃ q).
*)
Section ex_2_2.
  Context {A} {x y z : A} (p : x = y) (q : y = z).
  Goal (concat1_eq_concat2 p q) · (concat2_eq_concat3 p q) = concat1_eq_concat3 p q.
  Proof. destruct p, q. exact refl. Defined.
End ex_2_2.

(*
Exercise 2.3. Give a fourth, different, proof of Lemma 2.1.2, and prove that it is equal to the others.
*)

(*
Exercise 2.4. Define, by induction on n, a general notion of n-dimensional path in a type A,
simultaneously with the type of boundaries for such paths.
*)
Section ex_2_4.
  Local Open Scope nat_scope.
  Local Fixpoint npath (n:ℕ) : 𝓤 → 𝓤 := match n with
  | 0 => id
  | succ m => λ A, Σ (x y : A), npath m (x = y)
  end.
End ex_2_4.

(*
Exercise 2.5. Prove that the functions (2.3.6) and (2.3.7) are inverse equivalences.
*)
Section ex_2_5.
  Context {A B} `(p:x = y :> A) (f:A → B).

  (* This is just path_precomp_isequiv from chatper2. *)
  Goal (f x = f y) ≃ ((p # f x) = f y).
  Proof ((transport_const p (f x) ·); _).
End ex_2_5.

(*
Exercise 2.6. Prove that if p : x = y, then the function (p · –) : (y = z) → (x = z) is an
equivalence.
*)
(* See path_precomp_isequiv from chatper2. *)

(*
Exercise 2.7. State and prove a generalization of Theorem 2.6.5 from cartesian products to Σtypes.
*)
(* See ap_sig_eq from chapter2. *)

(*
Exercise 2.8. State and prove an analogue of Theorem 2.6.5 for coproducts.
*)
(* See inl_ap, inr_ap in chapter2. *)

(*
Exercise 2.9. Prove that coproducts have the expected universal property,
(A + B → X) ≃ (A → X) × (B → X).
Can you generalize this to an equivalence involving dependent functions?
*)
Section ex_2_9.
  Context `{!Funext}.
  Context {A B X : 𝓤}.

  Let F : (A + B → X) → (A → X) × (B → X)
  := λ f, (f ∘ inl, f ∘ inr).

  Let G : qinv F.
  Proof. exists ( λ p x, match x with
                         | inl a => π₁ p a
                         | inr b => π₂ p b
                         end ).
    split.
    + intros [f g]. exact refl.
    + intros f. apply funext. intros [a|b]; exact refl.
  Defined.

  Definition coproduct_universal : (A + B → X) ≃ (A → X) × (B → X) := (F; _).
End ex_2_9.

Section ex_2_9_ii.
  Context `{!Funext}.
  Context {A B : 𝓤} {C : A + B → 𝓤}.

  Let F : (Π x, C x) → (Π a, C (inl a)) × (Π b, C (inr b))
  := λ f, (λ a, f (inl a), λ b, f (inr b)).

  Let G : (Π a, C (inl a)) × (Π b, C (inr b)) → Π x, C x.
  Proof. intros [f g] [a|b]; [apply f | apply g]. Defined.

  Definition coproduct_universal_dep : (Π x, C x) ≃ (Π a, C (inl a)) × (Π b, C (inr b)).
  Proof. apply (Equiv_from_qinv_alt F G).
  + intros [f g]. exact refl.
  + intros f. apply funext. intros [a|b]; exact refl.
  Defined.
End ex_2_9_ii.


(*
Exercise 2.10. Prove that Σ-types are “associative”, in that for any A : U and families B : A → U
and C : (∑(x:A) B(x)) → U, we have
∑_(x:A) ∑_(y:B(x)) C((x, y)) ≃ ∑_(p:∑(x:A) B(x)) C(p) .
*)
Section ex_2_10.
  Context `{B:A → 𝓤} (C: (Σ x, B x) → 𝓤).

  Let F : (Σ x (y: B x), C (x; y)) → Σ p, C p
  := λ z, ((z.1; z.2.1); z.2.2).

  Let G : (Σ p, C p) → Σ x (y: B x), C (x; y).
  Proof. intros [[a b] c]. exists a. exists b. exact c. Defined.

  Definition sigma_assoc : (Σ x (y: B x), C (x; y)) ≃ Σ p, C p.
  Proof. apply (Equiv_from_qinv_alt F G).
  + intros [[a b] c]. exact refl.
  + intros [a [b c]]. exact refl.
  Defined.
End ex_2_10.

(*
Exercise 2.11. A (homotopy) commutative square

      h
   P ---> A
   |      |
 k |      | f
   v      v
   B ---> C
      g

consists of functions f, g, h, and k as shown, together with a path f ◦ h = g ◦ k. Note that
this is exactly an element of the pullback (P → A) ×P→C (P → B) as defined in (2.15.11). A
commutative square is called a (homotopy) pullback square if for any X, the induced map
(X → P) → (X → A) ×(X→C) (X → B)
is an equivalence. Prove that the pullback P :≡ A ×C B defined in (2.15.11) is the corner of a
pullback square.
*)
Definition pullback {A B C} (f:A → C) (g:B → C) := Σ a b, f a = g b.
Section ex_2_11.
  Context `{!Funext}.
  Context {A B C} (f:A → C) (g:B → C).
  Notation P := (pullback f g).

  Let h:P → A := pr₁.
  Let k:P → B := λ p, p.2.1.
  Let comm p : f (h p) = g (k p) := p.2.2.

  Context (X : 𝓤).
  Let square := pullback (compose (A:=X) f) (compose g).

  Let comm_hom (u:X → P) : f ∘ h ∘ u ~ g ∘ k ∘ u := λ x, comm (u x).
  Let F : (X → P) → square := λ u, (h ∘ u; (k ∘ u; funext (comm_hom u))).

  Let G : square → (X → P).
  Proof. intros [x₁[x₂ p]] x. exact (x₁ x; (x₂ x; happly p x)). Defined.

  Definition pullback_universal : (X → P) ≃ square.
  Proof. apply (Equiv_from_qinv_alt F G).
  + intros [x₁[x₂ p]].
    do 2 (apply sig⁼; exists refl). simpl.
    exact (ap funext 1 · (funext_unique p)⁻¹).
  + intros u. unfold compose, id, F, G. apply funext. intros x.
    do 2 (apply sig⁼; exists refl). simpl.
    exact (happly (funext_compute (comm_hom u)) x).
  Defined.
End ex_2_11.

(*
Exercise 2.12. Suppose given two commutative squares
A /

C /

E

B /D /F
and suppose that the right-hand square is a pullback square. Prove that the left-hand square is a
pullback square if and only if the outer rectangle is a pullback square.
*)

(*
Exercise 2.13. Show that (2 ≃ 2) ≃ 2.
*)
Require Import chapter3.
Section ex_2_13.
  Local Open Scope bool_scope.

  Instance: isequiv not₂.
  Proof. apply qinv_to_isequiv. exists not₂.
    split; intros [|]; exact refl.
  Defined.

  Let F : (𝟐 ≃ 𝟐) → 𝟐 := λ f, f 0.
  Let G : 𝟐 → (𝟐 ≃ 𝟐) := λ b, match b with 0 => 1%equiv | 1 => eqv not₂ end.

  Let aux1 (f:𝟐 → 𝟐) `{!isequiv f} : f 0 = f 1 ≃ 𝟎 := ((eqv (ap f))⁻¹ · bool_0_ne_1)%equiv.
  Let aux2 (f:𝟐 → 𝟐) `{!isequiv f} : ((0 = f 0) × (1 = f 1)) + ((1 = f 0) × (0 = f 1)).
  Proof. pose proof aux1 f as P.
    destruct (f 0) as [|], (f 1) as [|]; try destruct (P refl); [ right | left ]; exact (refl, refl).
  Defined.

  Let linv `{!Funext} (f:𝟐 ≃ 𝟐) : G (F f) = f :> (𝟐 → 𝟐) .
  Proof. destruct f as [f ?]. apply funext.
    enough ( (G (f 0) 0 = f 0) × (G (f 0) 1 = f 1) ) as P by (intros [|]; apply P).
    destruct (aux2 f) as [[[][]]|[[][]]]; exact (refl, refl).
  Defined.

  Definition bool_auto_equiv_bool `{!Funext} `{Hequiv:Π A B (f:A → B), isProp (isequiv f)} : (𝟐 ≃ 𝟐) ≃ 𝟐.
  Proof. apply (Equiv_from_qinv_alt F G).
  + intros [|]; exact refl.
  + intros f. eapply @subtype_eq.
    * intro p. apply Hequiv.
    * exact (linv f).
  Defined.
End ex_2_13.

(*
Exercise 2.14. Suppose we add to type theory the equality reflection rule which says that if there is
an element p : x = y, then in fact x ≡ y. Prove that for any p : x = x we have p ≡ reflx. (This
implies that every type is a set in the sense to be introduced in §3.1; see §7.2.)



Exercise 2.15. Show that Lemma 2.10.5 can be strengthened to
transportB
(p, –) =B(x)→B(y)
idtoeqv(apB
(p))
without using function extensionality. (In this and other similar cases, the apparently weaker
formulation has been chosen for readability and consistency.)
Exercise 2.16. Suppose that rather than function extensionality (Axiom 2.9.3), we suppose only
the existence of an element
funext : ∏
(A:U)
∏
(B:A→U)
∏
(f ,g:∏(x:A) B(x))
(f ∼ g) → (f = g)
(with no relationship to happly assumed). Prove that in fact, this is sufficient to imply the whole
function extensionality axiom (that happly is an equivalence). This is due to Voevodsky; its proof
is tricky and may require concepts from later chapters.
Exercise 2.17.
(i) Show that if A ' A
0 and B ' B
0
, then (A × B) ' (A
0 × B
0
).
(ii) Give two proofs of this fact, one using univalence and one not using it, and show that the
two proofs are equal.
(iii) Formulate and prove analogous results for the other type formers: Σ, →, Π, and +.
Exercise 2.18. State and prove a version of Lemma 2.4.3 for dependent functions
*)
