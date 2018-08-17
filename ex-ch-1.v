Require Import prelude.

(*
Exercise 1.1. Given functions f : A → B and g : B → C, define their composite g ◦ f : A → C.
Show that we have h ◦ (g ◦ f) ≡ (h ◦ g) ◦ f .
*)
Section ex_1_1.
  (* Composite defined in prelude:

     Print compose.
     compose = λ (A B C : 𝓤) (g : B → C) (f : A → B) (x : A), g (f x)
     : Π A B C : 𝓤, (B → C) → (A → B) → (A → C)
  *)
  Context {A B C D} (f:A → B) (g:B → C) (h:C → D).
  Goal 𝟏. Proof. unify (h ∘ (g ∘ f)) ((h ∘ g) ∘ f). Abort.
End ex_1_1.

(*
Exercise 1.2. Derive the recursion principle for products recA×B using only the projections, and
verify that the definitional equalities are valid. Do the same for Σ-types.
*)
Section ex_1_2.
  Section a.
    Context {A B : 𝓤}.
    Local Definition rec_prod' {C:𝓤} : (A → B → C) → (A × B → C) := λ g p, g (π₁ p) (π₂ p).

    Context (C:𝓤) (g : A → B → C) (a:A) (b:B).
    Goal 𝟏. Proof. unify (rec_prod' g (a,b)) (g a b). Abort.
  End a.
  Section b.
    Context `(B : A → 𝓤).
    Local Definition rec_sig' (C:𝓤) : (Π x, B x → C) → (Σ x, B x) → C := λ g p, g (p.1) (p.2).

    Context (C:𝓤) (g : Π x, B x → C) (a:A) (b:B a).
    Goal 𝟏. Proof. unify (rec_sig' C g (a;b)) (g a b). Abort.
  End b.
End ex_1_2.

(*
Exercise 1.3. Derive the induction principle for products indA×B, using only the projections and
the propositional uniqueness principle uniqA×B. Verify that the definitional equalities are valid.
Generalize uniqA×B
to Σ-types, and do the same for Σ-types. (This requires concepts from Chapter 2.)
*)
Require Import chapter2.
Local Open Scope path_scope.
Section ex_1_3.
  Section a.
    Local Definition ind_prod' `(C:A × B → 𝓤) : (Π a b, C (a, b)) → Π (p : A × B), C p
      := λ g p, (pair_unique p)⁻¹ # g (π₁ p) (π₂ p).

    Context `(C:A × B → 𝓤) (g:Π a b, C (a, b)) (a:A) (b:B).
    Goal 𝟏. Proof. unify (ind_prod' C g (a,b)) (g a b). Abort.
  End a.
  Section b.
    Context `(B:A → 𝓤).
    Local Definition ind_sigma' (C : (Σ a, B a) → 𝓤) : (Π a b, C (a; b)) → Π (x : Σ a, B a), C x
      := λ g x, (sig_unique x)⁻¹ # g (x.1) (x.2).

    Context (C : (Σ a, B a) → 𝓤) (g:Π a b, C (a; b)) (a:A) (b:B a).
    Goal 𝟏. Proof. unify (ind_sigma' C g (a;b)) (g a b). Abort.
  End b.
End ex_1_3.

(*
Exercise 1.4. Assuming as given only the iterator for natural numbers
  iter : ∏ {C:𝓤}, C → (C → C) → ℕ → C
with the defining equations
  iter c0 cs 0 :≡ c0,
  iter c0 cs (succ n) :≡ cs (iter c0 cs n),
derive a function having the type of the recursor recℕ. Show that the defining equations of the
recursor hold propositionally for this function, using the induction principle for ℕ.
*)
Section ex_1_4.
  Local Open Scope nat.
  Local Fixpoint iter {C:𝓤} (c₀:C) (cs:C → C) (n:ℕ) : C :=
    match n with
    | 0 => c₀
    | succ m => cs (iter c₀ cs m)
    end.

  Context {C:𝓤} (c₀:C) (cs:ℕ → C → C).
  Let f (p : ℕ × C) := (succ (π₁ p), cs (π₁ p) (π₂ p)).
  Let g (n:ℕ) : ℕ × C := iter (0, c₀) f n.
  Local Definition rec_nat' (n:ℕ) : C := π₂ (g n).

  Goal rec_nat' 0 = c₀. Proof refl.
  Goal Π n, rec_nat' (succ n) = cs n (rec_nat' n).
  Proof.
    (* Strengthen the inductive hypothesis *)
    refine (λ n, π₂ (pair_eq_equiv _ (succ n, _) _)); unfold rec_nat'; revert n.
    (* Proof by induction *)
    apply ind_nat.
    * (* 0 *) exact refl.
    * (* succ *)
      refine (λ n r, ap f r · pair⁼ (_, _)).
      + exact refl.
      + exact (ap (λ x, cs (succ n) (π₂ x)) r⁻¹).
  Defined.
  Local Close Scope nat.
End ex_1_4.

(*
Exercise 1.5. Show that if we define A + B :≡ ∑(x:2) rec₂(U, A, B, x), then we can give a definition
of indA+B for which the definitional equalities stated in §1.7 hold.
*)
Section ex_1_5.
  Local Open Scope bool_scope.
  Context {A B : 𝓤}.
  Local Definition sum' := Σ (x:𝟐), rec₂ 𝓤 A B x.
  Local Definition inl' (a:A) : sum' := (0; a).
  Local Definition inr' (b:B) : sum' := (1; b).

  Local Definition ind_sum' (C:sum' → 𝓤) : (Π a, C (inl' a)) → (Π b, C (inr' b)) → Π x, C x.
  Proof.
    refine (λ f g, ind_sig _ C _).
    exact (ind₂ (λ x, Π y, C (x; y)) f g).
  Defined.

  Context (C:sum' → 𝓤) (f:Π a, C (inl' a)) (g:Π b, C (inr' b)) (a:A) (b:B).
  Goal 𝟏. Proof.
    unify (ind_sum' C f g (inl' a)) (f a).
    unify (ind_sum' C f g (inr' b)) (g b).
  Abort.
  Local Close Scope bool_scope.
End ex_1_5.

(*
Exercise 1.6. Show that if we define A × B :≡ ∏(x:2) rec₂(U, A, B, x), then we can give a definition
of indA×B for which the definitional equalities stated in §1.5 hold propositionally (i.e. using
equality types). (This requires the function extensionality axiom, which is introduced in §2.9.)
*)
Section ex_1_6.
  Local Open Scope bool_scope.
  Context `{!Funext}.  (* Assume function extensionality axiom. Defined in chapter2.v *)

  Context {A B : 𝓤}.
  Local Definition prod' := Π (x:𝟐), rec₂ 𝓤 A B x.
  Local Definition pair' (a:A) (b:B) : prod' := ind₂ (rec₂ 𝓤 A B) a b.

  Local Definition pair_unique' (x : prod') :  pair' (x 0) (x 1) = x.
  Proof. apply funext. exact (ind₂ (λ b, pair' (x 0) (x 1) b = x b) refl refl). Defined.

  Context (C:prod' → 𝓤) (g:Π a b, C (pair' a b)).
  Local Definition ind_prod'' p : C p := pair_unique' p # g (p 0) (p 1).

  Context (a:A) (b:B).
  Local Definition ind_prod_comp'' : ind_prod'' (pair' a b) = g a b
    := (apd ind_prod'' (pair_unique' (pair' a b))⁻¹)⁻¹ · transport_Vp _ _ _.
  Local Close Scope bool_scope.
End ex_1_6.



(*
Exercise 1.7. Give an alternative derivation of ind'=A [based_path_ind] from ind=A [path_ind]
which avoids the use of universes. (This is easiest using concepts from later chapters.)
*)
Section ex_1_7.
  Local Definition concat' {A:𝓤} {a b c : A} (p : a = b) (q : b = c) : a = c
    := path_ind (λ x y (p:x=y), Π z, y = z → x = z) (λ x z, id) a b p c q.
  Local Definition transport' `(C : A → 𝓤) `(p : x = y :> A) : C x → C y
    := path_ind (λ x y p, C x → C y) (λ x, id) x y p.
  Local Definition concat_1p' `(p : x = y :> A) : concat' 1 p = p
    := path_ind (λ x y p, concat' 1 p = p) (λ x, 1) x y p.
  Local Definition concat_p1_back' `(p : x = y :> A) : p = concat' p 1
    := path_ind (λ x y p, p = concat' p 1) (λ x, 1) x y p.
  Local Definition transport_Id_ax' `(a:A) `(p:x₁ = x₂) (q:a = x₁) : transport' (λ x, a = x) p q = concat' q p
    := path_ind (λ x y r, Π (s:a = x), transport' (λ b, a = b) r s = concat' s r)
                (λ x s, concat_p1_back' s) x₁ x₂ p q.
  Local Definition sig_eq_intro' `{B: A → 𝓤} : Π (x y : sig B),
      (Σ (p:pr₁ x = pr₁ y), transport' B p (pr₂ x) = pr₂ y) → x = y.
  Proof.
    refine (ind_sig B _ (λ a b, _)).    (* intros [a b]. *)
    refine (ind_sig B _ (λ a' b', _)).  (* intros [a' b']. *)
    simpl.
    refine (ind_sig _ _ (λ p q, _)); simpl in q.  (* intros [p q]. *)
    refine (path_ind (λ x x' r, Π (y:B x) (y':B x'), transport' B r y = y' → (x;y) = (x' ; y')) (λ x, _) _ _ p _ _ q).
    clear a b a' b' p q. simpl. unfold id.
    exact (path_ind (λ y y' _, (x; y) = (x; y')) (λ y, 1)).
  Defined.

  Local Definition isContr_based_paths' `(a:A) : Π (p : Σ x, a = x), (a;1) = p.
  Proof.
    refine (ind_sig _ _ (λ x p, _)); simpl in p.
    refine (sig_eq_intro' _ _ _); simpl.
    refine (p; _).
    exact (concat' (transport_Id_ax' _ _ _) (concat_1p' _)).
  Defined.

  Local Definition based_path_ind' `(a:A) (C : Π x, (a = x) → 𝓤) (H:C a 1) x p : C x p
    := transport' (λ r, C r.1 r.2) (isContr_based_paths' a (x; p)) H.
End ex_1_7.



(*
Exercise 1.8. Define multiplication and exponentiation using recN. Verify that (N, +, 0, ×, 1) is
a semiring using only indN. You will probably also need to use symmetry and transitivity of
equality, Lemmas 2.1.1 and 2.1.2.
*)
Section ex_1_8.
  Local Open Scope nat_scope.
  Local Definition exp (a:ℕ) : ℕ → ℕ := rec_nat 1 (λ _ x, a * x).

  Local Ltac nat_induction := match goal with |- Π a, ?f => refine (ind_nat (λ a, f) _ _) end.

  Local Definition plus_assoc : Π x y z, (x + y) + z = x + (y + z).
  Proof. intros x y z. revert x. nat_induction.
  + exact refl.
  + exact (λ x p, ap succ p).
  Defined.
  Local Definition plus_0_r : Π x, x + 0 = x :=
    ind_nat (λ x, x + 0 = x) refl (λ x p, ap succ p).
  Local Definition plus_comm : Π x y, x + y = y + x.
  Proof.
    assert (Π y x, succ x + y = x + succ y) as aux. {
      intros y. nat_induction.
      + exact refl.
      + exact (λ x p, ap succ p).
    }
    intros x y. revert x. nat_induction.
    + exact (plus_0_r y)⁻¹.
    + exact (λ x p, ap succ p · aux _ _).
  Defined.


  Local Definition plus_mult_distr_r : Π x y z, (x + y) × z = x × z + y × z.
  Proof. intros x y z. revert x. nat_induction.
  + exact refl.
  + refine (λ x p, _). simpl.
    exact (ap (add z) p · (plus_assoc _ _ _)⁻¹).
  Defined.

  Local Definition mult_assoc : Π x y z, (x × y) × z = x × (y × z).
  Proof. intros x y z. revert x. nat_induction.
  + exact refl.
  + refine (λ x p, _). simpl.
    exact (plus_mult_distr_r _ _ _ · ap (add _) p).
  Defined.

  Local Definition mult_0_r : Π x, x × 0 = 0 :=
    ind_nat (λ x, x × 0 = 0) refl (λ x p, p).

  Local Definition mult_1_l : Π x, 1 × x = x := plus_0_r.
  Local Definition mult_1_r : Π x, x × 1 = x :=
    ind_nat (λ x, x × 1 = x) refl (λ x p, ap succ p).

  Local Definition plus_mult_distr_l : Π x y z, x × (y + z) = x × y + x × z.
  Proof. intros x y z. revert x. nat_induction.
  + exact refl.
  + refine (λ x p, _). simpl.
    refine (ap (add (y + z)) p · _).
    refine ((plus_assoc _ _ _) · ap (add y) _ · (plus_assoc _ _ _)⁻¹).
    refine ((plus_assoc _ _ _)⁻¹ · ap (λ a, a + x × z) _ · (plus_assoc _ _ _)).
    exact (plus_comm _ _).
  Defined.

  Local Definition mult_comm : Π x y, x × y = y × x.
  Proof.
    intros x y. revert x. nat_induction.
    + exact (mult_0_r y)⁻¹.
    + intros x p. simpl.
      refine (_ · (plus_mult_distr_l _ 1 _)⁻¹).
      exact (ap2 add (mult_1_r y)⁻¹ p).
  Defined.
  Local Close Scope nat_scope.
End ex_1_8.

(*
Exercise 1.9. Define the type family Fin : N → U mentioned at the end of §1.3, and the dependent
function fmax : ∏(n:N) Fin(n + 1) mentioned in §1.4.
*)
Section ex_1_9.
  Fixpoint Fin (n:ℕ) : 𝓤 :=
    match n with
    | 0%nat => 𝟎
    | succ m => 𝟏 + Fin m
    end.

  Fixpoint fmax (n:ℕ) : Fin (1+n) :=
    match n with
    | 0%nat => inl ★
    | succ m => inr (fmax m)
    end.
End ex_1_9.

(*
Exercise 1.10. Show that the Ackermann function ack : N → N → N is definable using only
recN satisfying the following equations:
ack(0, n) ≡ succ(n),
ack(succ(m), 0) ≡ ack(m, 1),
ack(succ(m),succ(n)) ≡ ack(m, ack(succ(m), n)).
*)
Section ex_1_10.
  Local Open Scope nat_scope.
  Fixpoint Ack (a:ℕ) : ℕ → ℕ :=
    match a with
    | 0 => succ
    | succ m => fix F (b:ℕ) :=
      match b with
      | 0 => Ack m 1
      | succ n => Ack m (F n)
      end
    end.

  Definition Ack' : ℕ → ℕ → ℕ :=
    rec_nat
      succ
      (λ m Ack_m, rec_nat
        (Ack_m 1)
        (λ n Ack_Sm_n, Ack_m Ack_Sm_n)
      ).

  Goal 𝟏. unify Ack Ack'. Abort.

  Context (n m : nat).
  Goal Ack 0 n = succ n. Proof refl.
  Goal Ack (succ m) 0 = Ack m (succ 0). Proof refl.
  Goal Ack (succ m) (succ n) = Ack m (Ack (succ m) n). Proof refl.
  Local Close Scope nat_scope.
End ex_1_10.

(*
Exercise 1.11. Show that for any type A, we have ¬¬¬A → ¬A.
*)
Local Definition TNE (A:𝓤) : ¬¬¬A → ¬A := λ f a, f (λ g, g a).

(*
Exercise 1.12. Using the propositions as types interpretation, derive the following tautologies.
(i) If A, then (if B then A).
(ii) If A, then not (not A).
(iii) If (not A or not B), then not (A and B).
*)
Goal Π A B, A → (B → A). Proof λ A B a b, a.
Goal Π A, A → ¬¬A. Proof λ A a f, f a.
Goal Π A B, (¬A + ¬B) → ¬(A × B). Proof λ A B d c, match d with inl f => f (π₁ c) | inr g => g (π₂ c) end.

(*
Exercise 1.13. Using propositions-as-types, derive the double negation of the principle of excluded
middle, i.e. prove not (not (P or not P)).
*)
Goal Π A, ¬¬(A + ¬A). Proof λ A f, let g:¬A := λ a, f (inl a) in f (inr g).

(*
Exercise 1.14. Why do the induction principles for identity types not allow us to construct a
function f : ∏ (x:A) (p:x=x), p = refl_x  with the defining equation
  f(x,reflx) :≡ refl_refl_x ?
*)
Goal Π `(x:A) (p:x=x), p = 1.
Proof. intros A x p. Fail destruct p. Abort.

(*
Exercise 1.15. Show that indiscernability of identicals follows from path induction.
*)
(* This is just transport. See definition in Ex 1.7 above. *)

(*
Exercise 1.16. Show that addition of natural numbers is commutative
*)
(* See Exercise 1.8 above. *)

