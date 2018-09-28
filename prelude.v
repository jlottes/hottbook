(*
  Load with "coqtop -nois", "coqide -nois", etc.
  Preliminaries. Taken mostly from Coq standard library and
  https://github.com/HoTT/book/blob/master/coq_introduction/Reading_HoTT_in_Coq.v
*)

Reserved Notation "x -> y" (at level 99, right associativity, y at level 200).
Reserved Notation "x → y" (at level 99, right associativity, y at level 200).

Reserved Notation "x = y :> T"
(at level 70, y at next level, no associativity).
Reserved Notation "x = y" (at level 70, no associativity).

Reserved Notation "x + y" (at level 50, left associativity).
Reserved Notation "x * y" (at level 40, left associativity).
Reserved Notation "x × y" (at level 40, left associativity).
Reserved Notation "( x , y , .. , z )" (at level 0).

Reserved Notation "p ⁻¹" (at level 1, format "p ⁻¹").
Reserved Notation "p · q" (at level 20).
Reserved Notation "p ∗ q" (at level 20).
Reserved Notation "p ·ₗ q" (at level 20).
Reserved Notation "p ·ᵣ q" (at level 20).
Reserved Notation "p ∘ₗ q" (at level 20).
Reserved Notation "p ∘ᵣ q" (at level 20).

Delimit Scope type_scope with type.
Delimit Scope function_scope with function.
Delimit Scope core_scope with core.

Bind Scope type_scope with Sortclass.
Bind Scope function_scope with Funclass.

Open Scope core_scope.
Open Scope function_scope.
Open Scope type_scope.

Declare ML Module "ltac_plugin".
Global Set Default Proof Mode "Classic".

Global Set Primitive Projections.
Global Set Universe Polymorphism.
Global Generalizable All Variables.
Global Unset Elimination Schemes.

Notation 𝓤₀ := Set.
Notation 𝓤 := Type.

(* Section 1.4: Dependent function types (Π-types) *)
Notation "A -> B" := (forall (_ : A), B) : type_scope.
Notation "A → B" := (A -> B) : type_scope.
Notation "'λ' x .. y , t" := (fun x => .. (fun y => t) ..)
  (at level 200, x binder, y binder, right associativity).
Notation "'Π' x .. y , P" := (forall x, .. (forall y, P) ..)
  (at level 200, x binder, y binder, right associativity) : type_scope.

Definition id {A} (x:A) := x.

Definition compose {A B C} (g:B → C) (f: A → B) (x:A) := g (f x).
Infix "∘" := compose (at level 40, left associativity) : function_scope.

(* Section 1.5: Product types *)
Inductive prod (A B: 𝓤) := pair : A → B → prod A B.
Arguments pair {A} {B} _ _.
Add Printing Let prod.

Notation "A * B" := (prod A B) : type_scope.
Notation "A × B" := (A * B) : type_scope.
Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z) : core_scope.

Definition fst `(p:A × B) := match p with (x, y) => x end.
Definition snd `(p:A × B) := match p with (x, y) => y end.
Notation π₁ := fst.
Notation π₂ := snd.

Definition rec_prod {A B C} (f:A → B → C) x : C
:= match x with (a, b) => f a b end.
Definition ind_prod `(C:A × B → 𝓤) (f:Π a b, C (a, b)) x : C x
:= match x with (a, b) => f a b end.

Definition swap `(p:A × B) := match p with (x, y) => (y, x) end.

Inductive unit : 𝓤₀ := tt : unit.
Notation "𝟏" := unit : type_scope.
Notation "★" := tt : unit_scope.
Bind Scope unit_scope with unit.
Open Scope unit_scope.

Definition rec₁ (C:𝓤) (c:C) x : C := match x with ★ => c end.
Definition ind₁ (C:𝟏 → 𝓤) (c:C ★) x : C x := match x with ★ => c end.

(* Section 1.6: Dependent pair types (Σ-types) *)
Inductive sig `(P:A → 𝓤) : 𝓤 := pairD : Π x, P x → sig P.
Notation "'Σ' x .. y , p" := (sig (λ x, .. (sig (λ y, p)) ..))
  (at level 200, x binder, right associativity)
  : type_scope.

Notation "( x ; y )" := (pairD _ x y) : fibration_scope.
Open Scope fibration_scope.

Definition pr₁ `{P: A → 𝓤} (x:sig P) : A
  := match x with (a; _) => a end.
Notation "x .1" := (pr₁ x) (at level 3, format "x .1") : fibration_scope.

Definition pr₂ `{P: A → 𝓤} (x:sig P) : P (x.1)
  := match x with (_; b) => b end.
Notation "x .2" := (pr₂ x) (at level 3, format "x .2") : fibration_scope.

Definition rec_sig `(B:A → 𝓤) (C:𝓤) (f:Π a (b:B a), C) (x:sig B) : C
:= match x with (a; b) => f a b end.
Definition ind_sig `(B:A → 𝓤) (C:sig B → 𝓤) (f:Π a b, C (a; b)) x : C x
:= match x with (a; b) => f a b end.

(* Section 1.7: Coproduct types *)
Inductive sum (A B:𝓤) : 𝓤 :=
  | inl : A → sum A B
  | inr : B → sum A B.
Arguments inl {A B} _ , [A] B _.
Arguments inr {A B} _ , A [B] _.
Notation "x + y" := (sum x y) : type_scope.

Definition rec_sum {A B C} (g₀:A → C) (g₁:B → C) (x:A + B) : C
:= match x with inl a => g₀ a | inr b => g₁ b end.
Definition ind_sum `(C:A + B → 𝓤) (g₀:Π a, C (inl a)) (g₁:Π b, C (inr b)) x : C x
:= match x with inl a => g₀ a | inr b => g₁ b end.

Inductive Empty_set : 𝓤₀ := .
Notation "𝟎" := Empty_set : type_scope.

Definition rec₀ (C:𝓤) (z:𝟎) : C := match z with end.
Definition ind₀ (C:𝟎 → 𝓤) z : C z := match z with end.

(* Section 1.8: Booleans *)
Inductive bool : 𝓤₀ :=
  | true : bool
  | false : bool.
Add Printing If bool.
Notation "𝟐" := bool : type_scope.

Delimit Scope bool_scope with bool.
Bind Scope bool_scope with bool.
Notation "0" := false : bool_scope.
Notation "1" := true : bool_scope.

Definition rec₂ (C:𝓤) (c₀ c₁:C) (x:𝟐) :=
  match x with 0 => c₀ | 1 => c₁ end%bool.
Definition ind₂ (C:𝟐 → 𝓤) (c₀:C false) (c₁:C true) (x:𝟐) : C x :=
  match x with 0 => c₀ | 1 => c₁ end%bool.

Definition not₂ := (rec₂ _ 1 0)%bool.

(* Section 1.9: Natural numbers *)
Inductive nat : 𝓤₀ :=
  | nat_zero : nat
  | succ : nat → nat.
Delimit Scope nat_scope with nat.
Bind Scope nat_scope with nat.
Arguments succ _%nat.

Notation ℕ := nat.

Notation "0" := nat_zero : nat_scope.
Notation "1" := (succ 0) : nat_scope.
Notation "2" := (succ 1) : nat_scope.
Notation "3" := (succ 2) : nat_scope.
Notation "4" := (succ 3) : nat_scope.

Local Open Scope nat_scope.

Definition rec_nat `(c₀:C) (cs:ℕ → C → C) : ℕ → C :=
  fix F (n:ℕ) := match n with
  | 0 => c₀
  | succ n' => cs n' (F n')
  end.
Definition ind_nat (C:ℕ → 𝓤) (c₀:C 0) (cs:Π n, C n → C (succ n)) : Π n, C n :=
  fix F (n:ℕ) := match n with
  | 0 => c₀
  | succ n' => cs n' (F n')
  end.
Definition nat_rect := ind_nat.

Definition pred n :=
  match n with
    | 0 => n
    | succ u => u
  end.

Fixpoint add n m :=
  match n with
  | 0 => m
  | succ p => succ (p + m)
  end
where "a + b" := (add a b) : nat_scope.

Fixpoint mul n m :=
  match n with
  | 0 => 0
  | succ p => m + (p * m)
  end
where "a * b" := (mul a b) : nat_scope.
Notation "a × b" := (a * b)%nat : nat_scope.

Local Close Scope nat_scope.

(* Section 1.11: Types as Proposistions *)
Definition not A := A → 𝟎.
Notation "¬ x" := (not x) (at level 35, right associativity) : type_scope.

(* Section 1.12: Identity types *)
Inductive Id {A : 𝓤} (a : A) : A → 𝓤 := refl : Id a a.

Notation "x = y :> A" := (@Id A x y) : type_scope.
Notation "x = y" := (x = y :> _) : type_scope.

Arguments refl {A a} , [A] a.

Definition path_ind `(C : Π x y, (x = y :> A) → 𝓤)
  (H : Π x, C x x refl) x y p : C x y p
:= match p with refl => H x end.

Definition based_path_ind `(a:A) (C : Π x, (a = x) → 𝓤)
  (H:C a refl) x p : C x p
:= match p with refl => H end.
