Require Import prelude chapter2.

Definition isProp P := Π (x y: P), x = y.
Definition isSet A := Π (x y: A), isProp (x = y).

Existing Class isProp.
Existing Class isSet.

Hint Extern 2 (isProp (_ = _ :> ?A)) => eapply (_ : @isSet A) : typeclass_instances.

Local Open Scope path_scope.

Definition isProp_0 : isProp 𝟎 := λ x, match x with end.

Hint Extern 2 (isProp 𝟎) => eexact isProp_0 : typeclass_instances.
Hint Extern 2 (isProp 𝟏) => eexact @unit_eq_intro : typeclass_instances.

(* Lemma 3.3.3 *)
Definition prop_equiv {P Q} `{isProp P} `{isProp Q} : (P → Q) → (Q → P) → P ≃ Q.
Proof. refine (λ f g, Equiv_from_qinv_alt f g _ _).
+ intros q. apply (_ : isProp Q).
+ intros p. apply (_ : isProp P).
Defined.

(* Lemma 3.3.2 *)
Definition inh_prop_equiv_1 `{!isProp P} (x₀:P) : P ≃ 𝟏
:= prop_equiv (λ _, ★) (λ _, x₀).

(* Lemma 3.3.4 *)
Definition prop_is_set A : isProp A → isSet A.
Proof. intros f x.
  set (g := f x).
  assert (Π y z (p:y = z :> A), p = (g y)⁻¹ · g z) as H.
  + intros y z p. apply (cancelL (g y)).
    refine (_ · (concat_p_Vp _ _)⁻¹).
    refine (_ · apd g p).
    exact (transport_Id_ax _ _ _)⁻¹.
  + intros y p q. exact (H _ _ _ · (H _ _ _)⁻¹).
Defined.
Hint Extern 8 (isSet _) => eapply @prop_is_set : typeclass_instances.

Tactic Notation "funext" simple_intropattern(a) := apply weak_funext; intros a.
Tactic Notation "funext" simple_intropattern(a) simple_intropattern(b) := funext a; funext b.

Definition isProp_isProp `{!Funext} A : isProp (isProp A).
Proof. intros f g. funext x y. apply (_ : isSet A). Defined.
Hint Extern 2 (isProp (isProp _)) => eapply @isProp_isProp : typeclass_instances.

Definition isProp_isSet `{!Funext} A : isProp (isSet A).
Proof. intros f g. funext x y. funext p q. apply (_ : isSet (x = y)). Defined.
Hint Extern 2 (isProp (isSet _)) => eapply @isProp_isSet : typeclass_instances.

Definition isProp_prod A B {HA:isProp A} {HB:isProp B} : isProp (A × B).
Proof. intros x y. apply pair⁼. split; apply (_ : isProp _). Defined.
Hint Extern 2 (isProp (_ × _)) => eapply @isProp_prod : typeclass_instances.

Definition isProp_Pi {WF:Funext} `(B:A → 𝓤) {H:Π x, isProp (B x)} : isProp (Π x, B x).
Proof. intros f g. funext x. apply H. Defined.
Hint Extern 2 (isProp (Π x, _)) => eapply @isProp_Pi : typeclass_instances.
Hint Extern 2 (isProp (¬ _)) => eapply @isProp_Pi : typeclass_instances.

Module Export PropTrunc.
  Private Inductive merely (A:𝓤) : 𝓤 := hexists : A → merely A.
  Arguments hexists {A} _.
  Axiom merely_isprop : Π A, isProp (merely A).

  Definition rec_merely {A} `{H:isProp B} (f:A → B) : merely A → B
  := λ x, match x with hexists a => λ _, f a end H.
End PropTrunc.

Existing Class merely.

Hint Extern 2 (isProp (merely _)) => eapply @merely_isprop : typeclass_instances.

Delimit Scope merely_scope with merely.
Bind Scope merely_scope with merely.
Notation "| x |" := (hexists x) (at level 10, format "| x |") : merely_scope.
Notation "‖ x ‖" := (merely x) (at level 10, format "‖ x ‖") : type_scope.

(* Lemma 3.9.1 *)
Definition prop_equiv_merely P `{!isProp P} : P ≃ ‖P‖
:= prop_equiv hexists (rec_merely id).

Definition unique_choice `(P:A → 𝓤) {H1:Π x, isProp (P x)} {H2:Π x, ‖P x‖}
  : Π x, P x
:= λ x, rec_merely id (H2 x).


(* Section 3.11: Contractibility *)
Definition isContr A := Σ (a:A), Π x, a = x.
Existing Class isContr.

(* Lemma 3.11.3 (i) ⇒ (ii) *)
Definition contr_is_prop A : isContr A → isProp A.
Proof. intros [a contr] x y. exact ((contr x)⁻¹ · (contr y)). Defined.
Hint Extern 8 (isProp _) => eapply @contr_is_prop : typeclass_instances.

(* Lemma 3.11.3 (ii) ⇒ (i) *)
Definition contr_prop `{H:isProp A} (a:A) : isContr A := (a; H a).

(* Lemma 3.11.3 (i) ⇒ (iii) *)
Definition contr_equiv_1 A {H:isContr A} : A ≃ 𝟏
:= inh_prop_equiv_1 H.1 .

(* Lemma 3.11.3 (iii) ⇒ (i) *)
Definition equiv_1_contr A : A ≃ 𝟏 → isContr A.
Proof. intros f. exists (inv_fun f ★). intros x.
  exact (ap (inv_fun f) unit⁼ · equiv_linv_hom f x).
Defined.

(* Lemma 3.11.4 *)
Definition isProp_isContr `{!Funext} A : isProp (isContr A).
Proof. intros c c'. pose proof (_:isContr A).
  apply sig_eq_intro. destruct c as [a p], c' as [a' p']. simpl.
  exists (p a'). apply (_ : isProp (Π x, a' = x) ).
Defined.
Hint Extern 2 (isProp (isContr _)) => eapply @isProp_isContr : typeclass_instances.

(* Corollary 3.11.5 *)
Definition isContr_isContr `{!Funext} A : isContr A → isContr (isContr A)
:= λ x, contr_prop x.
Hint Extern 2 (isContr (isContr _)) => eapply @isContr_isContr : typeclass_instances.

Definition isContr_unit : isContr 𝟏 := (★; λ x, unit⁼).
Hint Extern 2 (isContr 𝟏) => eapply isContr_unit : typeclass_instances.

Definition isContr_prod A B : isContr A → isContr B → isContr (A × B).
Proof. intros x y. exists (x.1, y.1). intro p. apply pair⁼; simpl. exact (x.2 _, y.2 _). Defined.
Hint Extern 2 (isContr (_ × _)) => eapply isContr_prod : typeclass_instances.

(* Lemma 3.11.6 *)
Definition isContr_Pi `{!Funext} `(P:A → 𝓤) : (Π a, isContr (P a)) → isContr (Π a, P a)
:= λ f, contr_prop (λ a, (f a).1).
Hint Extern 2 (isContr (Π x, _)) => eapply @isContr_Pi : typeclass_instances.

(* Lemma 3.11.7 *)
Definition isContr_retract `(r:A → B) (s:B → A) (ε: r ∘ s ~ id) : isContr A → isContr B.
Proof. intro H. exists (r (H.1)). intro b. exact (ap r (H.2 _) · ε b). Defined.

(* Lemma 3.11.8 *)
Definition isContr_based_paths `(a:A) : isContr (Σ x, a = x).
Proof. exists (a; refl). intros [x p].
  apply sig_eq_intro. exists p. simpl.
  exact (transport_Id_ax a p 1 · concat_1p _).
Defined.

(* Lemma 3.11.9 (i) *)
Definition sig_contr_pr1_isequiv `(P:A → 𝓤) : (Π x, isContr (P x)) → isequiv (pr₁ (P:=P)).
Proof. intros f. apply qinv_to_isequiv. exists (λ a, (a; (f a).1)). split.
+ intros a. exact refl.
+ intros x. unfold compose, id. apply sig_eq_intro. exists refl. exact ((f x.1).2 _).
Defined.
Hint Extern 2 (isequiv pr₁) => eapply @sig_contr_pr1_isequiv : typeclass_instances.

Definition transport_contr_loop `(P:A → 𝓤) {H:isSet A} `(p:a = a) (y:P a) : p # y = y
:= ap (λ q, q # y) (H a a p 1).

(* Lemma 3.11.9 (ii) *)
Definition sig_contr_index `(P:A → 𝓤) {H:isProp A} a : sig P ≃ P a.
Proof.
  set (f := λ (p: sig P), H p.1 a # p.2).
  set (g := λ (y: P a), (a; y)).
  apply (Equiv_from_qinv_alt f g).
+ intro y. exact (transport_contr_loop P _ _).
+ intros [a' y]. apply sig_eq_intro. unfold f; simpl.
  exists (H a a'). exact ((transport_pp P _ _ _)⁻¹ · transport_contr_loop P _ _).
Defined.

(* Lemma 3.11.10 *)
Definition isProp_alt A : (Π x y, isContr (x = y :> A)) → isProp A
:= λ f x y, (f x y).1 .

Definition isProp_isContr_eq A : isProp A → Π x y, isContr (x = y :> A).
Proof. intros f x y. exists (f x y). apply (_ : isSet A). Defined.
Hint Extern 2 (isContr (_ = _)) => eapply @isProp_isContr_eq : typeclass_instances.
