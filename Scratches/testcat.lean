import categories.category
import categories.isomorphism
import categories.tactics
open categories
open categories.isomorphism
open tactic

--delaration of universes and variables
universes u₁ v₁


variables p q r s: Prop
lemma t₁ : p → q → p ∧ q := λ hp hq, and.intro hp hq

lemma t₁' : p ∧ q → q ∧ p := λ h,  ⟨ h.right, h.left⟩

lemma t₂ : p ∧ q ↔ q ∧ p := iff.intro
(assume hl: p ∧ q, ⟨hl.right, hl.left⟩)
(assume hr: q ∧ p, ⟨hr.right, hr.left⟩)

lemma t₂'' : (p → q → r) → (p ∧ q → r) := λ h hp,  h hp.elim_left hp.elim_right


lemma t₂' : p → q → r ↔ p ∧ q → r := 
⟨(λ hl hpqr , hl hpqr.left hpqr.right),
(λ hr hp hq, hr ⟨hp, hq⟩)⟩ 

lemma t₃ : p ∧ q → p ∨ q := 
begin
intro h,
exact or.intro_left q h.left,
end

lemma t₄ : p ∨ q → q ∨ p := λ h, h.elim
(λ hp, or.inr hp)
(λ hq, or.inl hq)

lemma t₅' (h : p) : ¬ ¬ p :=
assume hnp : ¬ p,
show false, from hnp h

open classical
lemma t₅'' (h : ¬ ¬ p) : p :=
by_contradiction (λ hnp, absurd hnp h)

lemma t₅ : p ↔ ¬ ¬ p := ⟨t₅' p, t₅'' p⟩ 

lemma t₆ (h : ¬(p ∧ q)) : ¬p ∨ ¬q :=
(em p).elim
    (λ hp, 
        (em q).elim
            (λ hq,
            false.elim (h ⟨hp, hq⟩))
            (λ hnq,
            or.inr hnq))
    (λ hnp,
    or.inl hnp)


example : ¬(p ↔ ¬p) :=
λ h,
    have hnp : ¬p, from 
        (assume hp : p,
        h.elim_left hp hp),
    have hp : p, from h.elim_right hnp,
    hnp hp

example (α : Type) (p: α → Prop) : (∀ x : α, p x) → (∀ y : α, p y) := λ h y, h y

definition trans' : Π{α : Type}, (α → α → Prop) → Prop := λ α r, (∀ {x y z : α}, r x y → r y z → r x z)
definition eqn : ℕ → ℕ → Prop := λ n m, n = m
-- #check trans' eqn

example : trans' eqn :=
begin
unfold trans' eqn,
intros,
apply eq.trans a a_1
end

example (α : Type) (a b c : α) (r : α → α → Prop) (h : trans' r) (hab : r a b) (hbc : r b c) : r a c :=
h hab hbc


#print fin 

section 
variables (ObjC : Type u₁) [C : category.{u₁ v₁} ObjC]






end