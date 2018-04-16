-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Tim Baumann, Stephen Morgan, Scott Morrison

import .category
import .functor
open categories
open categories.functor

namespace categories.isomorphism
universes u

variable {C : Type (u+1)}
variable [category C]
variables {X Y Z : C}

structure Isomorphism (X Y : C) :=
  (morphism : X ⟶ Y)
  (inverse : Y ⟶ X)
  (witness_1 : morphism ≫ inverse = 𝟙 X . obviously_stub)
  (witness_2 : inverse ≫ morphism = 𝟙 Y . obviously_stub)

make_lemma Isomorphism.witness_1
make_lemma Isomorphism.witness_2
attribute [simp,ematch] Isomorphism.witness_1_lemma Isomorphism.witness_2_lemma

infixr ` ≅ `:10  := Isomorphism             -- type as \cong

-- These lemmas are quite common, to help us avoid having to muck around with associativity.
-- If anyone has a suggestion for automating them away, I would be very appreciative.
@[simp,ematch] lemma Isomorphism.witness_1_assoc_lemma (I : X ≅ Y) (f : X ⟶ Z) : I.morphism ≫ I.inverse ≫ f = f := 
begin
  -- `obviously'` says:
  rw[←category.associativity_lemma, Isomorphism.witness_1_lemma, category.left_identity_lemma]
end

@[simp,ematch] lemma Isomorphism.witness_2_assoc_lemma (I : X ≅ Y) (f : Y ⟶ Z) : I.inverse ≫ I.morphism ≫ f = f := 
begin
  -- `obviously'` says:
  rw[←category.associativity_lemma, Isomorphism.witness_2_lemma, category.left_identity_lemma]
end

instance Isomorphism_coercion_to_morphism : has_coe (X ≅ Y) (X ⟶ Y) :=
{ coe := Isomorphism.morphism }

definition Isomorphism.id (X : C) : X ≅ X := 
{ morphism  := 1,
  inverse   := 1, 
  witness_1 := begin
                 -- `obviously'` says:
                 simp!,
                 refl
               end,
  witness_2 := begin
                 -- `obviously'` says:
                 simp!,
                 refl
               end }

definition Isomorphism.comp (α : X ≅ Y) (β : Y ≅ Z) : X ≅ Z := 
{ morphism  := α.morphism ≫ β.morphism,
  inverse   := β.inverse ≫ α.inverse,
  witness_1 := begin
                 -- `obviously'` says:
                 simp!
               end,
  witness_2 := begin
                 -- `obviously'` says:
                 simp!
               end }

infixr ` ≫ `:80 := Isomorphism.comp -- type as \gg

@[applicable] lemma Isomorphism_pointwise_equal
  (α β : X ≅ Y)
  (w : α.morphism = β.morphism) : α = β :=
  begin
    induction α with f g wα1 wα2,
    induction β with h k wβ1 wβ2,
    simp at w,    
    have p : g = k,
      begin
        tidy,
        -- PROJECT rewrite_search can't do this rewrite!
        rewrite ← category.left_identity_lemma C k,
        rewrite_search_using `ematch,
      end,
    -- `obviously'` says:
    automatic_induction,
    refl
  end

definition Isomorphism.reverse (I : X ≅ Y) : Y ≅ X := 
{ morphism  := I.inverse,
  inverse   := I.morphism,
  witness_1 := begin
                 -- `obviously'` says:
                 simp!
               end,
  witness_2 := begin
                 -- `obviously'` says:
                 simp!
               end }

@[simp] lemma Isomorphism.cancel_morphism_left (I : X ≅ Y) (f g : Y ⟶ Z) : I.morphism ≫ f = I.morphism ≫ g ↔ f = g :=
begin
  tidy,
  have h := congr_arg (λ h, I.inverse ≫ h) a,
  tidy,
end
@[simp] lemma Isomorphism.cancel_morphism_right (I : X ≅ Y) (f g : Z ⟶ X) : f ≫ I.morphism = g ≫ I.morphism ↔ f = g :=
begin
  tidy,
  have h := congr_arg (λ h, h ≫ I.inverse) a,
  tidy,
end
@[simp] lemma Isomorphism.cancel_inverse_left (I : X ≅ Y) (f g : X ⟶ Z) : I.inverse ≫ f = I.inverse ≫ g ↔ f = g :=
begin
  tidy,
  have h := congr_arg (λ h, I.morphism ≫ h) a,
  tidy,
end
@[simp] lemma Isomorphism.cancel_inverse_right (I : X ≅ Y) (f g : Z ⟶ Y) : f ≫ I.inverse = g ≫ I.inverse ↔ f = g :=
begin
  tidy,
  have h := congr_arg (λ h, h ≫ I.morphism) a,
  tidy,
end

structure is_Isomorphism (morphism : X ⟶ Y) :=
  (inverse : Y ⟶ X)
  (witness_1 : morphism ≫ inverse = 𝟙 X . obviously_stub)
  (witness_2 : inverse ≫ morphism = 𝟙 Y . obviously_stub)

make_lemma is_Isomorphism.witness_1
make_lemma is_Isomorphism.witness_2
attribute [simp,ematch] is_Isomorphism.witness_1_lemma is_Isomorphism.witness_2_lemma

instance is_Isomorphism_coercion_to_morphism (f : X ⟶ Y): has_coe (is_Isomorphism f) (X ⟶ Y) :=
{ coe := λ _, f }

definition Epimorphism (f : X ⟶ Y) := Π (g h : Y ⟶ Z) (w : f ≫ g = f ≫ h), g = h
definition Monomorphism (f : X ⟶ Y) := Π (g h : Z ⟶ X) (w : g ≫ f = h ≫ f), g = h

end categories.isomorphism
