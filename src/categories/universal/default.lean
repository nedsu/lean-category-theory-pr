-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import .cones

open category_theory
open category_theory.initial
open category_theory.types

namespace category_theory.universal

/-
We give "explicit" definitions of (co)equalizers, and (finite) (co)products. Of course these are special cases of (co)limits,
but they are used so pervasively that they need a convenient interface.

TODO: pullbacks and pushouts should be here too.
-/

universes u v w
variables {C : Type u}
variables [𝒞 : category.{u v} C]
include 𝒞
variables {X Y : C}

structure Equalizer (f g : X ⟶ Y) :=
(equalizer     : C)
(inclusion     : equalizer ⟶ X)
(map           : ∀ {Z : C} (k : Z ⟶ X) (w : k ≫ f = k ≫ g), Z ⟶ equalizer)
(witness       : inclusion ≫ f = inclusion ≫ g . obviously)
(factorisation : ∀ {Z : C} (k : Z ⟶ X) (w : k ≫ f = k ≫ g), (map k w) ≫ inclusion = k . obviously)
(uniqueness    : ∀ {Z : C} (a b : Z ⟶ equalizer) (witness : a ≫ inclusion = b ≫ inclusion), a = b . obviously)

make_lemma Equalizer.witness
make_lemma Equalizer.factorisation
make_lemma Equalizer.uniqueness
attribute [simp,ematch] Equalizer.factorisation_lemma
attribute [applicable] Equalizer.inclusion Equalizer.map
attribute [applicable] Equalizer.uniqueness_lemma

structure BinaryProduct (X Y : C) :=
(product             : C)
(left_projection     : product ⟶ X)
(right_projection    : product ⟶ Y)
(map                 : ∀ {Z : C} (f : Z ⟶ X) (g : Z ⟶ Y), Z ⟶ product)
(left_factorisation  : ∀ {Z : C} (f : Z ⟶ X) (g : Z ⟶ Y), (map f g) ≫ left_projection  = f . obviously) 
(right_factorisation : ∀ {Z : C} (f : Z ⟶ X) (g : Z ⟶ Y), (map f g) ≫ right_projection = g . obviously) 
(uniqueness          : ∀ {Z : C} (f g : Z ⟶ product)
                          (left_witness  : f ≫ left_projection  = g ≫ left_projection )
                          (right_witness : f ≫ right_projection = g ≫ right_projection), f = g . obviously)

make_lemma BinaryProduct.left_factorisation
make_lemma BinaryProduct.right_factorisation
make_lemma BinaryProduct.uniqueness
attribute [simp,ematch] BinaryProduct.left_factorisation_lemma BinaryProduct.right_factorisation_lemma
attribute [applicable] BinaryProduct.left_projection BinaryProduct.right_projection BinaryProduct.map
attribute [applicable] BinaryProduct.uniqueness_lemma

structure Product {I : Type w} (F : I → C) :=
(product       : C)
(projection    : Π i : I, product ⟶ (F i))
(map           : ∀ {Z : C} (f : Π i : I, Z ⟶ (F i)), Z ⟶ product)
(factorisation : ∀ {Z : C} (f : Π i : I, Z ⟶ (F i)) (i : I), (map f) ≫ (projection i) = f i . obviously)
(uniqueness    : ∀ {Z : C} (f g : Z ⟶ product) (witness : ∀ i : I, f ≫ (projection i) = g ≫ (projection i)), f = g . obviously)

make_lemma Product.factorisation
make_lemma Product.uniqueness
attribute [simp,ematch] Product.factorisation_lemma
attribute [applicable] Product.projection Product.map
attribute [applicable] Product.uniqueness_lemma

structure Coequalizer (f g : X ⟶ Y) :=
(coequalizer   : C)
(projection    : Y ⟶ coequalizer)
(map           : ∀ {Z : C} (k : Y ⟶ Z) (w : f ≫ k = g ≫ k), coequalizer ⟶ Z)
(witness       : f ≫ projection = g ≫ projection . obviously)
(factorisation : ∀ {Z : C} (k : Y ⟶ Z) (w : f ≫ k = g ≫ k), projection ≫ (map k w) = k . obviously)
(uniqueness    : ∀ {Z : C} (a b : coequalizer ⟶ Z) (witness : projection ≫ a = projection ≫ b), a = b . obviously)

make_lemma Coequalizer.witness
make_lemma Coequalizer.factorisation
make_lemma Coequalizer.uniqueness
attribute [simp,ematch] Coequalizer.factorisation_lemma
attribute [applicable] Coequalizer.projection Coequalizer.map
attribute [applicable] Coequalizer.uniqueness_lemma

structure BinaryCoproduct (X Y : C) :=
(coproduct           : C)
(left_inclusion      : X ⟶ coproduct)
(right_inclusion     : Y ⟶ coproduct)
(map                 : ∀ {Z : C} (f : X ⟶ Z) (g : Y ⟶ Z), coproduct ⟶ Z)
(left_factorisation  : ∀ {Z : C} (f : X ⟶ Z) (g : Y ⟶ Z), left_inclusion ≫ (map f g)  = f . obviously) 
(right_factorisation : ∀ {Z : C} (f : X ⟶ Z) (g : Y ⟶ Z), right_inclusion ≫ (map f g) = g . obviously) 
(uniqueness          : ∀ {Z : C} (f g : coproduct ⟶ Z)
                          (left_witness  : left_inclusion ≫ f = left_inclusion ≫ g)
                          (right_witness : right_inclusion ≫ f = right_inclusion ≫ g), f = g . obviously)

make_lemma BinaryCoproduct.left_factorisation
make_lemma BinaryCoproduct.right_factorisation
make_lemma BinaryCoproduct.uniqueness
attribute [simp,ematch] BinaryCoproduct.left_factorisation_lemma BinaryCoproduct.right_factorisation_lemma
attribute [applicable] BinaryCoproduct.left_inclusion BinaryCoproduct.right_inclusion BinaryCoproduct.map
attribute [applicable] BinaryCoproduct.uniqueness_lemma

structure Coproduct {I : Type w} (X : I → C) :=
(coproduct     : C)
(inclusion     : Π i : I, (X i) ⟶ coproduct)
(map           : ∀ {Z : C} (f : Π i : I, (X i) ⟶ Z), coproduct ⟶ Z)
(factorisation : ∀ {Z : C} (f : Π i : I, (X i) ⟶ Z) (i : I), (inclusion i) ≫ (map f) = f i . obviously)
(uniqueness    : ∀ {Z : C} (f g : coproduct ⟶ Z) (witness : ∀ i : I, (inclusion i) ≫ f = (inclusion i) ≫ g), f = g . obviously)

-- Coming in later PRs: all these things special cases of (co)limits, and hence are unique up to unique isomorphism.

end category_theory.universal

