-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import category_theory.functor
import .limits
import .colimits

open category_theory
open category_theory.universal

namespace category_theory.universal

universes u v
variables {J : Type v} [small_category J]
variables {C : Type u} [𝒞 : category.{u v} C]
include 𝒞 

variable {F : J ↝ C}

structure cone_morphism (A B : cone F) : Type v :=
(hom : A.X ⟶ B.X)
(w : Π j : J, hom ≫ (B.π j) = (A.π j) . obviously)

restate_axiom cone_morphism.w
attribute [simp,ematch] cone_morphism.w_lemma

namespace cone_morphism

@[simp,ematch] def commutativity_lemma_assoc {A B : cone F} (c : cone_morphism A B) (j : J) {Z : C} (z : (F j) ⟶ Z): c.hom ≫ B.π j ≫ z = A.π j ≫ z :=
begin
  /- obviously' say: -/
  rw ← category.assoc,
  simp,
end

@[extensionality] lemma ext {A B : cone F} {f g : cone_morphism A B} (w : f.hom = g.hom) : f = g :=
begin
  /- obviously' say: -/
  induction f,
  induction g,
  dsimp at w,
  induction w,
  refl,
end

end cone_morphism

instance Cones (F : J ↝ C) : category.{(max u v) v} (cone F) :=
{ hom      := λ A B, cone_morphism A B,
  comp    := λ _ _ _ f g, { hom := f.hom ≫ g.hom,
                            w := begin /- `obviously'` says: -/ intros, simp end },
  id      := λ B, { hom := 𝟙 B.X, 
                    w := begin /- `obviously'` says: -/ intros, simp end },
  id_comp := begin /- `obviously'` says: -/ intros, ext, dsimp, simp end,
  comp_id := begin /- `obviously'` says: -/ intros, ext, dsimp, simp end,
  assoc   := begin /- `obviously'` says: -/ intros, ext, dsimp, simp end }

-- TODO rename or namespace?
@[simp] lemma Cones.identity.cone_morphism {F : J ↝ C} (c : cone F) : (𝟙 c : cone_morphism c c).hom = 𝟙 (c.X) := rfl
@[simp] lemma Cones.compose.cone_morphism {F : J ↝ C} {c d e : cone F} (f : c ⟶ d) (g : d ⟶ e) : ((f ≫ g) : cone_morphism c e).hom = (f : cone_morphism c d).hom ≫ (g : cone_morphism d e).hom := rfl

section
variables {D : Type u} [𝒟 : category.{u v} D]
include 𝒟

def Cones_functoriality (F : J ↝ C) (G : C ↝ D) : (cone F) ↝ (cone (F ⋙ G)) := 
{ obj      := λ A, { X := G A.X,
                     π := λ j, G.map (A.π j), 
                     w := begin /- `obviously'` says: -/ intros, simp, erw [←functor.map_comp_lemma, cone.w_lemma] end },
  map'     := λ X Y f, { hom := G.map f.hom,
                         w := begin /- `obviously'` says: -/ intros, dsimp, erw [←functor.map_comp_lemma, cone_morphism.w_lemma] end },
  map_id   := begin /- `obviously'` says: -/ intros, ext, dsimp, simp end,
  map_comp := begin /- `obviously'` says: -/ intros, ext, dsimp, simp end }
end

structure cocone_morphism (A B : cocone F) :=
(hom : A.X ⟶ B.X)
(w   : Π j : J, (A.ι j) ≫ hom = (B.ι j) . obviously)

restate_axiom cocone_morphism.w
attribute [simp,ematch] cocone_morphism.w_lemma

namespace CoconeMorphism
@[simp,ematch] def commutativity_lemma_assoc {A B : cocone F} (c : cocone_morphism A B) (j : J) {Z : C} (z : B.X ⟶ Z): (A.ι j) ≫ c.hom ≫ z = (B.ι j) ≫ z :=
begin
  -- `obviously'` says:
  erw [←category.assoc_lemma, cocone_morphism.w_lemma]
end

@[extensionality] lemma ext {A B : cocone F} {f g : cocone_morphism A B} (w : f.hom = g.hom) : f = g :=
begin 
  induction f,
  induction g,
  -- `obviously'` says:
  dsimp at *,
  induction w,
  refl,
end
end CoconeMorphism

instance Cocones (F : J ↝ C) : category.{(max u v) v} (cocone F) := 
{ hom     := λ A B, cocone_morphism A B,
  comp    := λ _ _ _ f g, { hom := f.hom ≫ g.hom,
                            w   := begin /- `obviously'` says: -/ intros, simp end },
  id      := λ B,         { hom := 𝟙 B.X,
                            w   := begin /- `obviously'` says: -/ intros, simp end },
  id_comp := begin /- `obviously'` says: -/ intros, ext, dsimp, simp end,
  comp_id := begin /- `obviously'` says: -/ intros, ext, dsimp, simp end,
  assoc   := begin /- `obviously'` says: -/ intros, ext, dsimp, simp end }

-- TODO rename or namespace?
@[simp] lemma Cocones.identity.cone_morphism {F : J ↝ C} (c : cocone F) : (𝟙 c : cocone_morphism c c).hom = 𝟙 (c.X) := rfl
@[simp] lemma Cocones.compose.cone_morphism {F : J ↝ C} {c d e : cocone F} (f : c ⟶ d) (g : d ⟶ e) : ((f ≫ g) : cocone_morphism c e).hom = (f : cocone_morphism c d).hom ≫ (g : cocone_morphism d e).hom := rfl

section
variables {D : Type u} [𝒟 : category.{u v} D]
include 𝒟

def Cocones_functoriality (F : J ↝ C) (G : C ↝ D) : (cocone F) ↝ (cocone (F ⋙ G)) := 
{ obj      := λ A,     { X    := G A.X,
                         ι     := λ j, G.map (A.ι j),
                         w   := begin /- `obviously'` says: -/ intros, simp, erw [←functor.map_comp_lemma, cocone.w_lemma] end },
  map'     := λ _ _ f, { hom := G.map f.hom,
                         w   := begin /- `obviously'` says: -/ intros, dsimp, erw [←functor.map_comp_lemma, cocone_morphism.w_lemma] end },
  map_id   := begin /- `obviously'` says -/ intros, ext, dsimp, simp end,
  map_comp := begin /- `obviously'` says -/ intros, ext, dsimp, simp end }
end

def LimitCone     (F : J ↝ C) := terminal_object.{(max u v) v} (cone F)
def ColimitCocone (F : J ↝ C) := initial_object.{(max u v) v} (cocone F)

end category_theory.universal

namespace category_theory.functor

universes u v
variables {J : Type v} [small_category J]
variables {C : Type u} [category.{u v} C] {D : Type u} [category.{u v} D]
variable {F : J ↝ C}

open category_theory.universal

def on_cone   (G : C ↝ D) (c : cone F)   : cone (F ⋙ G)   := (Cones_functoriality F G) c
def on_cocone (G : C ↝ D) (c : cocone F) : cocone (F ⋙ G) := (Cocones_functoriality F G) c

end category_theory.functor