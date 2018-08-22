import categories.category
import categories.isomorphism
import categories.tactics
import categories.functor
open categories

universes u v u₀ v₀

namespace categories.isomorphism
definition is_Isomorphism' {D : Type u} [𝒟 : category.{u v} D] {X Y : D} (f : X ⟶ Y) : Prop := nonempty (is_Isomorphism f)
end categories.isomorphism

namespace categories.functor
definition is_Faithful_Functor {D : Type u} [𝒟 : category.{u v} D] 
                        {E : Type u₀} [ℰ : category.{u₀ v₀} E]
                        (F : D ↝ E) := ∀ {A B : D} {f g : A ⟶ B} (p : F &> f = F &> g), f = g
definition is_Full_Functor {D : Type u} [𝒟 : category.{u v} D] 
                        {E : Type u₀} [ℰ : category.{u₀ v₀} E]
                        (F : D ↝ E)  := ∀ {A B : D} h : F +> A ⟶ F +> B, ∃f : A ⟶ B, F &> f = h
end categories.functor

namespace categories.idempotent
definition is_Idempotent {D : Type u} [𝒟 : category.{u v} D] {X : D} (e : X ⟶ X) := e ≫ e = e
definition is_Split_Idempotent {D : Type u} [𝒟 : category.{u v} D] {X : D} (e : X ⟶ X) := ∃(f g : X ⟶ X),(f ≫ g = e)∧(g ≫ f = 𝟙X) 
end categories.idempotent