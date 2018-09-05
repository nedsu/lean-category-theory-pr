import categories.category
import categories.isomorphism
import categories.tactics
import categories.functor
import ncategories.Ndefs
open categories categories.isomorphism categories.functor categories.Idempotent tactic

--delaration of universes and variables
universes u v u₁ v₁
variables (C : Type u) [𝒞 : category.{u v} C] 
include 𝒞

namespace Idempotent

--3a Let E be a class of idempotents in a category 𝒞. Show that there is a category 𝒞[Ě] whose objects are the members of E, whose morphisms e ⟶ d are those morphisms f : dom e ⟶ dom d in 𝒞 for which dfe = f, and whose composition coincides with composition in 𝒞
structure class_of_Idempotents (E : Type v) : Type(max u v) :=
    (mor : E → Σ (X : C), X ⟶ X)
    (idem : ∀ (e : E), is_Idempotent (mor e).2)

instance Idempotents_category (E : Type v) [ℰ : class_of_Idempotents.{_ v} C E] : category.{v _} E :=
    {
        Hom := λ e d : E, {f : (ℰ.mor e).1 ⟶ (ℰ.mor d).1 // (ℰ.mor e).2 ≫ f ≫ (ℰ.mor d).2 = f},
        compose := (λ _ _ _ f g, (↑f ≫ ↑g)),
        identity := sorry,
        left_identity := sorry,
        right_identity := sorry,
        associativity := sorry
    }

end Idempotent