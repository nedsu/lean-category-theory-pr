import category_theory.isomorphism
open category_theory
open category_theory.is_iso

universes v₁ v₂ v₃ u₁ u₂ u₃

theorem twooutofthree {C : Type u₁} [category.{v₁} C] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [is_iso f] [is_iso g] : is_iso (f ≫ g) :=
    {
        inv := is_iso.inv g ≫ is_iso.inv f,
        hom_inv_id' := begin rw [category.assoc], rw [hom_inv_id' g] end,
        inv_hom_id' := sorry
    }