import category_theory.isomorphism
import ncategory_theory.Ndefs
import algebra.group
open category_theory
open category_theory.isomorphism
universes u v

namespace category_theory.CatGroup

variables (C : Type u)
definition D := unit

class CatGroupoid (C : Type u) extends category.{v} C :=
    (hominverse : Π {X Y : C} (f : X ⟶ Y), is_iso f)

class CatGroup (C : Type u) extends CatGroupoid C :=
    (obj : C)
    (uniqueobj' : ∀ X : C, X = obj)

restate_axiom CatGroup.uniqueobj'

instance [𝒞 : CatGroup C] : has_one (𝒞.obj ⟶ 𝒞.obj) :=
{ one := 𝟙 𝒞.obj}

instance CatGroupoid.homgroup [𝒞 : CatGroupoid C] (X : C) : group (X ⟶ X) :=
{ 
    mul             := category.comp,
    mul_assoc       := by simp,
    one             := 𝟙X,
    one_mul         := by simp,
    mul_one         := by simp,
    inv             := (λ g, (CatGroupoid.hominverse g).1),
    mul_left_inv    := begin intro, unfold, apply is_iso.inv_hom_id' end
}

instance CatGroup_to_group {C : Type u} (𝒞 : CatGroup C) : group (𝒞.obj ⟶ 𝒞.obj) :=
CatGroupoid.homgroup C 𝒞.obj

instance group_to_CatGroup (α : Type v) [group α] : CatGroup.{_ v} D :=
{ 
    hom         :=  (λ X Y : D, α),
    id          :=  (λ X : D, (1 : α)), 
    comp        :=  (λ X Y Z : D, (λ x y : α, (x * y : α))),
    id_comp'    :=  by simp,
    comp_id'    :=  by simp,
    assoc'      :=  λ _ _ _ _ _ _ _, by rw mul_assoc,  
    hominverse  :=  begin
                        intros _ _ x,
                        exact   {
                                    inv := x⁻¹, 
                                    hom_inv_id' :=  by simp,
                                    inv_hom_id' :=  by simp
                                }
                    end,
    obj         :=  unit.star,
    uniqueobj'  :=  begin
                        intro,
                        apply punit.cases_on X,
                        refl
                    end 
}


instance grp_to_CatGrp_to_grp (α : Type v) [group α] : group((CatGroup.obj D) ⟶ (CatGroup.obj D)) := CatGroup.CatGroup_to_group (CatGroup.group_to_CatGroup α)


example (α : Type v) [a :group α] : ∃ (f : α → ((CatGroup.obj D) ⟶ (CatGroup.obj D))), is_group_hom f := sorry
/- the aim here is to show that these two groups are isomorphic, 
but something in the construction here is not working. Lots of errors.
Think that we are somehow refering not to the elements of the group itself
but the group structure. Unsure how to refer directly to the elements-/

section
variables (α : Type v) [group α]
--#check CatGroup.group_to_CatGroup α
end



--example {α : Type v} [a :group α] : is_group_hom  :=

end category_theory.CatGroup