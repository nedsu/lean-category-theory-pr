import categories.category
import categories.isomorphism
import ncategories.ndefs
import algebra.group
open categories
open categories.isomorphism
universes u v

namespace categories.CatGroup

variables (C : Type u)
definition D := unit

class CatGroupoid (C : Type u) extends category.{u v} C :=
    (hominverse : Π {X Y : C} (f : X ⟶ Y), is_Isomorphism f)

class CatGroup (C : Type u) extends CatGroupoid C :=
    (obj : C)
    (uniqueobj : ∀ X : C, X = obj)

make_lemma CatGroup.uniqueobj

instance [𝒞 : CatGroup C] : has_one (𝒞.obj ⟶ 𝒞.obj) :=
{ one := 𝟙 𝒞.obj}

instance CatGroupoid.homgroup [𝒞 : CatGroupoid C] (X : C) : group (X ⟶ X) :=
{ 
    mul := category.compose,
    mul_assoc :=begin
                    simp
                end,
    one := 𝟙X,
    one_mul :=  begin
                    simp
                end,
    mul_one :=  begin
                    simp
                end,
    inv :=      (λ g, (CatGroupoid.hominverse g).1),
    mul_left_inv := begin
                        simp 
                    end
}

instance CatGroup_to_group {C : Type u} (𝒞 : CatGroup C) : group (𝒞.obj ⟶ 𝒞.obj) :=
CatGroupoid.homgroup C 𝒞.obj

instance group_to_CatGroup (α : Type v) [group α] : CatGroup.{_ v} D :=
{ 
    Hom             :=  (λ X Y : D, α),
    identity        :=  (λ X : D, (1 : α)), 
    compose         :=  (λ X Y Z : D, (λ x y : α, (x * y : α))),
    left_identity   :=  by simp,
    right_identity  :=  by simp,
    associativity   :=  begin
                            intros,
                            rw mul_assoc
                        end,  
    hominverse      :=  begin
                            intros _ _ x,
                            exact   {
                                        inverse := has_inv.inv x, 
                                        witness_1 :=begin
                                                        simp
                                                    end,
                                        witness_2 :=begin
                                                        simp
                                                    end
                                    }
                        end,
    obj             :=  unit.star,
    uniqueobj       :=  begin
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

end categories.CatGroup