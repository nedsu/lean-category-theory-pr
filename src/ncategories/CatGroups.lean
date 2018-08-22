import categories.category
import categories.isomorphism
import ncategories.ndefs
import algebra.group
open categories
open categories.isomorphism
universes u v

namespace categories.CatGroup

variables (C : Type u)

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

instance group_to_CatGroup (α : Type v) [group α] : CatGroup.{_ v} (fin 1) :=
{ 
    Hom := (λ X Y : fin 1, α),
    identity := (λ X : fin 1, (1 : α)), 
    compose := (λ X Y Z : fin 1, (λ x y : α, (x * y : α))),
    left_identity  := by simp,
    right_identity := by simp,
    associativity  :=   begin
                            intros,
                            rw mul_assoc
                        end,  
    hominverse :=   begin
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
    obj := 0,
    uniqueobj := dec_trivial
}


theorem grp_to_CatGrp_to_grp_id {α : Type v} [group α] : group((CatGroup.obj (fin 1)) ⟶ (CatGroup.obj (fin 1))) := CatGroup.CatGroup_to_group (CatGroup.group_to_CatGroup α)

end categories.CatGroup