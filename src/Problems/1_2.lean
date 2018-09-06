import ncategory_theory.CatGroups
import category_theory.natural_transformation
import data.equiv.basic
open category_theory
open category_theory.isomorphism
open category_theory.functor
open category_theory.CatGroup
open category_theory.nat_trans

--delaration of universes and variables
universes u v u₀ v₀ u₁ v₁ u₂ v₂ 


lemma t {C : Type u} [𝒞 : CatGroup C] : ∀ X Y : C,((𝒞.obj ⟶ 𝒞.obj) = ((functor.id C) X ⟶ (functor.id C) Y)) :=
begin
intros,
exact calc
    (𝒞.obj ⟶ 𝒞.obj) = (((functor.id C) (𝒞.obj)) ⟶ 𝒞.obj) : by simp
    ... = ((functor.id C) 𝒞.obj ⟶ (functor.id C) 𝒞.obj) : by simp
    ... = ((functor.id C) X ⟶ (functor.id C) 𝒞.obj) : by rw CatGroup.uniqueobj X
    ... = ((functor.id C) X ⟶ (functor.id C) Y) : by rw CatGroup.uniqueobj Y
end


section
--#print eq.rec
variables (C : Type u) [𝒞 : CatGroup C] (a : 𝒞.obj ⟶ 𝒞.obj) (X : C)
--#check (eq.rec a (eq.symm(CatGroup.uniqueobj X)) : 𝒞.obj ⟶ X)
--#check @congr_arg
--#print eq.rec.congr_arg
--#print prefix eq.rec
end

--2 Let G be a group viewed as a one-object category. 
--Show that the natural transformations α : functor.id G ⟹ Identity Functor G
-- correspond to elements in the centre of the group.
definition Grp_id_nat_trans_center (C : Type u) [𝒞 : CatGroup C] :
{ a : 𝒞.obj ⟶ 𝒞.obj // ∀ x : 𝒞.obj ⟶ 𝒞.obj, a ≫ x = x ≫ a} ≃ (functor.id C ⟹ functor.id C) :=
{ to_fun := sorry,
  inv_fun := λ α, 
    ⟨(𝟙 𝒞.obj : 𝒞.obj ⟶ ((functor.id C) 𝒞.obj)) ≫ 
      ((α 𝒞.obj) : ((functor.id C) 𝒞.obj) ⟶ ((functor.id C) 𝒞.obj)) ≫
      (𝟙 (𝒞.obj) : ((functor.id C) 𝒞.obj) ⟶ 𝒞.obj),λ x,begin 
        rw [category.id_comp,←category.assoc],
        rw @category.comp_id _ _ _ (CatGroup.obj C) _,
        -- it's such a struggle to rewrite!
        rw @category.comp_id _ _ _ (CatGroup.obj C) _,
        -- goal now ⊢ α (CatGroup.obj C) ≫ x = x ≫ α (CatGroup.obj C)
        sorry 
        end⟩,
  left_inv := sorry,
  right_inv := sorry
}

theorem Grp_id_nat_trans_center' (C : Type u) [𝒞 : CatGroup C] (a : 𝒞.obj ⟶ 𝒞.obj) : 
(∀ x : 𝒞.obj ⟶ 𝒞.obj, a ≫ x = x ≫ a) ↔ (∃ α : functor.id C ⟹ functor.id C, α 𝒞.obj = a)  :=
begin
    apply iff.intro,
        intro hc,
        exact exists.intro 
                (
                    ⟨
                        (λ X , cast (t X X) a), 
                        begin
                            apply_auto_param,
                            have Hy : Y = 𝒞.obj, from CatGroup.uniqueobj Y,
                            have Hx : X = 𝒞.obj, from CatGroup.uniqueobj X,
                            rw Hx at f,
                            rw Hy at f,
                            convert (hc f).symm,
                            repeat {sorry},
                        end
                    ⟩   : functor.id C ⟹ functor.id C)
                (
                    begin
                        simp,
                        exact cast_eq _ a
                    end
                ),
        intro hn,
        cases (classical.indefinite_description _ hn) with α ha,
        intro,
        exact calc
            a ≫ x = (α 𝒞.obj) ≫ x : by rw ha
            ... = (α 𝒞.obj) ≫ ((functor.id C).map x) : by simp
            ... = ((functor.id C).map x) ≫ (α 𝒞.obj) : by rw nat_trans.naturality
            ... = x ≫ (α 𝒞.obj) : by simp
            ... = x ≫ a : by rw ha
end