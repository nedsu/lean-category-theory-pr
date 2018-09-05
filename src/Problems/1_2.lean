import ncategories.CatGroups
import categories.tactics
import categories.functor
import categories.natural_transformation
open categories
open categories.isomorphism
open categories.functor
open categories.CatGroup
open categories.natural_transformation

--delaration of universes and variables
universes u v u₀ v₀ u₁ v₁ u₂ v₂ 


lemma t {C : Type u} [𝒞 : CatGroup C] : ∀ X Y : C,((𝒞.obj ⟶ 𝒞.obj) = ((IdentityFunctor C) +> X ⟶ (IdentityFunctor C) +> Y)) :=
begin
intros,
exact calc
    (𝒞.obj ⟶ 𝒞.obj) = (((IdentityFunctor C) +> (𝒞.obj)) ⟶ 𝒞.obj) : by simp
    ... = ((IdentityFunctor C) +> 𝒞.obj ⟶ (IdentityFunctor C) +> 𝒞.obj) : by simp
    ... = ((IdentityFunctor C) +> X ⟶ (IdentityFunctor C) +> 𝒞.obj) : by rw CatGroup.uniqueobj_lemma X
    ... = ((IdentityFunctor C) +> X ⟶ (IdentityFunctor C) +> Y) : by rw CatGroup.uniqueobj_lemma Y
end


section
#print eq.rec
variables (C : Type u) [𝒞 : CatGroup C] (a : 𝒞.obj ⟶ 𝒞.obj) (X : C)
#check (eq.rec a (eq.symm(CatGroup.uniqueobj_lemma X)) : 𝒞.obj ⟶ X)
--#check @congr_arg
--#print eq.rec.congr_arg
#print prefix eq.rec
end

--2 Let G be a group viewed as a one-object category. Show that the natural transformations α : IdentityFunctor G ⟹ Identity Functor G correspond to elements in the centre of the group.
theorem Grp_id_nat_trans_center (C : Type u) [𝒞 : CatGroup C] (a : 𝒞.obj ⟶ 𝒞.obj) : 
(∀ x : 𝒞.obj ⟶ 𝒞.obj, a ≫ x = x ≫ a) ↔ (∃ α : IdentityFunctor C ⟹ IdentityFunctor C, α.components 𝒞.obj = a)  :=
begin
    apply iff.intro,
        intro hc,
        exact exists.intro 
                (
                    ⟨
                        (λ X , cast (t X X) a), 
                        begin
                            apply_auto_param,
                            have Hy : Y = 𝒞.obj, from CatGroup.uniqueobj_lemma Y,
                            have Hx : X = 𝒞.obj, from CatGroup.uniqueobj_lemma X,
                            tidy
                        end
                    ⟩   : IdentityFunctor C ⟹ IdentityFunctor C)
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
            a ≫ x = (α.components 𝒞.obj) ≫ x : by rw ha
            ... = (α.components 𝒞.obj) ≫ ((IdentityFunctor C) &> x) : by simp
            ... = ((IdentityFunctor C) &> x) ≫ (α.components 𝒞.obj) : by rw NaturalTransformation.naturality_lemma
            ... = x ≫ (α.components 𝒞.obj) : by simp
            ... = x ≫ a : by rw ha
end