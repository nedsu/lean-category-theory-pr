import category_theory.isomorphism
open category_theory

universes u v u₀ v₀

namespace category_theory.isomorphism

definition is_Isomorphism' {D : Type u} [𝒟 : category.{u v} D] {X Y : D} (f : X ⟶ Y) : Prop := nonempty (is_iso f)

end category_theory.isomorphism



namespace category_theory.functor

variables {D : Type u} [𝒟 : category.{u v} D] {E : Type u₀} [ℰ : category.{u₀ v₀} E]
include 𝒟 ℰ

definition is_Faithful_Functor  (F : D ⥤ E) := 
                                ∀ {A B : D} {f g : A ⟶ B} (p : F.map' f = F.map' g), f = g

definition is_Full_Functor      (F : D ⥤ E)  := 
                                ∀ {A B : D} (h : F A ⟶ F B), ∃f : A ⟶ B, F.map' f = h

structure Full_and_Faithful_Functor (F : D ⥤ E) : Type (max u v u₀ v₀) :=
    (morinv : Π {X Y : D}, (F X ⟶ F Y) → (X ⟶ Y))
    (left_inverse' : ∀ {X Y : D} {f : X ⟶ Y}, morinv (F.map' f) = f)
    (right_inverse' : ∀ {X Y : D} {f : F X ⟶ F Y}, F.map' (morinv f) = f)

restate_axiom Full_and_Faithful_Functor.left_inverse'
restate_axiom Full_and_Faithful_Functor.right_inverse'

definition Full_and_Faithful_Functor_is_Full_is_Faithful (F : D ⥤ E) : Full_and_Faithful_Functor F → (is_Full_Functor F ∧ is_Faithful_Functor F) := 
begin
    intro,
    apply and.intro,
        unfold is_Full_Functor,
        intros,
        exact ⟨ a.morinv h, by rw Full_and_Faithful_Functor.right_inverse ⟩,
    
        unfold is_Faithful_Functor,
        intros,
        exact calc
            f       = a.morinv (F.map' f) : by rw Full_and_Faithful_Functor.left_inverse
            ...     = a.morinv (F.map' g) : by rw p
            ...     = g                 : by rw Full_and_Faithful_Functor.left_inverse
end

noncomputable definition is_Full_is_Faithful_to_Full_and_Faithful_Functor (F : D ⥤ E) : (is_Full_Functor F ∧ is_Faithful_Functor F) → Full_and_Faithful_Functor F := 
begin
    intros,
    exact   {
                morinv :=   begin
                                intros _ _ g,
                                exact (classical.indefinite_description _ (a.left g)).1
                            end,
                left_inverse' :=     begin
                                        intros,
                                        exact (a.right ((classical.indefinite_description (λ (x : X ⟶ Y), F.map' x = F.map' f) _).2))
                                    end,
                right_inverse' :=    begin
                                        intros,
                                        exact (classical.indefinite_description (λ (x : X ⟶ Y), F.map' x = f) _).2
                                    end,
            }

end
end category_theory.functor



namespace category_theory.Idempotent

definition is_Idempotent {D : Type u} [𝒟 : category.{u v} D] {X : D} (e : X ⟶ X) := 
                                e ≫ e = e

definition is_Split_Idempotent {D : Type u} [𝒟 : category.{u v} D] {X : D} (e : X ⟶ X) := 
                                ∃(Y : D) (f : X ⟶ Y) (g : Y ⟶ X),(f ≫ g = e)∧(g ≫ f = 𝟙Y) 

lemma Split_Idem_is_Idem {D : Type u} [𝒟 : category.{u v} D] (X : D) (e : X ⟶ X) : (is_Split_Idempotent e) → (is_Idempotent e) :=
    begin
        intro hsi,
        cases (classical.indefinite_description _ hsi) with Y hsi₁,
        cases (classical.indefinite_description _ hsi₁) with f hsi₂,
        cases (classical.indefinite_description _ hsi₂) with g hg,
        exact calc
            e ≫ e = (f ≫ g) ≫ f ≫ g : by rw hg.1
            ... = f ≫ g ≫ f ≫ g : by rw category.assoc
            ... = f ≫ (g ≫ f) ≫ g : by rw category.assoc
            ... = f ≫ 𝟙Y ≫ g : by rw hg.2
            ... = f ≫ g : by rw category.id_comp
            ... =  e : by rw hg.1
    end

end category_theory.Idempotent

