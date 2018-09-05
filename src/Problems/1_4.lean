import ncategories.ndefs
open categories categories.functor function

universes u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄ 

--4a Show that any functor F : C ↝ D can be factorised as L : C ↝ E and R : E ↝ D where L is bijective on objects, and R is full and faithful.

structure functor_decomp (C : Type u₁) [category.{u₁ v₁} C] (D : Type u₂) [category.{u₂ v₂} D] (F: C ↝ D) : Type (max u₁ v₁ u₂ v₂+1) :=
    (E : Type u₁)
    (decomp_category : (category.{u₁ v₂} E))
    (functor1 : C ↝ E)
    (functor2 : E ↝ D)
    (biject : bijective(functor1.onObjects) . obviously)
    (fandf : is_Faithful_Functor functor2 ∧ is_Full_Functor functor2)

definition canonical_functor_decomp (C : Type u₁) [category.{u₁ v₁} C] (D : Type u₂) [category.{u₂ v₂} D] (F : C ↝ D) : (functor_decomp _ _ F) := 
    {
        E := C,
        decomp_category :=  {
                                Hom := (λ X Y : C, (F +> X) ⟶ (F +> Y)),
                                identity := (λ X, 𝟙(F +> X)),
                                compose := (λ _ _ _ f g, f ≫ g),
                                left_identity := by simp,
                                right_identity := by simp,
                                associativity := (λ _ _ _ _ _ _ _, by simp)
                            },
        functor1 := {
                        onObjects := λ X , X,
                        onMorphisms := λ _ _ f, F &> f,
                        identities := by simp,
                        functoriality := (λ _ _ _ _ _ , by simp)
                    },
        functor2 := {
                        onObjects := λ X, F +> X,
                        onMorphisms := λ _ _ f, f,
                        identities := by simp,
                        functoriality := (λ _ _ _ _ _ , by simp)
                    },
        biject :=   ⟨
                        begin
                            simp,
                            unfold function.injective,
                            exact λ _ _, id
                        end,
                        begin
                            simp,
                            unfold function.surjective,
                            intro,
                            exact ⟨b, eq.refl b⟩
                        end
                    ⟩,
        fandf :=    ⟨
                        begin
                            unfold is_Faithful_Functor,
                            simp,
                            intros,
                            trivial
                        end
                    ,
                        begin
                            unfold is_Full_Functor,
                            simp,
                        end
                    ⟩
    }

--4b
section
variable {B : Type u₁}
variable [ℬ : category.{u₁ v₁} B]
variable {C : Type u₂}
variable [𝒞 : category.{u₂ v₂} C]
variable {D : Type u₃}
variable [𝒟 : category.{u₃ v₃} D]
variable {E : Type u₄}
variable [ℰ : category.{u₄ v₄} E]
variables (L : B ↝ C) (F : B ↝ D) (R : D ↝ E) (G : C ↝ E)
include ℬ 𝒞 𝒟 ℰ


/-noncomputable definition fourb (Linv : C → B) (hlinv : left_inverse L.onObjects Linv) (hrinv : right_inverse L.onObjects Linv) (hfa : is_Faithful_Functor R) (hfu : is_Full_Functor R) (heq : L ⋙ G = F ⋙ R) : C ↝ D :=
    {
        onObjects :=    begin
                            intro Xc,
                            exact F +> (Linv Xc)
                        end,
        onMorphisms :=  begin
                            intros Xc Yc f,
                            exact (classical.indefinite_description _ (hfu (cast 
                                    (calc
                                        (G +> Xc ⟶ G +> Yc)    = (G +> Xc ⟶ G +> (L +> Linv Yc)) : by rw hlinv
                                        ...                     = (G +> (L +> Linv Xc) ⟶ G +> (L +> Linv Yc)) : by rw (hlinv Xc)
                                        ...                     = ((L ⋙ G) +> Linv Xc ⟶ (L ⋙ G) +> Linv Yc) : by simp
                                        ...                     = ((F ⋙ R) +> Linv Xc ⟶ (F ⋙ R) +> Linv Yc) : by rw heq
                                        ...                     = (R +> (F +> Linv Xc)⟶ R +> (F +> Linv Yc)) : by simp) (G &> f) ))).1
                        end,
        identities :=   begin
                            intros,
                            let blegh := (classical.indefinite_description (λ (f : F +> Linv X ⟶ F +> Linv X), R &> f = cast _ (G &> 𝟙 X)) _),
                            
                        end,
        functoriality :=    begin
                                sorry
                            end
    }
end-/

definition fourb (Linv : C → B) (hlinv : left_inverse L.onObjects Linv) (hrinv : right_inverse L.onObjects Linv) (Rff : Full_and_Faithful_Functor R) (heq : L ⋙ G = F ⋙ R) : C ↝ D :=
    {
        onObjects :=    λ Xc, (F +> (Linv Xc)),
        onMorphisms :=  λ Xc Yc f, Rff.morinv (cast 
                                    (calc
                                        (G +> Xc ⟶ G +> Yc)    = (G +> Xc ⟶ G +> (L +> Linv Yc)) : by rw hlinv
                                        ...                     = (G +> (L +> Linv Xc) ⟶ G +> (L +> Linv Yc)) : by rw (hlinv Xc)
                                        ...                     = ((L ⋙ G) +> Linv Xc ⟶ (L ⋙ G) +> Linv Yc) : by simp
                                        ...                     = ((F ⋙ R) +> Linv Xc ⟶ (F ⋙ R) +> Linv Yc) : by rw heq
                                        ...                     = (R +> (F +> Linv Xc)⟶ R +> (F +> Linv Yc)) : by simp) (G &> f)),
        identities :=   begin
                            intro Xc,
                            sorry
                        end,
        functoriality :=    begin
                                intros Xc Yc Zc f g,
                                sorry
                            end
    }
end