import ncategory_theory.ndefs
open category_theory category_theory.functor function

universes u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄ 

--4a Show that any functor F : C ⥤ D can be factorised as L : C ⥤ E and R : E ⥤ D where L is bijective on objects, and R is full and faithful.

structure functor_decomp (C : Type u₁) [category.{u₁ v₁} C] (D : Type u₂) [category.{u₂ v₂} D] (F: C ⥤ D) : Type (max u₁ v₁ u₂ v₂+1) :=
    (E : Type u₁)
    (decomp_category : (category.{u₁ v₂} E))
    (functor1 : C ⥤ E)
    (functor2 : E ⥤ D)
    (biject : bijective(functor1.obj) . obviously)
    (fandf : is_Faithful_Functor functor2 ∧ is_Full_Functor functor2)

definition canonical_functor_decomp (C : Type u₁) [category.{u₁ v₁} C] (D : Type u₂) [category.{u₂ v₂} D] (F : C ⥤ D) : (functor_decomp _ _ F) := 
    {
        E := C,
        decomp_category :=  {
                                hom         := (λ X Y : C, (F X) ⟶ (F Y)),
                                id          := (λ X, 𝟙(F X)),
                                comp        := (λ _ _ _ f g, f ≫ g),
                                id_comp'    := by simp,
                                comp_id'    := by simp,
                                assoc'      := (λ _ _ _ _ _ _ _, by simp)
                            },
        functor1 := {
                        obj         := λ X , X,
                        map'        := λ _ _ f, F.map f,
                        map_id'     := by simp,
                        map_comp'   := (λ _ _ _ _ _ , by simp)
                    },
        functor2 := {
                        obj         := λ X, F X,
                        map'        := λ _ _ f, f,
                        map_id'     := by simp,
                        map_comp'   := (λ _ _ _ _ _ , by simp)
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
variables (L : B ⥤ C) (F : B ⥤ D) (R : D ⥤ E) (G : C ⥤ E)
include ℬ 𝒞 𝒟 ℰ


/-noncomputable definition fourb (Linv : C → B) (hlinv : left_inverse L.obj Linv) (hrinv : right_inverse L.obj Linv) (hfa : is_Faithful_Functor R) (hfu : is_Full_Functor R) (heq : L ⋙ G = F ⋙ R) : C ⥤ D :=
    {
        obj :=    begin
                            intro Xc,
                            exact F (Linv Xc)
                        end,
        map' :=  begin
                            intros Xc Yc f,
                            exact (classical.indefinite_description _ (hfu (cast 
                                    (calc
                                        (G Xc ⟶ G Yc)    = (G Xc ⟶ G (L Linv Yc)) : by rw hlinv
                                        ...                     = (G (L Linv Xc) ⟶ G (L Linv Yc)) : by rw (hlinv Xc)
                                        ...                     = ((L ⋙ G) Linv Xc ⟶ (L ⋙ G) Linv Yc) : by simp
                                        ...                     = ((F ⋙ R) Linv Xc ⟶ (F ⋙ R) Linv Yc) : by rw heq
                                        ...                     = (R (F Linv Xc)⟶ R (F Linv Yc)) : by simp) (G.map f) ))).1
                        end,
        identities :=   begin
                            intros,
                            let blegh := (classical.indefinite_description (λ (f : F Linv X ⟶ F Linv X), R.map f = cast _ (G.map 𝟙 X)) _),
                            
                        end,
        functoriality :=    begin
                                sorry
                            end
    }
end-/

definition fourb (Linv : C → B) (hlinv : left_inverse L.obj Linv) (hrinv : right_inverse L.obj Linv) (Rff : Full_and_Faithful_Functor R) (heq : L ⋙ G = F ⋙ R) : C ⥤ D :=
    {
        obj         :=    λ Xc, (F (Linv Xc)),
        map'        :=  λ Xc Yc f, Rff.morinv (cast 
                                    (calc
                                        (G Xc ⟶ G Yc)    = (G Xc ⟶ G (L.obj (Linv Yc))) : by rw hlinv
                                        ...                     = (G (L.obj (Linv Xc)) ⟶ G (L.obj (Linv Yc))) : by rw (hlinv Xc)
                                        ...                     = ((L ⋙ G) (Linv Xc) ⟶ (L ⋙ G) (Linv Yc)) : by simp
                                        ...                     = ((F ⋙ R) (Linv Xc) ⟶ (F ⋙ R) (Linv Yc)) : by rw heq
                                        ...                     = (R (F (Linv Xc))⟶ R (F (Linv Yc))) : by simp) (G.map f)),
        map_id'     :=   begin
                            intro Xc,
                            sorry
                        end,
        map_comp'   :=    begin
                                intros Xc Yc Zc f g,
                                sorry
                            end
    }
end