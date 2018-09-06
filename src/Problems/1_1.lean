import category_theory.isomorphism
import ncategories.Ndefs
open category_theory
open category_theory.isomorphism
open category_theory.functor
open tactic

--delaration of universes and variables
universes u v u₁ v₁
variables (C : Type u₁) [𝒞 : category.{u₁ v₁} C]
include 𝒞

-- 1a Show that identities in a category are unique
theorem uniq_id (X : C) (id' : X ⟶ X) : (∀ {A : C} (g : X ⟶ A), id' ≫ g = g) → (∀ {A : C} (g : A ⟶ X), g ≫ id' = g) → (id' = 𝟙X) :=
    begin
        intros hl hr,
        transitivity,
        symmetry,
        exact category.comp_id C id',
        exact hl(𝟙X)
    end

-- 1b Show that a morphism with both a left inverse and right inverse is an isomorphism
theorem landr_id (X Y Z : C) (f : X ⟶ Y) : (∃ gl : Y ⟶ X, gl ≫ f = 𝟙Y) → (∃ gr : Y ⟶ X, f ≫ gr = 𝟙X) → (is_iso' f) :=
    begin
    intros,
    cases (classical.indefinite_description _ a) with gl hl,
    cases (classical.indefinite_description _ a_1) with gr hr,
    apply nonempty.intro 
        (⟨gr, hr,    
            begin 
                simp,
                symmetry,
                exact calc
                𝟙Y     = gl ≫ f                : eq.symm hl
                ...    = gl ≫ 𝟙X ≫ f           : by rw category.id_comp C f
                ...    = (gl ≫ 𝟙X) ≫ f         : by rw category.assoc
                ...    = (gl ≫ (f ≫ gr)) ≫ f  : by rw hr
                ...    = ((gl ≫ f) ≫ gr) ≫ f  : by rw category.assoc C gl f gr 
                ...    = (𝟙Y ≫ gr) ≫ f         : by rw hl
                ...    = gr ≫ f                 : by rw category.id_comp C gr
            end⟩ 
        : is_iso f)
    end

-- 1c Consider f : X ⟶ Y and g : Y ⟶ Z. Show that if two out of f, g and gf are isomorphisms,then so is the third.
section Two_Out_Of_Three
    variables (X Y Z : C)
    variables (f : X ⟶ Y) (g : Y ⟶ Z)
    
    theorem tootfirsec : is_iso' f → is_iso' g → is_iso' (f ≫ g) :=
        begin
            intros hf hg,
            apply hf.elim,
            apply hg.elim,
            intros Ig If,
            exact nonempty.intro 
                ⟨Ig.1 ≫ If.1,
                begin
                    simp,
                    exact calc
                    f ≫ g ≫ Ig.1 ≫ If.1 = f ≫ (g ≫ Ig.1) ≫ If.1 : by rw category.assoc
                    ...                   = f ≫ 𝟙Y ≫ If.1          : by rw is_iso.hom_inv_id
                    ...                   = f ≫ If.1               : by rw category.id_comp
                    ...                   = 𝟙X                      : by rw is_iso.hom_inv_id
                end,    
                begin 
                    simp,
                    exact calc
                        Ig.1 ≫ If.1 ≫ f ≫ g  = Ig.1 ≫ (If.1 ≫ f) ≫ g : by rw category.assoc
                        ...                    = Ig.1 ≫ 𝟙Y ≫ g          : by rw is_iso.inv_hom_id
                        ...                    = Ig.1 ≫ g               : by rw category.id_comp
                        ...                    = 𝟙Z                      : by rw is_iso.inv_hom_id
                end⟩
        end

    theorem tootsecthi : is_iso' g → is_iso' (f ≫ g) → is_iso' f :=
        begin
            intros hg hfg,
            apply hg.elim,
            apply hfg.elim,
            intros Ifg Ig,
            exact nonempty.intro
                ⟨g ≫ Ifg.1,
                    begin
                        simp,
                        exact calc
                            f ≫ g ≫ Ifg.1 = (f ≫ g) ≫ Ifg.1 : by rw category.assoc
                            ... = 𝟙X : by rw is_iso.hom_inv_id
                    end,
                    begin
                        simp,
                        exact calc
                            g ≫ Ifg.1 ≫ f = (g ≫ Ifg.1 ≫ f) ≫ 𝟙Y : by rw category.comp_id
                            ... = g ≫ (Ifg.1 ≫ f) ≫ 𝟙Y : by rw category.assoc
                            ... = g ≫ Ifg.1 ≫ f ≫ 𝟙Y : by rw category.assoc
                            ... = g ≫ Ifg.1 ≫ f ≫ g ≫ Ig.1 : by rw is_iso.hom_inv_id
                            ... = g ≫ (Ifg.1 ≫ ((f ≫ g) ≫ Ig.1)) : by rw category.assoc
                            ... = g ≫ (Ifg.1 ≫ (f ≫ g)) ≫ Ig.1 : by rw (category.assoc C Ifg.1 (f ≫ g) Ig.1)
                            ... = g ≫ 𝟙Z ≫ Ig.1 : by rw is_iso.inv_hom_id
                            ... = g ≫ Ig.1 : by rw category.id_comp
                            ... = 𝟙Y : by rw is_iso.hom_inv_id
                    end⟩
        end
    theorem tootfirthi : is_iso' f → is_iso' (f ≫ g) → is_iso' g :=
        begin
            intros hf hfg,
            apply hf.elim,
            apply hfg.elim,
            intros Ifg If,
            exact nonempty.intro
                ⟨Ifg.1 ≫ f,
                    begin
                        simp,
                        exact calc
                            g ≫ Ifg.1 ≫ f = 𝟙Y ≫ g ≫ Ifg.1 ≫ f : by rw category.id_comp
                            ... = (If.1 ≫ f) ≫ g ≫ Ifg.1 ≫ f : by rw is_iso.inv_hom_id
                            ... = ((If.1 ≫ f) ≫ g) ≫ Ifg.1 ≫ f : by rw (category.assoc C (If.1 ≫ f) g (Ifg.1 ≫ f))
                            ... = (If.1 ≫ (f ≫ g)) ≫ Ifg.1 ≫ f : by rw (category.assoc C If.1 f g)
                            ... = If.1 ≫ (f ≫ g) ≫ Ifg.1 ≫ f : by rw category.assoc
                            ... = If.1 ≫ ((f ≫ g) ≫ Ifg.1) ≫ f : by rw (category.assoc C (f ≫ g) Ifg.1 f)
                            ... = If.1 ≫ 𝟙X ≫ f : by rw is_iso.hom_inv_id
                            ... = If.1 ≫ f : by rw category.id_comp
                            ... = 𝟙Y : by rw is_iso.inv_hom_id
                    end,
                    begin
                        simp
                    end⟩
        end
end Two_Out_Of_Three

variables {D : Type u} [𝒟 : category.{u v} D]
include 𝒟

-- 1d Show functors preserve isomorphisms
theorem fun_id (F : C ⥤ D) (X Y : C) (f : X ⟶ Y) : (is_iso' f) → (is_iso' (F.map f)) :=
    begin
        intro hf,
        apply hf.elim,
        intro If,
        exact nonempty.intro
            /- ⟨F.map If.1,
            begin
                simp,
                exact calc
                    (F.map f) ≫ (F.map If.1) = F.map (f ≫ If.1) : by rw functor.functoriality_lemma
                    ... = F.map 𝟙X : by rw is_iso.hom_inv_id
                    ... = 𝟙 (F X) : by rw functor.identities
            end,
            begin
                simp,
                exact calc
                    (F.map If.1) ≫ (F.map f) = F.map (If.1 ≫ f) : by rw functor.functoriality_lemma
                    ... = F.map 𝟙Y : by rw is_iso.inv_hom_id
                    ... = 𝟙 (F Y) : by rw functor.identities
            end⟩ -/
            (is_iso.of_iso (F.on_iso ⟨f , If.1, by simp, by simp⟩))
    end

-- 1e Show that if F : C ⥤ D is full and faithful, and F.map f : F A ⟶ F B is an isomorphism in 𝒟, then f : A ⟶ B is an isomorphism in 𝒞
theorem reflecting_isomorphisms (F : C ⥤ D) (X Y : C) (f : X ⟶ Y) : is_Full_Functor F → is_Faithful_Functor F → is_iso' (F.map f) → is_iso' f :=
    begin
        intros hfu hfa hFf,
        apply hFf.elim,
        intro IFf,
        cases (classical.indefinite_description _ (hfu IFf.1)) with g hg,
        apply nonempty.intro
            (⟨g,
            begin
                simp,
                exact hfa
                    (calc
                        F.map (f ≫ g) = (F.map f) ≫ (F.map g) : by rw functor.map_comp
                        ... = 𝟙(F X) : by rw [hg, is_iso.hom_inv_id]
                        ... = F.map (𝟙X) : by rw functor.map_id
                    )
            end,
            begin
                simp,
                exact hfa
                    (calc
                        F.map (g ≫ f) = (F.map g) ≫ (F.map f) : by rw functor.map_comp
                        ... = 𝟙(F Y) : by rw [hg, is_iso.inv_hom_id]
                        ... = F.map (𝟙Y) : by rw functor.map_id
                    )
            end⟩
            : is_iso f)
    end