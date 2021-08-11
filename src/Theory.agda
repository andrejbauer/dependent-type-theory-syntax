open import Syntax
import Renaming
import Instantiation

module Theory (𝕊 : Signature) where

  open Expression 𝕊
  open Instantiation
  open Renaming

  infix 5 □⦂_
  infix 5 _≡_⦂type-by□
  infix 5 _≡_⦂_by□

  data BoundaryThesis : ∀ (cl : Class) (𝕄 : MShape) (γ : VShape) → Set where
    □⦂type : ∀ {𝕄 γ} → BoundaryThesis (obj Ty) 𝕄 γ
    □⦂_ : ∀ {𝕄 γ} (A : ExprTy 𝕄 γ) → BoundaryThesis (obj Tm) 𝕄 γ
    _≡_⦂type-by□ : ∀ {𝕄 γ} (A B : ExprTy 𝕄 γ) → BoundaryThesis EqTy 𝕄 γ
    _≡_⦂_by□ : ∀ {𝕄 γ} (u v : ExprTm 𝕄 γ) (A : ExprTy 𝕄 γ) → BoundaryThesis EqTm 𝕄 γ

  rename-boundary-thesis : ∀ {cl 𝕄 γ δ} → (γ →ʳ δ) → BoundaryThesis cl 𝕄 γ → BoundaryThesis cl 𝕄 δ
  rename-boundary-thesis ρ □⦂type = □⦂type
  rename-boundary-thesis ρ (□⦂ A) = □⦂ [ ρ ]ʳ A
  rename-boundary-thesis ρ (A ≡ B ⦂type-by□) = [ ρ ]ʳ A ≡ [ ρ ]ʳ B ⦂type-by□
  rename-boundary-thesis ρ (u ≡ v ⦂ A by□) = [ ρ ]ʳ u ≡ [ ρ ]ʳ v ⦂ [ ρ ]ʳ A by□

  instantiate-boundary-thesis : ∀ {cl 𝕂 𝕄 γ} → (𝕊 % 𝕂 →ⁱ 𝕄 ∥ γ) → BoundaryThesis cl 𝕂 γ → BoundaryThesis cl 𝕄 γ
  instantiate-boundary-thesis I □⦂type = □⦂type
  instantiate-boundary-thesis I (□⦂ A) = □⦂ [ I ]ⁱ A
  instantiate-boundary-thesis I (A ≡ B ⦂type-by□) = [ I ]ⁱ A ≡ [ I ]ⁱ B ⦂type-by□
  instantiate-boundary-thesis I (u ≡ v ⦂ A by□) = [ I ]ⁱ u ≡ [ I ]ⁱ v ⦂ [ I ]ⁱ A by□

  VContext : ∀ (𝕄 : MShape) (γ : VShape) → Set
  VContext 𝕄 γ = ∀ (x : var γ) → ExprTy 𝕄 γ

  instantiate-vcontext : ∀ {𝕂 𝕄 γ} (I : 𝕊 % 𝕂 →ⁱ 𝕄 ∥ γ) (Γ : VContext 𝕂 γ) → VContext 𝕄 γ
  instantiate-vcontext I Γ x = [ I ]ⁱ Γ x

  VExtension : ∀ (𝕄 : MShape) (γ δ : VShape) → Set
  VExtension 𝕄 γ δ = ∀ (x : var δ) → ExprTy 𝕄 (γ ⊕ δ)

  empty-vextension : ∀ {𝕄 γ} → VExtension 𝕄 γ 𝟘
  empty-vextension ()

  -- variable context extension
  infixl 6 _⊕ᶜ_

  _⊕ᶜ_ : ∀ {𝕄 γ δ} → VContext 𝕄 γ → VExtension 𝕄 γ δ → VContext 𝕄 (γ ⊕ δ)
  (Γ ⊕ᶜ Δ) (var-left x) = [ var-left ]ʳ (Γ x)
  (Γ ⊕ᶜ Δ) (var-right y) = Δ y

  rename-vextension : ∀ {𝕄 β γ δ} → (β →ʳ γ) → VExtension 𝕄 β δ → VExtension 𝕄 γ δ
  rename-vextension ρ Δ x =  [ [ (var-left ∘ʳ ρ) , var-right ]ʳ ]ʳ Δ x

  instantiate-vextension : ∀ {𝕂 𝕄 γ δ} → (I : 𝕊 % 𝕂 →ⁱ 𝕄 ∥ γ) → VExtension 𝕂 γ δ → VExtension 𝕄 γ δ
  instantiate-vextension I Δ x = [ ⇑ⁱ I ]ⁱ (Δ x)

  record JudgementThesis (cl : Class) (𝕄 : MShape) (γ : VShape) : Set where
    constructor _⟦_⟧
    field
      jdg-bdry : BoundaryThesis cl 𝕄 γ
      jdg-head : Expr cl 𝕄 γ

  presupposition : ∀ {cl 𝕄 γ} → JudgementThesis cl 𝕄 γ → BoundaryThesis cl 𝕄 γ
  presupposition (𝒷 ⟦ _ ⟧) = 𝒷

  -- shorthands for the four judgement forms

  infix 5 _⦂type
  _⦂type : ∀ {𝕄 γ} (A : ExprTy 𝕄 γ) → JudgementThesis (obj Ty) 𝕄 γ
  A ⦂type = □⦂type ⟦ A ⟧

  infix 5 _⦂_
  _⦂_ : ∀ {𝕄 γ} (e : ExprTm 𝕄 γ) (A : ExprTy 𝕄 γ) → JudgementThesis (obj Tm) 𝕄 γ
  e ⦂ A = (□⦂ A) ⟦ e ⟧

  infix 5 _≡_by_
  _≡_by_ : ∀ {𝕄 γ} (A B : ExprTy 𝕄 γ) (ξ : Expr EqTy 𝕄 γ) → JudgementThesis (EqTy) 𝕄 γ
  A ≡ B by ξ = (A ≡ B ⦂type-by□) ⟦ ξ ⟧

  infix 5 _≡_⦂_by_
  _≡_⦂_by_ : ∀ {𝕄 γ} (d e : ExprTm 𝕄 γ) (A : ExprTy 𝕄 γ) (ξ : Expr EqTm 𝕄 γ) → JudgementThesis (EqTm) 𝕄 γ
  d ≡ e ⦂ A by ξ = (d ≡ e ⦂ A by□) ⟦ ξ ⟧

  rename-judgement-thesis : ∀ {cl 𝕄 γ δ} → (γ →ʳ δ) → JudgementThesis cl 𝕄 γ → JudgementThesis cl 𝕄 δ
  rename-judgement-thesis ρ (b ⟦ e ⟧) = (rename-boundary-thesis ρ b) ⟦ [ ρ ]ʳ e ⟧

  instantiate-judgement-thesis : ∀ {cl 𝕂 𝕄 γ} → (𝕊 % 𝕂 →ⁱ 𝕄 ∥ γ) → JudgementThesis cl 𝕂 γ → JudgementThesis cl 𝕄 γ
  instantiate-judgement-thesis I (B ⟦ e ⟧) = (instantiate-boundary-thesis I B) ⟦ [ I ]ⁱ e ⟧

  infix 4 ⟪_⟫_

  record Abstracted (F : MShape → VShape → Set) (𝕄 : MShape) (γ δ : VShape) : Set where
    constructor ⟪_⟫_
    field
      abstr-vextenson : VExtension 𝕄 γ δ
      abstr-body : F 𝕄 (γ ⊕ δ)

  non-abstracted : ∀ (F : MShape → VShape → Set) (r : ∀ {𝕄 β γ} → (β →ʳ γ) → F 𝕄 β → F 𝕄 γ)
                     {𝕄 : MShape} {γ : VShape} (t : F 𝕄 γ) → Abstracted F 𝕄 γ 𝟘
  non-abstracted F r t = ⟪ empty-vextension ⟫ (r var-left t)

  rename-abstracted : ∀ (F : MShape → VShape → Set) (r : ∀ {𝕄 β γ} → (β →ʳ γ) → F 𝕄 β → F 𝕄 γ) {𝕄 β γ δ} (ρ : β →ʳ γ) →
                        Abstracted F 𝕄 β δ → Abstracted F 𝕄 γ δ
  rename-abstracted F r ρ (⟪ Δ ⟫ t) = ⟪ rename-vextension ρ Δ ⟫ (r (⇑ʳ ρ) t)

  instantiate-abstracted : ∀ (F : MShape → VShape → Set) (ι : ∀ {𝕂 𝕄 γ} → (𝕊 % 𝕂 →ⁱ 𝕄 ∥ γ) → F 𝕂 γ → F 𝕄 γ)
                             {𝕂 𝕄 γ δ} (I : 𝕊 % 𝕂 →ⁱ 𝕄 ∥ γ) → Abstracted F 𝕂 γ δ → Abstracted F 𝕄 γ δ
  instantiate-abstracted F ι I (⟪ Δ ⟫ t) = ⟪ (instantiate-vextension I Δ) ⟫ ι (⇑ⁱ I) t

  AbstractedBoundary : ∀ cl 𝕄 γ δ → Set
  AbstractedBoundary cl 𝕄 γ δ = Abstracted (BoundaryThesis cl) 𝕄 γ δ

  infix 4 ⟪⟫ᵇ_
  ⟪⟫ᵇ_ : ∀ {cl 𝕄 γ} → BoundaryThesis cl 𝕄 γ → AbstractedBoundary cl 𝕄 γ 𝟘
  ⟪⟫ᵇ_ {cl = cl} 𝒷 = non-abstracted (BoundaryThesis cl) rename-boundary-thesis 𝒷

  rename-abstracted-boundary : ∀ {cl 𝕄 β γ δ} (ρ : β →ʳ γ) →
                                 AbstractedBoundary cl 𝕄 β δ → AbstractedBoundary cl 𝕄 γ δ
  rename-abstracted-boundary {cl = cl} = rename-abstracted (BoundaryThesis cl) rename-boundary-thesis

  instantiate-abstracted-boundary : ∀ {cl 𝕂 𝕄 γ δ} (I : 𝕊 % 𝕂 →ⁱ 𝕄 ∥ γ) →
                                      AbstractedBoundary cl 𝕂 γ δ → AbstractedBoundary cl 𝕄 γ δ
  instantiate-abstracted-boundary {cl = cl} = instantiate-abstracted (BoundaryThesis cl) instantiate-boundary-thesis

  AbstractedJudgement : ∀ cl 𝕄 γ δ → Set
  AbstractedJudgement cl 𝕄 γ δ = Abstracted (JudgementThesis cl) 𝕄 γ δ

  infix 4 ⟪⟫ʲ_
  ⟪⟫ʲ_ : ∀ {cl 𝕄 γ} → JudgementThesis cl 𝕄 γ → AbstractedJudgement cl 𝕄 γ 𝟘
  ⟪⟫ʲ_ {cl = cl} 𝒷 = non-abstracted (JudgementThesis cl) rename-judgement-thesis 𝒷

  fill-abstraction : ∀ {cl 𝕄 γ δ} (ℬ : AbstractedBoundary cl 𝕄 γ δ) → Arg cl 𝕄 γ δ → AbstractedJudgement cl 𝕄 γ δ
  fill-abstraction (⟪ Δ ⟫ 𝒷) e = ⟪ Δ ⟫ (𝒷 ⟦ e ⟧)

  rename-abstracted-judgement : ∀ {cl 𝕄 β γ δ} (ρ : β →ʳ γ) →
                                  AbstractedJudgement cl 𝕄 β δ → AbstractedJudgement cl 𝕄 γ δ
  rename-abstracted-judgement {cl = cl} = rename-abstracted (JudgementThesis cl) rename-judgement-thesis

  instantiate-abstracted-judgement : ∀ {cl 𝕂 𝕄 γ δ} (I : 𝕊 % 𝕂 →ⁱ 𝕄 ∥ γ) →
                                       AbstractedJudgement cl 𝕂 γ δ → AbstractedJudgement cl 𝕄 γ δ
  instantiate-abstracted-judgement {cl = cl} = instantiate-abstracted (JudgementThesis cl) instantiate-judgement-thesis

  MContext : ∀ (𝕄 : MShape) → Set
  MContext 𝕄 = ∀ {clᴹ : Class} {γᴹ : VShape} (M : [ clᴹ , γᴹ ]∈ 𝕄) → AbstractedBoundary clᴹ 𝕄 𝟘 γᴹ

  HypotheticalBoundary : ∀ cl {𝕄 : MShape} {γ} (Θ : MContext 𝕄) (Γ : VContext 𝕄 γ) δ → Set
  HypotheticalBoundary cl {𝕄 = 𝕄} {γ = γ} Θ Γ δ = Abstracted (BoundaryThesis cl) 𝕄 γ δ

  instantiate-hypothetical-boundary :
    ∀ {cl 𝕂 𝕄 γ δ} (I : 𝕊 % 𝕂 →ⁱ 𝕄 ∥ γ) {Ξ : MContext 𝕂} {Γ : VContext 𝕂 γ} {Θ : MContext 𝕄} →
      HypotheticalBoundary cl Ξ Γ δ → HypotheticalBoundary cl Θ (instantiate-vcontext I Γ) δ
  instantiate-hypothetical-boundary I B = instantiate-abstracted-boundary I B

  HypotheticalJudgement : ∀ cl {𝕄 : MShape} {γ} (Θ : MContext 𝕄) (Γ : VContext 𝕄 γ) δ → Set
  HypotheticalJudgement cl {𝕄 = 𝕄} {γ = γ} Θ Γ δ = Abstracted (JudgementThesis cl) 𝕄 γ δ

  instantiate-hypothetical-judgement :
    ∀ {cl 𝕂 𝕄 γ δ} (I : 𝕊 % 𝕂 →ⁱ 𝕄 ∥ γ) {Ξ : MContext 𝕂} {Γ : VContext 𝕂 γ} {Θ : MContext 𝕄} →
      HypotheticalJudgement cl Ξ Γ δ → HypotheticalJudgement cl Θ (instantiate-vcontext I Γ) δ
  instantiate-hypothetical-judgement I B = instantiate-abstracted-judgement I B

  infix 6 _⇛_

  record Rule (cl : Class) (𝕄 : MShape) : Set where
    constructor _⇛_

    field
      premises : MContext 𝕄
      conclusion : JudgementThesis cl 𝕄 𝟘

  Theory = ∀ {cl} {𝕄} → Rule cl 𝕄 → Set

  instantiate-conclusion : ∀ {cl 𝕂 𝕄 γ} (I : 𝕊 % 𝕂 →ⁱ 𝕄 ∥ γ) → JudgementThesis cl 𝕂 𝟘 → JudgementThesis cl 𝕄 γ
  instantiate-conclusion I 𝒿 = instantiate-judgement-thesis I (rename-judgement-thesis 𝟘-initial 𝒿)

  module Derivation (𝒯 : Theory) where

    open Rule

    infix 3 _,_⊢ʲ_
    infix 3 _,_⊢ᵇ_

    data _,_⊢ʲ_ :
      ∀ {cl 𝕄 γ δ} (Θ : MContext 𝕄) (Γ : VContext 𝕄 γ) (𝒥 : HypotheticalJudgement cl Θ Γ δ) → Set

    data _,_⊢ᵇ_ :
      ∀ {cl 𝕄 γ δ} (Θ : MContext 𝕄) (Γ : VContext 𝕄 γ) (ℬ : HypotheticalBoundary cl Θ Γ δ) → Set

    -- derivable instantiation
    is-derivable : ∀ {𝕂 𝕄 γ} (I : 𝕊 % 𝕂 →ⁱ 𝕄 ∥ γ) (Ξ : MContext 𝕂) (Θ : MContext 𝕄) (Γ : VContext 𝕄 γ) → Set
    is-derivable {𝕂 = 𝕂} I Ξ Θ Γ =
       ∀ {clᴷ γᴷ} (M : [ clᴷ , γᴷ ]∈ 𝕂) →
         Θ , Γ ⊢ʲ fill-abstraction (instantiate-abstracted-boundary I (rename-abstracted-boundary 𝟘-initial (Ξ M))) (I M)

    data _,_⊢ʲ_ where

      TT-VAR :
        ∀ {𝕄 γ} {Θ : MContext 𝕄} {Γ : VContext 𝕄 γ} (x : var γ) → Θ , Γ ⊢ʲ (⟪⟫ʲ (expr-var x ⦂ Γ x))

      TT-RULE :
        ∀ {cl 𝕂 𝕄 γ} {Ξ : MContext 𝕂} {Θ : MContext 𝕄} {Γ : VContext 𝕄 γ}
          (I : 𝕊 % 𝕂 →ⁱ 𝕄 ∥ γ) {𝒿 : JudgementThesis cl 𝕂 𝟘} (R : 𝒯 (Ξ ⇛ 𝒿)) →
          Θ , Γ ⊢ᵇ ⟪⟫ᵇ instantiate-boundary-thesis I (rename-boundary-thesis 𝟘-initial (presupposition 𝒿)) →
          is-derivable I Ξ Θ Γ →
          Θ , Γ ⊢ʲ ⟪⟫ʲ instantiate-conclusion I 𝒿

      TT-ABSTR :
        ∀ {cl 𝕄 γ δ} {Θ : MContext 𝕄} {Γ : VContext 𝕄 γ} {Δ : VExtension 𝕄 γ δ} {𝒿 : JudgementThesis cl 𝕄 (γ ⊕ δ) } →
          Θ , Γ ⊕ᶜ Δ ⊢ʲ ⟪⟫ʲ 𝒿 →
          Θ , Γ ⊢ʲ ⟪ Δ ⟫ 𝒿

      TT-META :
        {!!}

      TT-META-CONGR :
        {!!}

      TT-EQTY-REFL :
        {!!}
      TT-EQTY-SYM :
        {!!}
      TT-EQTY-TRANS :
        {!!}
      TT-EQTM-REFL :
        {!!}
      TT-EQTM-SYM :
        {!!}
      TT-EQTM-TRANS :
        {!!}
      TT-CONV-TM :
        {!!}
      TT-CONV-EQTM :
        {!!}

    data _,_⊢ᵇ_ where

      TT-BDRY-TY :
        ∀ {𝕄 γ} {Θ : MContext 𝕄} {Γ : VContext 𝕄 γ} →
          Θ , Γ ⊢ᵇ ⟪⟫ᵇ □⦂type

      TT-BDRY-TM :
        ∀ {𝕄 γ} {Θ : MContext 𝕄} {Γ : VContext 𝕄 γ} {A} →
          Θ , Γ ⊢ʲ ⟪⟫ʲ A ⦂type →
          Θ , Γ ⊢ᵇ ⟪⟫ᵇ □⦂ A

      TT-BDRY-EQTY :
        ∀ {𝕄 γ} {Θ : MContext 𝕄} {Γ : VContext 𝕄 γ} {A B} →
          Θ , Γ ⊢ʲ ⟪⟫ʲ A ⦂type →
          Θ , Γ ⊢ʲ ⟪⟫ʲ B ⦂type →
          Θ , Γ ⊢ᵇ ⟪⟫ᵇ A ≡ B ⦂type-by□

      TT-BDRY-EQTM :
        ∀ {𝕄 γ} {Θ : MContext 𝕄} {Γ : VContext 𝕄 γ} {u v A} →
          Θ , Γ ⊢ʲ ⟪⟫ʲ A ⦂type →
          Θ , Γ ⊢ʲ ⟪⟫ʲ u ⦂ A →
          Θ , Γ ⊢ʲ ⟪⟫ʲ v ⦂ A →
          Θ , Γ ⊢ᵇ ⟪⟫ᵇ u ≡ v ⦂ A by□

      TT-BDRY-ABSTR :
        ∀ {cl 𝕄 γ δ} {Θ : MContext 𝕄} {Γ : VContext 𝕄 γ} {Δ : VExtension 𝕄 γ δ} {𝒷 : BoundaryThesis cl 𝕄 (γ ⊕ δ) } →
          Θ , Γ ⊕ᶜ Δ ⊢ᵇ ⟪⟫ᵇ 𝒷 →
          Θ , Γ ⊢ᵇ ⟪ Δ ⟫ 𝒷

    -- Missing: well-formed extensions and contexts
