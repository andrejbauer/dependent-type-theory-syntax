open import Syntax

module Theory (𝕊 : Signature) where

  open Expression 𝕊

  data BoundaryThesis : ∀ (cl : Class) (𝕄 : MShape) (γ : VShape) → Set where
    bdry-isty : ∀ {𝕄 γ} → BoundaryThesis (obj Ty) 𝕄 γ
    bdry-istm : ∀ {𝕄 γ} (A : ExprTy 𝕄 γ) → BoundaryThesis (obj Tm) 𝕄 γ
    bdry-eqty : ∀ {𝕄 γ} (A B : ExprTy 𝕄 γ) → BoundaryThesis EqTy 𝕄 γ
    bdry-eqtm : ∀ {𝕄 γ} (A : ExprTy 𝕄 γ) (u v : ExprTm 𝕄 γ) → BoundaryThesis EqTm 𝕄 γ

  MContext : ∀ (𝕄 : MShape) → Set
  MContext 𝕄 = ∀ {cl : Class} {γ : VShape} (M : [ cl , γ ]∈ 𝕄) → BoundaryThesis cl 𝕄 γ

  VContext : ∀ (𝕄 : MShape) (γ : VShape) → Set
  VContext 𝕄 γ = ∀ (x : var γ) → ExprTy 𝕄 γ

  record JudgementThesis (cl : Class) (𝕄 : MShape) (γ : VShape) : Set where
    constructor _⟦_⟧
    field
      jdg-bdry : BoundaryThesis cl 𝕄 γ
      jdg-head : Expr cl 𝕄 γ

  data Abstracted (F : VShape → Set) : Set where
    non-abstr : F 𝟘 → Abstracted F
    abstr : ∀ γ → Abstracted (λ δ → F (γ ⊕ δ)) → Abstracted F

  AbstractedBoundary : Class → MShape → VShape → Set
  AbstractedBoundary cl 𝕄 γ = Abstracted (λ δ → BoundaryThesis cl 𝕄 (γ ⊕ δ))

  AbstractedJudgement : Class → MShape → VShape → Set
  AbstractedJudgement cl 𝕄 γ = Abstracted (λ δ → JudgementThesis cl 𝕄 (γ ⊕ δ))

  Hypothetical : ∀ (F : MShape → VShape → Set) → Set
  Hypothetical F = ∀ {𝕄 : MShape} {γ : VShape} (Θ : MContext 𝕄) (Γ : VContext 𝕄 γ) → F 𝕄 γ

  HypotheticalBoundary : Class → Set
  HypotheticalBoundary cl = Hypothetical (AbstractedBoundary cl)

  HypotheticalJudgement : Class → Set
  HypotheticalJudgement cl = Hypothetical (AbstractedJudgement cl)

  RawRule : ∀ (cl : Class) → Set
  RawRule cl = HypotheticalJudgement cl
