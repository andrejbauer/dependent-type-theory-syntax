open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)

open import Syntax
import Renaming

-- Substitutions
module Substitution where

  module Core {𝕊 : SymbolSignature} where

    open Expression 𝕊
    open Renaming
    open Equality

    infix 5 _∥_→ˢ_

    -- the set of substitutions
    _∥_→ˢ_ : MShape → VShape → VShape → Set
    𝕄 ∥ γ →ˢ δ = var γ → ExprTm 𝕄 δ

    -- equality of substitutions

    infix 4 _≈ˢ_

    _≈ˢ_ : ∀ {𝕄} {γ δ} (σ : 𝕄 ∥ γ →ˢ δ) (σ : 𝕄 ∥ γ →ˢ δ) → Set
    σ ≈ˢ τ = ∀ x → σ x ≈ τ x

    -- equality is an equivalence relation

    ≈ˢ-refl : ∀ {𝕄} {γ δ} {σ : 𝕄 ∥ γ →ˢ δ} → σ ≈ˢ σ
    ≈ˢ-refl x = ≈-refl

    ≈ˢ-sym : ∀ {𝕄} {γ δ} {σ τ : 𝕄 ∥ γ →ˢ δ} → σ ≈ˢ τ → τ ≈ˢ σ
    ≈ˢ-sym ξ x = ≈-sym (ξ x)

    ≈ˢ-trans : ∀ {𝕄} {γ δ} {σ τ χ : 𝕄 ∥ γ →ˢ δ} → σ ≈ˢ τ → τ ≈ˢ χ → σ ≈ˢ χ
    ≈ˢ-trans ζ ξ x = ≈-trans (ζ x) (ξ x)

    -- identity substitution
    𝟙ˢ : ∀ {𝕄} {γ} → 𝕄 ∥ γ →ˢ γ
    𝟙ˢ = expr-var

    -- inclusions

    inlˢ : ∀ {𝕄} {γ δ} → 𝕄 ∥ γ →ˢ γ ⊕ δ
    inlˢ x = expr-var (var-left x)

    inrˢ : ∀ {𝕄} {γ δ} → 𝕄 ∥ δ →ˢ γ ⊕ δ
    inrˢ x = expr-var (var-right x)

    -- join of substitutions

    [_,_]ˢ : ∀ {𝕄} {γ δ η} → (𝕄 ∥ γ →ˢ η) → (𝕄 ∥ δ →ˢ η) → (𝕄 ∥ γ ⊕ δ →ˢ η)
    [ ξ , σ ]ˢ (var-left x) = ξ x
    [ ξ , σ ]ˢ (var-right y) = σ y

    -- join respect equality

    [,]ˢ-resp-≈ˢ : ∀ {𝕄} {γ δ η} {ρ₁ ρ₂ : 𝕄 ∥ γ →ˢ η} {τ₁ τ₂ : 𝕄 ∥ δ →ˢ η} →
                 ρ₁ ≈ˢ ρ₂ → τ₁ ≈ˢ τ₂ → [ ρ₁ , τ₁ ]ˢ ≈ˢ [ ρ₂ , τ₂ ]ˢ
    [,]ˢ-resp-≈ˢ ζ ξ (var-left x) = ζ x
    [,]ˢ-resp-≈ˢ ζ ξ (var-right y) = ξ y

    -- substutution extension

    ⇑ˢ : ∀ {𝕄} {γ δ η} → (𝕄 ∥ γ →ˢ δ) → (𝕄 ∥ γ ⊕ η →ˢ δ ⊕ η)
    ⇑ˢ σ (var-left x) = [ var-left ]ʳ σ x
    ⇑ˢ σ (var-right y) = expr-var (var-right y)

    -- extension preserves equality

    ⇑ˢ-resp-≈ˢ : ∀ {𝕄} {γ δ η} {σ τ : 𝕄 ∥ γ →ˢ δ} → σ ≈ˢ τ → ⇑ˢ {η = η} σ ≈ˢ ⇑ˢ τ
    ⇑ˢ-resp-≈ˢ ξ (var-left x) = []ʳ-resp-≈ var-left (ξ x)
    ⇑ˢ-resp-≈ˢ ξ (var-right y) = ≈-refl

    -- extension preserves identity

    ⇑ˢ-𝟙ˢ : ∀ {𝕄} {γ δ} → ⇑ˢ 𝟙ˢ ≈ˢ 𝟙ˢ {𝕄 = 𝕄} {γ = γ ⊕ δ}
    ⇑ˢ-𝟙ˢ (var-left x) = ≈-refl
    ⇑ˢ-𝟙ˢ (var-right x) = ≈-refl

    -- action of a substitution

    infix 5 [_]ˢ_

    [_]ˢ_ : ∀ {cl 𝕄} {γ δ} → (𝕄 ∥ γ →ˢ δ) → Expr cl 𝕄 γ → Expr cl 𝕄 δ
    [ σ ]ˢ (expr-var x) =  σ x
    [ σ ]ˢ (expr-symb S es) = expr-symb S (λ i → [ ⇑ˢ σ ]ˢ es i)
    [ σ ]ˢ (expr-meta M ts) = expr-meta M (λ i → [ σ ]ˢ ts i )
    [ σ ]ˢ expr-eqty = expr-eqty
    [ σ ]ˢ expr-eqtm = expr-eqtm

    -- the action respects equality

    []ˢ-resp-≈ : ∀ {cl 𝕄} {γ δ} (σ : 𝕄 ∥ γ →ˢ δ) {t u : Expr cl 𝕄 γ} → t ≈ u → [ σ ]ˢ t ≈ [ σ ]ˢ u
    []ˢ-resp-≈ σ (≈-≡ ξ) = ≈-≡ (cong ([ σ ]ˢ_) ξ)
    []ˢ-resp-≈ σ (≈-symb ξ) = ≈-symb (λ i → []ˢ-resp-≈ (⇑ˢ σ) (ξ i))
    []ˢ-resp-≈ σ (≈-meta ξ) = ≈-meta (λ i → []ˢ-resp-≈ σ (ξ i))

    []ˢ-resp-≈ˢ : ∀ {cl 𝕄} {γ δ} {σ τ : 𝕄 ∥ γ →ˢ δ} → σ ≈ˢ τ → ∀ (t : Expr cl 𝕄 γ) → [ σ ]ˢ t ≈ [ τ ]ˢ t
    []ˢ-resp-≈ˢ ξ (expr-var x) = ξ x
    []ˢ-resp-≈ˢ ξ (expr-symb S es) = ≈-symb (λ i → []ˢ-resp-≈ˢ (⇑ˢ-resp-≈ˢ ξ) (es i))
    []ˢ-resp-≈ˢ ξ (expr-meta M ts) = ≈-meta (λ i → []ˢ-resp-≈ˢ ξ (ts i))
    []ˢ-resp-≈ˢ ξ expr-eqty = ≈-eqty
    []ˢ-resp-≈ˢ ξ expr-eqtm = ≈-eqtm

    []ˢ-resp-≈ˢ-≈ : ∀ {cl 𝕄} {γ δ} {σ τ : 𝕄 ∥ γ →ˢ δ} {t u : Expr cl 𝕄 γ} → σ ≈ˢ τ → t ≈ u → [ σ ]ˢ t ≈ [ τ ]ˢ u
    []ˢ-resp-≈ˢ-≈ {τ = τ} {t = t} ζ ξ = ≈-trans ([]ˢ-resp-≈ˢ ζ t) ([]ˢ-resp-≈ τ ξ)

    -- composition of substitutions

    infixl 7 _∘ˢ_

    _∘ˢ_ : ∀ {𝕄} {γ δ η} → (𝕄 ∥ δ →ˢ η) → (𝕄 ∥ γ →ˢ δ) → (𝕄 ∥ γ →ˢ η)
    (ξ ∘ˢ σ) x = [ ξ ]ˢ (σ x)

    -- sum of substitutions

    infixl 8 _⊕ˢ_

    _⊕ˢ_ : ∀ {𝕄} {γ δ η χ} → (𝕄 ∥ γ →ˢ δ) → (𝕄 ∥ η →ˢ χ) → (𝕄 ∥ γ ⊕ η →ˢ δ ⊕ χ)
    σ ⊕ˢ τ = [ inlˢ ∘ˢ σ , inrˢ ∘ˢ τ  ]ˢ

    -- composition of renaming and substitition

    infixr 7 _ʳ∘ˢ_

    _ʳ∘ˢ_ : ∀ {𝕄} {γ δ η} → (δ →ʳ η) → (𝕄 ∥ γ →ˢ δ) → (𝕄 ∥ γ →ˢ η)
    (ρ ʳ∘ˢ σ) x = [ ρ ]ʳ σ x

    infixl 7 _ˢ∘ʳ_

    _ˢ∘ʳ_ : ∀ {𝕄} {γ δ η} → (𝕄 ∥ δ →ˢ η) → (γ →ʳ δ) → (𝕄 ∥ γ →ˢ η)
    (σ ˢ∘ʳ ρ) x =  σ (ρ x)

    -- extension commutes with the composition of renaming and substitution

    ⇑ˢ-ˢ∘ʳ : ∀ {𝕄} {β γ δ η} {ρ : β →ʳ γ} {σ : 𝕄 ∥ γ →ˢ δ} → ⇑ˢ {η = η} (σ ˢ∘ʳ ρ) ≈ˢ ⇑ˢ σ ˢ∘ʳ ⇑ʳ ρ
    ⇑ˢ-ˢ∘ʳ (var-left x) = ≈-refl
    ⇑ˢ-ˢ∘ʳ (var-right y) = ≈-refl

    ⇑ˢ-ʳ∘ˢ : ∀ {𝕄} {β γ δ η} {σ : 𝕄 ∥ β →ˢ γ} {ρ : γ →ʳ δ} → ⇑ˢ {η = η} (ρ ʳ∘ˢ σ) ≈ˢ ⇑ʳ ρ ʳ∘ˢ ⇑ˢ σ
    ⇑ˢ-ʳ∘ˢ (var-left x) = ≈-trans (≈-trans (≈-sym ([∘]ʳ _)) ([]ʳ-resp-≡ʳ _ λ x → refl)) ([∘]ʳ _)
    ⇑ˢ-ʳ∘ˢ (var-right x) = ≈-refl

    -- action of a composition of a renaming and a substitition

    [ˢ∘ʳ]ˢ : ∀ {𝕄 cl} {γ δ η} → {σ : 𝕄 ∥ δ →ˢ η} → {ρ : γ →ʳ δ} (t : Expr cl 𝕄 γ) → [ σ ˢ∘ʳ ρ ]ˢ t  ≈ [ σ ]ˢ [ ρ ]ʳ t
    [ˢ∘ʳ]ˢ (expr-var x) = ≈-refl
    [ˢ∘ʳ]ˢ (expr-symb S es) = ≈-symb (λ i → ≈-trans ([]ˢ-resp-≈ˢ ⇑ˢ-ˢ∘ʳ (es i)) ([ˢ∘ʳ]ˢ (es i)))
    [ˢ∘ʳ]ˢ (expr-meta M ts) = ≈-meta (λ i → [ˢ∘ʳ]ˢ (ts i))
    [ˢ∘ʳ]ˢ expr-eqty = ≈-eqty
    [ˢ∘ʳ]ˢ expr-eqtm = ≈-eqtm

    [ʳ∘ˢ]ˢ : ∀ {𝕄 cl} {γ δ η} → {σ : 𝕄 ∥ γ →ˢ δ} → {ρ : δ →ʳ η} (t : Expr cl 𝕄 γ) → [ ρ ʳ∘ˢ σ ]ˢ t ≈ [ ρ ]ʳ ([ σ ]ˢ  t)
    [ʳ∘ˢ]ˢ (expr-var x) = ≈-refl
    [ʳ∘ˢ]ˢ (expr-symb S es) = ≈-symb (λ i → ≈-trans ([]ˢ-resp-≈ˢ ⇑ˢ-ʳ∘ˢ (es i)) ([ʳ∘ˢ]ˢ (es i)))
    [ʳ∘ˢ]ˢ (expr-meta M ts) = ≈-meta (λ i → [ʳ∘ˢ]ˢ (ts i))
    [ʳ∘ˢ]ˢ expr-eqty = ≈-eqty
    [ʳ∘ˢ]ˢ expr-eqtm = ≈-eqtm

    -- composition commutes with extensions

    ⇑ˢ-∘ˢ : ∀ {𝕄} {β γ δ η} {σ : 𝕄 ∥ β →ˢ γ} {τ : 𝕄 ∥ γ →ˢ δ} → ⇑ˢ {η = η} (τ ∘ˢ σ) ≈ˢ ⇑ˢ τ ∘ˢ ⇑ˢ σ
    ⇑ˢ-∘ˢ {σ = σ} (var-left x) = ≈-trans (≈-trans (≈-sym ([ʳ∘ˢ]ˢ (σ x))) ([]ˢ-resp-≈ˢ (λ x₁ → ≈-refl) (σ x))) ([ˢ∘ʳ]ˢ (σ x))
    ⇑ˢ-∘ˢ (var-right y) = ≈-refl

    -- action of substitutions is functorial

    [𝟙]ˢ : ∀ {cl 𝕄 γ} (t : Expr cl 𝕄 γ) → [ 𝟙ˢ ]ˢ t ≈ t
    [𝟙]ˢ (expr-var x) = ≈-refl
    [𝟙]ˢ (expr-symb S es) = ≈-symb (λ i → ≈-trans ([]ˢ-resp-≈ˢ ⇑ˢ-𝟙ˢ (es i)) ([𝟙]ˢ (es i)))
    [𝟙]ˢ (expr-meta M ts) = ≈-meta (λ i → [𝟙]ˢ (ts i))
    [𝟙]ˢ expr-eqty = ≈-eqty
    [𝟙]ˢ expr-eqtm = ≈-eqtm

    [∘]ˢ : ∀ {cl 𝕄} {γ δ η} {σ : 𝕄 ∥ γ →ˢ δ} {τ : 𝕄 ∥ δ →ˢ η} (t : Expr cl 𝕄 γ) → [ τ ∘ˢ σ ]ˢ t ≈ [ τ ]ˢ [ σ ]ˢ t
    [∘]ˢ (expr-var x) = ≈-refl
    [∘]ˢ (expr-symb S es) = ≈-symb (λ i → ≈-trans ([]ˢ-resp-≈ˢ ⇑ˢ-∘ˢ (es i)) ([∘]ˢ (es i)))
    [∘]ˢ (expr-meta M ts) = ≈-meta (λ i → [∘]ˢ (ts i))
    [∘]ˢ expr-eqty = ≈-eqty
    [∘]ˢ expr-eqtm = ≈-eqtm

    []ˢ-id : ∀ {cl 𝕄 γ} {σ : 𝕄 ∥ γ →ˢ γ} {t : Expr cl 𝕄 γ} → σ ≈ˢ 𝟙ˢ → [ σ ]ˢ t ≈ t
    []ˢ-id {t = t} ξ = ≈-trans ([]ˢ-resp-≈ˢ ξ t) ([𝟙]ˢ t)

  open Core public

  -- Notations

  infix 5 _%[_]ˢ_
  _%[_]ˢ_ : ∀ (𝕊 : SymbolSignature) {cl 𝕄 γ δ} → 𝕄 ∥ γ →ˢ δ → Expression.Expr 𝕊 cl 𝕄 γ → Expression.Expr 𝕊 cl 𝕄 δ
  _%[_]ˢ_ 𝕊 = Core.[_]ˢ_ {𝕊 = 𝕊}

  infix 5 _%_∥_→ˢ_
  _%_∥_→ˢ_ : ∀ (𝕊 : SymbolSignature) → MShape → VShape → VShape → Set
  _%_∥_→ˢ_ 𝕊 = _∥_→ˢ_ {𝕊 = 𝕊}
