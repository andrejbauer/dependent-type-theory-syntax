open import Level
open import Relation.Binary.PropositionalEquality

import Categories.Category

open import Syntax

module Renaming where

  module Core (𝕊 : SymbolSignature) where
    open Equality 𝕊

    -- the set of renamings

    infix 5 _→ʳ_

    _→ʳ_ : VShape → VShape → Set
    γ →ʳ δ = var γ → var δ

    -- equality of renamings

    infix 5 _≡ʳ_

    _≡ʳ_ : ∀ {γ δ} → (ρ : γ →ʳ δ) → (t : γ →ʳ δ) → Set
    ρ ≡ʳ σ = ∀ x → ρ x ≡ σ x

    -- equality is an equivalence relation

    ≡ʳ-refl : ∀ {γ δ} → {ρ : γ →ʳ δ} → ρ ≡ʳ ρ
    ≡ʳ-refl x = refl

    ≡ʳ-sym : ∀ {γ δ} → {ρ τ : γ →ʳ δ} → ρ ≡ʳ τ → τ ≡ʳ ρ
    ≡ʳ-sym ξ x = sym (ξ x)

    ≡ʳ-trans : ∀ {γ δ} → {ρ τ χ : γ →ʳ δ} → ρ ≡ʳ τ → τ ≡ʳ χ → ρ ≡ʳ χ
    ≡ʳ-trans ζ ξ x = trans (ζ x) (ξ x)

    -- identity renaming

    𝟙ʳ : ∀ {γ} → γ →ʳ γ
    𝟙ʳ x = x

    -- composition of renamings

    infixl 7 _∘ʳ_

    _∘ʳ_ : ∀ {γ δ η} → (δ →ʳ η) → (γ →ʳ δ) → (γ →ʳ η)
    (ρ ∘ʳ τ) x =  ρ (τ x)

    -- join of renamings
    infix 6 [_,_]ʳ

    [_,_]ʳ : ∀ {γ δ η} → (γ →ʳ η) → (δ →ʳ η) → (γ ⊕ δ →ʳ η)
    [ ρ , τ ]ʳ (var-left x) = ρ x
    [ ρ , τ ]ʳ (var-right y) = τ y

    infix 6 _+ʳ_

    -- sum of renamings

    _+ʳ_ : ∀ {γ δ η θ} → (γ →ʳ η) → (δ →ʳ θ) → (γ ⊕ δ →ʳ η ⊕ θ)
    (ρ +ʳ τ) (var-left x) = var-left (ρ x)
    (ρ +ʳ τ) (var-right y) = var-right (τ y)

    -- renaming extension
    ⇑ʳ : ∀ {γ δ η} → (γ →ʳ δ) → (γ ⊕ η →ʳ δ ⊕ η)
    ⇑ʳ ρ = ρ +ʳ 𝟙ʳ

    -- a sum of idenities is an identity

    𝟙ʳ+𝟙ʳ : ∀ {γ δ} → 𝟙ʳ +ʳ 𝟙ʳ ≡ʳ 𝟙ʳ {γ = γ ⊕ δ}
    𝟙ʳ+𝟙ʳ (var-left x) = refl
    𝟙ʳ+𝟙ʳ (var-right x) = refl

    -- extension commutes with composition

    ⇑ʳ-∘ʳ : ∀ {β γ δ η} {ρ : β →ʳ γ} {τ : γ →ʳ δ} → ⇑ʳ {η = η} (τ ∘ʳ ρ) ≡ʳ ⇑ʳ τ ∘ʳ ⇑ʳ ρ
    ⇑ʳ-∘ʳ (var-left x) = refl
    ⇑ʳ-∘ʳ (var-right y) = refl

    -- sum preserves equality

    ≡ʳ-+ʳ : ∀ {γ δ η θ} {ρ₁ ρ₂ : γ →ʳ η} → {τ₁ τ₂ : δ →ʳ θ} →
            ρ₁ ≡ʳ ρ₂ → τ₁ ≡ʳ τ₂ → ρ₁ +ʳ τ₁ ≡ʳ ρ₂ +ʳ τ₂
    ≡ʳ-+ʳ ζ ξ (var-left x) = cong var-left (ζ x)
    ≡ʳ-+ʳ ζ ξ (var-right x) = cong var-right (ξ x)

    -- the action of a renaming on an expression
    infix 6 [_]ʳ_

    open Expression 𝕊

    [_]ʳ_ : ∀ {𝕄} {cl} {γ} {δ} (ρ : γ →ʳ δ) → Expr 𝕄 cl γ → Expr 𝕄 cl δ
    [ ρ ]ʳ (expr-var x) = expr-var (ρ x)
    [ ρ ]ʳ (expr-symb S es) = expr-symb S (λ i → [ ⇑ʳ ρ ]ʳ (es i))
    [ ρ ]ʳ (expr-meta M ts) = expr-meta M (λ i → [ ρ ]ʳ (ts i))
    [ ρ ]ʳ expr-eqty = expr-eqty
    [ ρ ]ʳ expr-eqtm = expr-eqtm

    -- the action respects equality of renamings and equality of terms

    []ʳ-resp-≈ : ∀ {𝕄} {cl} {γ} {δ} (ρ : γ →ʳ δ) {t u : Expr 𝕄 cl γ} → t ≈ u → [ ρ ]ʳ t ≈ [ ρ ]ʳ u
    []ʳ-resp-≈ ρ (≈-≡ ξ) = ≈-≡ (cong [ ρ ]ʳ_ ξ)
    []ʳ-resp-≈ ρ (≈-symb ξ) = ≈-symb (λ i → []ʳ-resp-≈ (⇑ʳ ρ) (ξ i))
    []ʳ-resp-≈ ρ (≈-meta ξ) = ≈-meta (λ i → []ʳ-resp-≈ ρ (ξ i))

    []ʳ-resp-≡ʳ : ∀ {𝕄} {cl} {γ} {δ} {ρ τ : γ →ʳ δ} (t : Expr cl 𝕄 γ) → ρ ≡ʳ τ → [ ρ ]ʳ t ≈ [ τ ]ʳ t
    []ʳ-resp-≡ʳ (expr-var x) ξ = ≈-≡ (cong expr-var (ξ x))
    []ʳ-resp-≡ʳ (expr-symb S es) ξ = ≈-symb (λ i → []ʳ-resp-≡ʳ (es i) (≡ʳ-+ʳ ξ ≡ʳ-refl))
    []ʳ-resp-≡ʳ (expr-meta M ts) ξ = ≈-meta (λ i → []ʳ-resp-≡ʳ (ts i) ξ)
    []ʳ-resp-≡ʳ expr-eqty ξ = ≈-eqty
    []ʳ-resp-≡ʳ expr-eqtm ξ = ≈-eqtm

    -- the action is functorial

    [𝟙]ʳ : ∀ {cl 𝕄 γ} {t : Expr cl 𝕄 γ} → [ 𝟙ʳ ]ʳ t ≈ t
    [𝟙]ʳ {t = expr-var x} = ≈-refl
    [𝟙]ʳ {t = expr-symb S es} = ≈-symb (λ i → ≈-trans ([]ʳ-resp-≡ʳ (es i) 𝟙ʳ+𝟙ʳ) [𝟙]ʳ)
    [𝟙]ʳ {t = expr-meta M ts} = ≈-meta (λ i → [𝟙]ʳ)
    [𝟙]ʳ {t = expr-eqty} = ≈-eqty
    [𝟙]ʳ {t = expr-eqtm} = ≈-eqtm

    [∘]ʳ : ∀ {cl 𝕄} {γ δ η} {ρ : γ →ʳ δ} {τ : δ →ʳ η} (t : Expr cl 𝕄 γ) → [ τ ∘ʳ ρ ]ʳ t ≈ [ τ ]ʳ [ ρ ]ʳ t
    [∘]ʳ (expr-var x) = ≈-refl
    [∘]ʳ (expr-symb S es) = ≈-symb (λ i → ≈-trans ([]ʳ-resp-≡ʳ (es i) ⇑ʳ-∘ʳ) ([∘]ʳ (es i)))
    [∘]ʳ (expr-meta M ts) = ≈-meta (λ i → [∘]ʳ (ts i))
    [∘]ʳ expr-eqty = ≈-eqty
    [∘]ʳ expr-eqtm = ≈-eqtm

    []ʳ-id : ∀ {cl 𝕄 γ} {ρ : γ →ʳ γ} {t : Expr cl 𝕄 γ} → ρ ≡ʳ 𝟙ʳ → [ ρ ]ʳ t ≈ t
    []ʳ-id ξ = ≈-trans ([]ʳ-resp-≡ʳ _ ξ) [𝟙]ʳ

    -- re-associatiate the shape

    assocˡ : ∀ {γ δ η} → (γ ⊕ δ) ⊕ η →ʳ γ ⊕ (δ ⊕ η)
    assocˡ (var-left (var-left x)) = var-left x
    assocˡ (var-left (var-right y)) = var-right (var-left y)
    assocˡ (var-right z) = var-right (var-right z)

    assocʳ : ∀ {γ δ η} → γ ⊕ (δ ⊕ η) →ʳ (γ ⊕ δ) ⊕ η
    assocʳ (var-left x) = var-left (var-left x)
    assocʳ (var-right (var-left y)) = var-left (var-right y)
    assocʳ (var-right (var-right z)) = var-right z

    -- 𝟘 is neutral in various ways

    𝟘-initial : ∀ {γ} → 𝟘 →ʳ γ
    𝟘-initial ()

    𝟘-neutral-lr : ∀ {γ} → γ ⊕ 𝟘 →ʳ γ
    𝟘-neutral-lr (var-left x) = x

    𝟘-neutral-rl : ∀ {γ} → γ →ʳ 𝟘 ⊕ γ
    𝟘-neutral-rl x = var-right x

    -- the categorical structure

    module _ where
      open Categories.Category

      Renamings : Category zero zero zero
      Renamings =
        record
          { Obj = VShape
          ; _⇒_ = _→ʳ_
          ; _≈_ = _≡ʳ_
          ; id = 𝟙ʳ
          ; _∘_ = _∘ʳ_
          ; assoc = λ _ → refl
          ; sym-assoc = λ _ → refl
          ; identityˡ = λ _ → refl
          ; identityʳ = λ _ → refl
          ; identity² = λ _ → refl
          ; equiv = record { refl = ≡ʳ-refl ; sym = ≡ʳ-sym ; trans = ≡ʳ-trans }
          ; ∘-resp-≈ = λ {_} {_} {_} {ρ} {_} {_} {τ} ζ ξ x → trans (cong ρ (ξ x)) (ζ (τ x))
          }

  -- Notation for working with renamings & multiple signatures
  infix 5 _%_→ʳ_
  _%_→ʳ_ = Core._→ʳ_

  infix 5 _%_≡ʳ_
  _%_≡ʳ_ = Core._≡ʳ_

  infix 6 _%[_]ʳ_
  _%[_]ʳ_ = Core.[_]ʳ_
