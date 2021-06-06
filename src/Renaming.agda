open import Level
open import Relation.Binary.PropositionalEquality

import Categories.Category

open import Syntax

module Renaming where

  open Equality

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

  -- 𝟘 is the weakly initial shape

  𝟘-initial : ∀ {γ} → 𝟘 →ʳ γ
  𝟘-initial ()

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

  -- renaming extension
  ⇑ʳ : ∀ {γ δ η} → (γ →ʳ δ) → (γ ⊕ η →ʳ δ ⊕ η)
  ⇑ʳ ρ (var-left x) =  var-left (ρ x)
  ⇑ʳ ρ (var-right y) = var-right y

  -- extension preserves equality

  ⇑ʳ-resp-≡ʳ : ∀ {γ δ η} {ρ τ : γ →ʳ δ} → ρ ≡ʳ τ → ⇑ʳ {η = η} ρ ≡ʳ ⇑ʳ τ
  ⇑ʳ-resp-≡ʳ ξ (var-left x) = cong var-left (ξ x)
  ⇑ʳ-resp-≡ʳ ξ (var-right y) = refl

  -- extension respects identity

  ⇑ʳ-resp-𝟙ʳ : ∀ {γ δ} → ⇑ʳ {η = δ} (𝟙ʳ {γ = γ})  ≡ʳ 𝟙ʳ
  ⇑ʳ-resp-𝟙ʳ (var-left x) = refl
  ⇑ʳ-resp-𝟙ʳ (var-right x) = refl

  -- extension commutes with composition

  ⇑ʳ-resp-∘ʳ : ∀ {β γ δ η} {ρ : β →ʳ γ} {τ : γ →ʳ δ} → ⇑ʳ {η = η} (τ ∘ʳ ρ) ≡ʳ ⇑ʳ τ ∘ʳ ⇑ʳ ρ
  ⇑ʳ-resp-∘ʳ (var-left x) = refl
  ⇑ʳ-resp-∘ʳ (var-right y) = refl

  module _ {𝕊 : Signature} where
    open Expression 𝕊

    -- the action of a renaming on an expression

    infixr 6 [_]ʳ_

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
    []ʳ-resp-≡ʳ (expr-symb S es) ξ = ≈-symb (λ i → []ʳ-resp-≡ʳ (es i) (⇑ʳ-resp-≡ʳ ξ))
    []ʳ-resp-≡ʳ (expr-meta M ts) ξ = ≈-meta (λ i → []ʳ-resp-≡ʳ (ts i) ξ)
    []ʳ-resp-≡ʳ expr-eqty ξ = ≈-eqty
    []ʳ-resp-≡ʳ expr-eqtm ξ = ≈-eqtm

    -- the action is functorial

    [𝟙ʳ] : ∀ {cl 𝕄 γ} {t : Expr cl 𝕄 γ} → [ 𝟙ʳ ]ʳ t ≈ t
    [𝟙ʳ] {t = expr-var x} = ≈-refl
    [𝟙ʳ] {t = expr-symb S es} = ≈-symb (λ i → ≈-trans ([]ʳ-resp-≡ʳ (es i) ⇑ʳ-resp-𝟙ʳ) [𝟙ʳ])
    [𝟙ʳ] {t = expr-meta M ts} = ≈-meta (λ i → [𝟙ʳ])
    [𝟙ʳ] {t = expr-eqty} = ≈-eqty
    [𝟙ʳ] {t = expr-eqtm} = ≈-eqtm

    [∘ʳ] : ∀ {cl 𝕄} {γ δ η} {ρ : γ →ʳ δ} {τ : δ →ʳ η} (t : Expr cl 𝕄 γ) → [ τ ∘ʳ ρ ]ʳ t ≈ [ τ ]ʳ [ ρ ]ʳ t
    [∘ʳ] (expr-var x) = ≈-refl
    [∘ʳ] (expr-symb S es) = ≈-symb (λ i → ≈-trans ([]ʳ-resp-≡ʳ (es i) ⇑ʳ-resp-∘ʳ) ([∘ʳ] (es i)))
    [∘ʳ] (expr-meta M ts) = ≈-meta (λ i → [∘ʳ] (ts i))
    [∘ʳ] expr-eqty = ≈-eqty
    [∘ʳ] expr-eqtm = ≈-eqtm

    []ʳ-id : ∀ {cl 𝕄 γ} {ρ : γ →ʳ γ} {t : Expr cl 𝕄 γ} → ρ ≡ʳ 𝟙ʳ → [ ρ ]ʳ t ≈ t
    []ʳ-id ξ = ≈-trans ([]ʳ-resp-≡ʳ _ ξ) [𝟙ʳ]

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
