open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)

open import Syntax
import Renaming
import Substitution

module Instantiation where
  -- Instantiations
  module Core (𝕊 : SymbolSignature) where

    open Expression 𝕊
    open Substitution.Core 𝕊
    open Renaming.Core 𝕊
    open Equality 𝕊

    -- the set of instantiations

    infix 5 _→ⁱ_∥_

    _→ⁱ_∥_ : MShape → MShape → VShape → Set
    𝕄 →ⁱ 𝕂 ∥ γ = ∀ {clᴹ γᴹ} (M : [ clᴹ , γᴹ ]∈ 𝕄) → Arg clᴹ 𝕂 γ γᴹ

    -- equality of instantiations

    infix 4 _≈ⁱ_

    _≈ⁱ_ : ∀ {𝕂 𝕄} {γ} (I J : 𝕂 →ⁱ 𝕄 ∥ γ) → Set
    I ≈ⁱ J = ∀ {clᴹ γᴹ} (M : [ clᴹ , γᴹ ]∈ _) → I M ≈ J M

    ≈ⁱ-sym : ∀ {𝕂 𝕄} {γ} {I J : 𝕂 →ⁱ 𝕄 ∥ γ} → I ≈ⁱ J → J ≈ⁱ I
    ≈ⁱ-sym ξ M = ≈-sym (ξ M)

    -- identity instantiation
    𝟙ⁱ : ∀ {𝕄 γ δ} → 𝕄 →ⁱ 𝕄 ∥ γ ⊕ δ
    𝟙ⁱ M = expr-meta-generic M

    -- instantiation extension

    ⇑ⁱ : ∀ {𝕂 𝕄 γ δ} → 𝕂 →ⁱ 𝕄 ∥ γ → 𝕂 →ⁱ 𝕄 ∥ γ ⊕ δ
    ⇑ⁱ I M = [ (⇑ʳ var-left) ]ʳ (I M)

    -- extension respects equality

    ⇑ⁱ-resp-≈ⁱ : ∀ {𝕂 𝕄} {γ δ} → {I J : 𝕂 →ⁱ 𝕄 ∥ γ} → I ≈ⁱ J → ⇑ⁱ {δ = δ} I ≈ⁱ ⇑ⁱ J
    ⇑ⁱ-resp-≈ⁱ ξ M = []ʳ-resp-≈ (⇑ʳ var-left) (ξ M)

    -- the action of an instantiation on an expression

    infix 6 [_]ⁱ_

    [_]ⁱ_ : ∀ {cl 𝕂 𝕄} {γ} → (𝕂 →ⁱ 𝕄 ∥ γ) → Expr cl 𝕂 γ → Expr cl 𝕄 γ
    [ I ]ⁱ (expr-var x) = expr-var x
    [ I ]ⁱ (expr-symb S es) = expr-symb S (λ i → [ ⇑ⁱ I ]ⁱ es i)
    [ I ]ⁱ (expr-meta M ts) = [ [ 𝟙ˢ , (λ i → [ I ]ⁱ ts i) ]ˢ ]ˢ I M
    [ I ]ⁱ expr-eqty = expr-eqty
    [ I ]ⁱ expr-eqtm = expr-eqtm

    -- instantiations respects equality

    []ⁱ-resp-≈ : ∀ {cl} {𝕂 𝕄} {γ} (I : 𝕂 →ⁱ 𝕄 ∥ γ) {t u : Expr cl 𝕂 γ} → t ≈ u → [ I ]ⁱ t ≈ [ I ]ⁱ u
    []ⁱ-resp-≈ I (≈-≡ ξ) = ≈-≡ (cong [ I ]ⁱ_ ξ)
    []ⁱ-resp-≈ I (≈-symb ξ) = ≈-symb (λ i → []ⁱ-resp-≈ (⇑ⁱ I) (ξ i))
    []ⁱ-resp-≈ I (≈-meta ξ) = []ˢ-resp-≈ˢ ([,]ˢ-resp-≈ˢ ≈ˢ-refl (λ i → []ⁱ-resp-≈ I (ξ i))) (I _)

    []ⁱ-resp-≈ⁱ : ∀ {cl} {𝕂 𝕄} {γ} {I J : 𝕂 →ⁱ 𝕄 ∥ γ} (t : Expr cl 𝕂 γ) → I ≈ⁱ J → [ I ]ⁱ t ≈ [ J ]ⁱ t
    []ⁱ-resp-≈ⁱ (expr-var x) ξ = ≈-refl
    []ⁱ-resp-≈ⁱ (expr-symb S es) ξ = ≈-symb (λ i → []ⁱ-resp-≈ⁱ (es i) (⇑ⁱ-resp-≈ⁱ ξ))
    []ⁱ-resp-≈ⁱ (expr-meta M ts) ξ = []ˢ-resp-≈ˢ-≈ ([,]ˢ-resp-≈ˢ ≈ˢ-refl (λ i → []ⁱ-resp-≈ⁱ (ts i) ξ)) (ξ M)
    []ⁱ-resp-≈ⁱ expr-eqty ξ = ≈-eqty
    []ⁱ-resp-≈ⁱ expr-eqtm ξ = ≈-eqtm

    -- composition of instantiations

    infixl 7 _∘ⁱ_

    _∘ⁱ_ : ∀ {𝕂 𝕃 𝕄} {γ} → 𝕃 →ⁱ 𝕄 ∥ γ → 𝕂 →ⁱ 𝕃 ∥ γ → 𝕂 →ⁱ 𝕄 ∥ γ
    (J ∘ⁱ I) M = [ ⇑ⁱ J ]ⁱ I M

    -- composition of a renaming and instantiation

    infixr 7 _ʳ∘ⁱ_

    _ʳ∘ⁱ_ : ∀ {𝕂 𝕄} {γ δ} → (ρ : γ →ʳ δ) → (I : 𝕂 →ⁱ 𝕄 ∥ γ) → 𝕂 →ⁱ 𝕄 ∥ δ
    (ρ ʳ∘ⁱ I) M =  [ ⇑ʳ ρ ]ʳ I M

    ⇑ⁱ-resp-ʳ∘ⁱ : ∀ {𝕂 𝕄} {γ δ η} {ρ : γ →ʳ δ} → {I : 𝕂 →ⁱ 𝕄 ∥ γ} →
                  ⇑ⁱ {δ = η} (ρ ʳ∘ⁱ I) ≈ⁱ ⇑ʳ ρ ʳ∘ⁱ ⇑ⁱ I
    ⇑ⁱ-resp-ʳ∘ⁱ {I = I} M =
      ≈-trans
        (≈-trans
          (≈-sym ([∘]ʳ (I M)))
          ([]ʳ-resp-≡ʳ (I M) (λ {(var-left x) → refl ; (var-right y) → refl})))
        ([∘]ʳ (I M))

    [ʳ∘ⁱ]ⁱ : ∀ {cl 𝕂 𝕄} {γ δ} {ρ : γ →ʳ δ} {I : 𝕂 →ⁱ 𝕄 ∥ γ} (t : Expr cl 𝕂 γ) →
             [ ρ ]ʳ ([ I ]ⁱ t) ≈ [ ρ ʳ∘ⁱ I ]ⁱ [ ρ ]ʳ t
    [ʳ∘ⁱ]ⁱ (expr-var x) = ≈-refl
    [ʳ∘ⁱ]ⁱ {ρ = ρ} {I = I} (expr-symb S es) =
      ≈-symb (λ i → ≈-trans
                     ([ʳ∘ⁱ]ⁱ (es i))
                     ([]ⁱ-resp-≈ⁱ
                        ([ ⇑ʳ ρ ]ʳ es i)
                        (≈ⁱ-sym (⇑ⁱ-resp-ʳ∘ⁱ {I = I}))))
    [ʳ∘ⁱ]ⁱ {ρ = ρ} {I = I} (expr-meta M ts) =
      ≈-trans
        (≈-sym ([ʳ∘ˢ]ˢ (I M)))
        (≈-trans
          ([]ˢ-resp-≈ˢ (λ { (var-left x) → ≈-refl ; (var-right y) →  [ʳ∘ⁱ]ⁱ (ts y)}) (I M))
          ([ˢ∘ʳ]ˢ (I M)))
    [ʳ∘ⁱ]ⁱ expr-eqty = ≈-eqty
    [ʳ∘ⁱ]ⁱ expr-eqtm = ≈-eqtm

    -- composition of an instantiation and substitution

    infixr 7 _ⁱ∘ˢ_

    _ⁱ∘ˢ_ : ∀ {𝕂 𝕄} {γ δ} (I : 𝕂 →ⁱ 𝕄 ∥ δ) (σ : 𝕂 ∥ γ →ˢ δ) → (𝕄 ∥ γ →ˢ δ)
    (I ⁱ∘ˢ σ) x = [ I ]ⁱ σ x

    -- [ⁱ∘ˢ]ⁱ : ∀ {cl} {𝕂 𝕄} {γ δ} {σ : 𝕄 ∥ γ →ˢ δ} {I : 𝕂 →ⁱ 𝕄 ∥ γ} (t : Expr cl 𝕂 γ) →
    --          [ σ ⁱ∘ˢ I ]ⁱ {!!} ≈ [ σ ]ˢ [ I ]ⁱ t
    -- [ⁱ∘ˢ]ⁱ t = {!!}

    -- extension respects identity

    ⇑ⁱ-resp-𝟙ⁱ : ∀ {𝕄 γ δ η} → ⇑ⁱ {δ = η} 𝟙ⁱ ≈ⁱ 𝟙ⁱ {𝕄 = 𝕄} {γ = γ ⊕ δ}
    ⇑ⁱ-resp-𝟙ⁱ {clᴹ = obj _} M = ≈-refl
    ⇑ⁱ-resp-𝟙ⁱ {clᴹ = EqTy} M = ≈-eqty
    ⇑ⁱ-resp-𝟙ⁱ {clᴹ = EqTm} M = ≈-eqtm

    -- extension respects composition

    ⇑ⁱ-resp-∘ⁱ : ∀ {𝕂 𝕃 𝕄 γ δ} {I : 𝕂 →ⁱ 𝕃 ∥ γ} {J : 𝕃 →ⁱ 𝕄 ∥ γ} → ⇑ⁱ {δ = δ} (J ∘ⁱ I) ≈ⁱ ⇑ⁱ J ∘ⁱ ⇑ⁱ I
    ⇑ⁱ-resp-∘ⁱ {I = I} {J = J} M =
      ≈-trans
        ([ʳ∘ⁱ]ⁱ (I M))
        ([]ⁱ-resp-≈ⁱ ([ ⇑ʳ var-left ]ʳ I M)
          λ N → ≈-trans (≈-sym ([∘]ʳ (J N)))
                  (≈-trans ([]ʳ-resp-≡ʳ (J N)  λ {(var-left x) → refl ; (var-right y) → refl}) ([∘]ʳ (J N))))

    ⇑ⁱ-resp-ⁱ∘ˢ : ∀ {𝕂 𝕄} {γ δ η} {I : 𝕂 →ⁱ 𝕄 ∥ δ} {σ : 𝕂 ∥ γ →ˢ δ} →
                  ⇑ˢ {η = η} (I ⁱ∘ˢ σ ) ≈ˢ ⇑ⁱ I ⁱ∘ˢ ⇑ˢ σ
    ⇑ⁱ-resp-ⁱ∘ˢ {σ = σ}(var-left x) = ≈-trans ([ʳ∘ⁱ]ⁱ (σ x)) ([]ⁱ-resp-≈ⁱ ([ var-left ]ʳ σ x) (λ _ → ≈-refl))
    ⇑ⁱ-resp-ⁱ∘ˢ (var-right y) = ≈-refl


    -- the action of an instantiation on a generic metavariable application

    []ⁱ-meta-generic : ∀ {𝕂 𝕄} {γ} {I : 𝕂 →ⁱ 𝕄 ∥ γ} {clᴹ γᴹ} {M : [ clᴹ , γᴹ ]∈ 𝕂} → [ ⇑ⁱ I ]ⁱ (expr-meta-generic {γ = γ} M) ≈ I M
    []ⁱ-meta-generic {I = I} {clᴹ = obj _} {M = M} =
      ≈-trans (≈-sym ([ˢ∘ʳ]ˢ (I M))) ([]ˢ-id (λ { (var-left _) → ≈-refl ; (var-right _) → ≈-refl}))
    []ⁱ-meta-generic {clᴹ = EqTy} = ≈-eqty
    []ⁱ-meta-generic {clᴹ = EqTm} = ≈-eqtm

    -- action of the identity

    [𝟙]ⁱ : ∀ {cl 𝕄 γ δ} (t : Expr cl 𝕄 (γ ⊕ δ)) → [ 𝟙ⁱ ]ⁱ t ≈ t
    [𝟙]ⁱ (expr-var x) = ≈-refl
    [𝟙]ⁱ (expr-symb S es) = ≈-symb (λ i → ≈-trans ([]ⁱ-resp-≈ⁱ (es i) ⇑ⁱ-resp-𝟙ⁱ) ([𝟙]ⁱ (es i)))
    [𝟙]ⁱ (expr-meta M ts) = ≈-meta (λ i → [𝟙]ⁱ (ts i))
    [𝟙]ⁱ (expr-eqty) = ≈-eqty
    [𝟙]ⁱ (expr-eqtm) = ≈-eqtm

    -- interaction of instantiation, substitution and renaming

    []ⁱ-[]ˢ : ∀ {cl 𝕂 𝕄 γ δ} {I : 𝕂 →ⁱ 𝕄 ∥ δ} {σ : 𝕂 ∥ γ →ˢ δ} {ρ : δ →ʳ γ} (t : Expr cl 𝕂 γ) →
          σ ˢ∘ʳ ρ ≈ˢ 𝟙ˢ → ([ I ]ⁱ ([ σ ]ˢ t)) ≈ ([ I ⁱ∘ˢ σ ]ˢ [ ρ ʳ∘ⁱ I ]ⁱ t)
    []ⁱ-[]ˢ (expr-var x) ξ = ≈-refl
    []ⁱ-[]ˢ {I = I} {σ = σ} {ρ = ρ} (expr-symb S es) ξ =
      ≈-symb (λ i →
        ≈-trans
          ([]ⁱ-[]ˢ {ρ = ⇑ʳ ρ} (es i)
            λ where
              (var-left x) → []ʳ-resp-≈ var-left (ξ x)
              (var-right x) → ≈-refl)
          (≈-sym ([]ˢ-resp-≈ˢ-≈ (⇑ⁱ-resp-ⁱ∘ˢ) (([]ⁱ-resp-≈ⁱ (es i) (⇑ⁱ-resp-ʳ∘ⁱ {I = I}))))))
    []ⁱ-[]ˢ {I = I} {σ = σ} (expr-meta M ts) ξ =
      ≈-trans
        (≈-trans
          ([]ˢ-resp-≈ˢ (λ where
                          (var-left x) → ≈-sym ([]ⁱ-resp-≈ I (ξ x))
                          (var-right x) → []ⁱ-[]ˢ (ts x) ξ)
                       (I M))
          ([∘]ˢ (I M)))
        (≈-sym ([]ˢ-resp-≈ (I ⁱ∘ˢ σ) (≈-sym ([ˢ∘ʳ]ˢ (I M))) ))
    []ⁱ-[]ˢ expr-eqty _ = ≈-eqty
    []ⁱ-[]ˢ expr-eqtm _ = ≈-eqtm

    -- action of composition

    [∘]ⁱ : ∀ {cl 𝕂 𝕃 𝕄 γ} {I : 𝕂 →ⁱ 𝕃 ∥ γ} {J : 𝕃 →ⁱ 𝕄 ∥ γ} (t : Expr cl 𝕂 γ) → [ J ∘ⁱ I ]ⁱ t ≈ [ J ]ⁱ [ I ]ⁱ t
    [∘]ⁱ (expr-var _) = ≈-refl
    [∘]ⁱ {I = I} {J = J} (expr-symb S es) =
      ≈-symb (λ i → ≈-trans ([]ⁱ-resp-≈ⁱ (es i) (⇑ⁱ-resp-∘ⁱ {I = I})) ([∘]ⁱ (es i)))
    [∘]ⁱ {I = I} {J = J} (expr-meta M ts) =
      ≈-sym (≈-trans
               ([]ⁱ-[]ˢ {I = J} {ρ = var-left} (I M) λ _ → ≈-refl)
               ([]ˢ-resp-≈ˢ
                 (λ { (var-left x) → ≈-refl ; (var-right x) → ≈-sym ([∘]ⁱ (ts x))})
                 ([ ⇑ⁱ J ]ⁱ (I M))))
    [∘]ⁱ expr-eqty = ≈-eqty
    [∘]ⁱ expr-eqtm = ≈-eqtm


  -- Notation for working with multiple signatures
  infix 5 _%_→ⁱ_∥_
  _%_→ⁱ_∥_ = Core._→ⁱ_∥_

  infix 6 _%[_]ⁱ_
  _%[_]ⁱ_ = Core.[_]ⁱ_

  infix 4 _%_≈ⁱ_
  _%_≈ⁱ_ = Core._≈ⁱ_
