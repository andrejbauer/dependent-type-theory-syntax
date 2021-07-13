open import Agda.Primitive using (lzero; lsuc; _⊔_; Level)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Relation.Binary using (Setoid)

-- A formalization of raw syntax

module Syntax where

  -- Syntactic classes

  data ObjectClass : Set where
    Ty Tm : ObjectClass

  data Class : Set where
    obj : ObjectClass → Class
    EqTy EqTm : Class

  -- Variable context shape

  infixl 6 _⊕_

  data VShape : Set where
    𝟘 : VShape
    𝟙 : VShape
    _⊕_ : VShape → VShape → VShape

  data var : VShape → Set where
    var-here : var 𝟙
    var-left : ∀ {γ δ} → var γ → var (γ ⊕ δ)
    var-right : ∀ {γ δ} → var δ → var (γ ⊕ δ)

  -- Metavariable context shapes

  infixl 9 _⊕ᵐᵛ_

  data MShape : Set where
    𝟘ᵐᵛ : MShape
    𝟙ᵐᵛ : ∀ (cl : Class) (γ : VShape) → MShape
    _⊕ᵐᵛ_ : MShape → MShape → MShape

  infix 8 [_,_]∈_

  data [_,_]∈_ : Class → VShape → MShape → Set where
    mv-here : ∀ cl γ → [ cl , γ ]∈ 𝟙ᵐᵛ cl γ
    mv-left : ∀ {𝕂 𝕄} cl γ → [ cl , γ ]∈ 𝕂 → [ cl , γ ]∈ 𝕂 ⊕ᵐᵛ 𝕄
    mv-right : ∀ {𝕂 𝕄} cl γ → [ cl , γ ]∈ 𝕄 → [ cl , γ ]∈ 𝕂 ⊕ᵐᵛ 𝕄

  -- Symbol signature

  record Signature : Set₁ where
    field
      symb : ObjectClass → Set -- a set of symbol names, one for each class
      symb-arg : ∀ {cl} → symb cl → MShape

  -- Expressions

  module Expression (𝕊 : Signature) where
    open Signature 𝕊

    data Expr : Class → (𝕄 : MShape) → (γ : VShape) → Set

    Arg : ∀ (cl : Class) (𝕄 : MShape) (γ : VShape) (δ : VShape) → Set
    Arg cl 𝕄 γ δ = Expr cl 𝕄 (γ ⊕ δ)

    ExprObj : ∀ (cl : ObjectClass) (𝕄 : MShape) (γ : VShape) → Set
    ExprObj cl = Expr (obj cl)

    ExprTm = ExprObj Tm
    ExprTy = ExprObj Ty

    data Expr where
      expr-var : ∀ {𝕄} {γ} (x : var γ) → ExprTm 𝕄 γ
      expr-symb : ∀ {cl 𝕄 γ} (S : symb cl) →
                    (es : ∀ {clⁱ γⁱ} (i : [ clⁱ , γⁱ ]∈ symb-arg S) → Arg clⁱ 𝕄 γ γⁱ) →
                    ExprObj cl 𝕄 γ
      expr-meta : ∀ {cl 𝕄 γ} {γᴹ} (M : [ obj cl , γᴹ ]∈ 𝕄) → (ts : ∀ (i : var γᴹ) → ExprTm 𝕄 γ) → ExprObj cl 𝕄 γ
      expr-eqty : ∀ {γ} {𝕄} → Expr EqTy 𝕄 γ
      expr-eqtm : ∀ {γ} {𝕄} → Expr EqTm 𝕄 γ

    expr-meta-generic : ∀ {𝕄} {cl} {γ γᴹ} (M : [ cl , γᴹ ]∈ 𝕄) → Arg cl 𝕄 γ γᴹ
    expr-meta-generic {cl = obj _} M = expr-meta M (λ i → expr-var (var-right i))
    expr-meta-generic {cl = EqTy} M = expr-eqty
    expr-meta-generic {cl = EqTm} M = expr-eqtm

  -- Syntactic equality

  module Equality {𝕊 : Signature} where

    open Signature 𝕊
    open Expression 𝕊

    infix 4 _≈_

    data _≈_ : ∀ {cl 𝕄 γ} → Expr cl 𝕄 γ → Expr cl 𝕄 γ → Set where
      ≈-≡ : ∀ {cl 𝕄 γ} {t u : Expr cl 𝕄 γ} (ξ : t ≡ u) → t ≈ u
      ≈-symb : ∀ {cl 𝕄 γ} {S : symb cl} →
                {ds es : ∀ {cⁱ γⁱ} (i : [ cⁱ , γⁱ ]∈ symb-arg S) → Arg cⁱ 𝕄 γ γⁱ}
                (ξ : ∀ {cⁱ γⁱ} (i : [ cⁱ , γⁱ ]∈ symb-arg S) → ds i ≈ es i) → expr-symb S ds ≈ expr-symb S es
      ≈-meta : ∀ {cl 𝕄 γ} {γᴹ} {M : [ obj cl , γᴹ ]∈ 𝕄} → {ts us : ∀ (i : var γᴹ) → ExprTm 𝕄 γ}
                (ξ : ∀ i → ts i ≈ us i) → expr-meta M ts ≈ expr-meta M us

    ≈-refl : ∀ {cl 𝕄 γ} {t : Expr cl 𝕄 γ} → t ≈ t
    ≈-refl = ≈-≡ refl

    ≈-eqty : ∀ {𝕄 γ} {s t : Expr EqTy 𝕄  γ} → s ≈ t
    ≈-eqty {s = expr-eqty} {t = expr-eqty} = ≈-refl

    ≈-eqtm : ∀ {𝕄 γ} {s t : Expr EqTm 𝕄 γ} → s ≈ t
    ≈-eqtm {s = expr-eqtm} {t = expr-eqtm} = ≈-refl

    ≈-sym : ∀ {cl 𝕄 γ} {t u : Expr cl 𝕄 γ} → t ≈ u → u ≈ t
    ≈-sym (≈-≡ refl) = ≈-≡ refl
    ≈-sym (≈-symb ε) = ≈-symb (λ i → ≈-sym (ε i))
    ≈-sym (≈-meta ε) = ≈-meta (λ i → ≈-sym (ε i))

    ≈-trans : ∀ {cl 𝕄 γ} {t u v : Expr cl 𝕄 γ} → t ≈ u → u ≈ v → t ≈ v
    ≈-trans (≈-≡ refl) ξ = ξ
    ≈-trans (≈-symb ζ) (≈-≡ refl) = ≈-symb ζ
    ≈-trans (≈-symb ζ) (≈-symb ξ) = ≈-symb (λ i → ≈-trans (ζ i) (ξ i))
    ≈-trans (≈-meta ζ) (≈-≡ refl) = ≈-meta ζ
    ≈-trans (≈-meta ζ) (≈-meta ξ) = ≈-meta (λ i → ≈-trans (ζ i) (ξ i))

    -- the setoid of expressions

    Expr-setoid : ∀ (cl : Class) (𝕄 : MShape) (γ : VShape) →  Setoid lzero lzero
    Expr-setoid cl 𝕄 γ =
      record
        { Carrier =  Expr cl 𝕄 γ
        ; _≈_ = _≈_
        ; isEquivalence = record { refl = ≈-refl ; sym = ≈-sym ; trans = ≈-trans }
        }

  infix 4 _%_≈_

  _%_≈_ : ∀ (𝕊 : Signature) {cl 𝕄 γ} → (t u : Expression.Expr 𝕊 cl 𝕄 γ) → Set
  _%_≈_ 𝕊 = Equality._≈_ {𝕊 = 𝕊}
