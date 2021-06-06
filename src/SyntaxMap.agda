open import Level
import Categories.Category
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)

open import Syntax
open import Renaming
open import Substitution
open import Instantiation

module SyntaxMap where

  open SymbolSignature
  open Expression
  open Equality

  infix 5 _→ᵐ_

  -- syntax map

  _→ᵐ_ : SymbolSignature → SymbolSignature → Set
  𝕊 →ᵐ 𝕋 = ∀ {cl} (S : symb 𝕊 cl) → Expr 𝕋 (obj cl) (symb-arg 𝕊 S)  𝟘

  -- equality of syntax maps

  infix 4 _≈ᵐ_

  _≈ᵐ_ : ∀ {𝕊 𝕋} (f g : 𝕊 →ᵐ 𝕋) → Set
  _≈ᵐ_ {𝕊 = 𝕊} {𝕋 = 𝕋} f g =
    ∀ {cl} (S : symb 𝕊 cl) → 𝕋 % f S ≈ g S

  -- equality is an equivalence relation

  ≈ᵐ-refl : ∀ {𝕊 𝕋} {f : 𝕊 →ᵐ 𝕋} → f ≈ᵐ f
  ≈ᵐ-refl {𝕋 = 𝕋} S = Equality.≈-refl 𝕋

  ≈ᵐ-sym : ∀ {𝕊 𝕋} {f g : 𝕊 →ᵐ 𝕋} → f ≈ᵐ g → g ≈ᵐ f
  ≈ᵐ-sym {𝕋 = 𝕋} ξ S = Equality.≈-sym 𝕋 (ξ S)

  ≈ᵐ-trans : ∀ {𝕊 𝕋} {f g h : 𝕊 →ᵐ 𝕋} → f ≈ᵐ g → g ≈ᵐ h → f ≈ᵐ h
  ≈ᵐ-trans {𝕋 = 𝕋} ζ ξ S = Equality.≈-trans 𝕋 (ζ S) (ξ S)

  -- The identity raw syntax map

  𝟙ᵐ : ∀ {𝕊} → (𝕊 →ᵐ 𝕊)
  𝟙ᵐ {𝕊} S = expr-symb S (expr-meta-generic 𝕊)

  -- Action of a raw syntax map

  infixr 10 [_]ᵐ_

  [_]ᵐ_ : ∀ {𝕊 𝕋} → (𝕊 →ᵐ 𝕋) → ∀ {cl 𝕄 γ} → Expr 𝕊 𝕄 cl γ → Expr 𝕋 𝕄 cl γ
  [ f ]ᵐ (expr-var x) = expr-var x
  [_]ᵐ_ {𝕋 = 𝕋} f {𝕄 = 𝕄} (expr-symb S es) =
        𝕋 %[ (λ M → [ f ]ᵐ es M) ]ⁱ (𝕋 %[ Core.𝟘-initial 𝕋 ]ʳ f S)
  [ f ]ᵐ (expr-meta M ts) = expr-meta M (λ i → [ f ]ᵐ (ts i))
  [ f ]ᵐ expr-eqty = expr-eqty
  [ f ]ᵐ expr-eqtm = expr-eqtm

  -- Composition of raw syntax maps

  infixl 7 _∘ᵐ_

  _∘ᵐ_ : ∀ {𝕊 𝕋 𝕌} → (𝕋 →ᵐ 𝕌) → (𝕊 →ᵐ 𝕋) → (𝕊 →ᵐ 𝕌)
  (g ∘ᵐ f) S =  [ g ]ᵐ (f S)

  -- Action preserves identity
  module _ {𝕊} where
    open Equality
    open Renaming.Core 𝕊
    open Substitution.Core 𝕊
    open Instantiation.Core 𝕊

    [𝟙]ᵐ : ∀ {cl 𝕄 γ} (t : Expr 𝕊 cl 𝕄 γ) → 𝕊 % [ 𝟙ᵐ ]ᵐ t ≈ t
    [𝟙]ᵐ (expr-var x) = Equality.≈-refl 𝕊
    [𝟙]ᵐ (expr-symb S es) =
      ≈-symb (λ {cⁱ γⁱ} i → [𝟙]ᵐ-arg cⁱ γⁱ i)
        where [𝟙]ᵐ-arg : ∀ cⁱ γⁱ (i : [ cⁱ , γⁱ ]∈ symb-arg 𝕊 S) → _
              [𝟙]ᵐ-arg (obj x) γⁱ i =
                ≈-trans
                  ([]ˢ-resp-≈ _ _ ([]ʳ-resp-≈ _ ([𝟙]ᵐ (es i))))
                  (≈-trans (≈-sym ([ˢ∘ʳ]ˢ (es i))) ([]ˢ-id (λ { (var-left _) → ≈-refl ; (var-right _) → ≈-refl })))
              [𝟙]ᵐ-arg EqTy γⁱ i = ≈-eqty
              [𝟙]ᵐ-arg EqTm γⁱ i = ≈-eqtm
    [𝟙]ᵐ (expr-meta M ts) = ≈-meta λ i → [𝟙]ᵐ (ts i)
    [𝟙]ᵐ expr-eqty = ≈-eqty
    [𝟙]ᵐ expr-eqtm = ≈-eqtm

  -- Action preserves composition
  module _ {𝕊 𝕋 𝕌} where
    open Equality

    [∘]ᵐ : ∀ {f : 𝕊 →ᵐ 𝕋} {g : 𝕋 →ᵐ 𝕌} {cl 𝕄 γ} (t : Expr 𝕊 𝕄 cl γ) → 𝕌 % [ g ∘ᵐ f ]ᵐ t ≈ [ g ]ᵐ [ f ]ᵐ t
    [∘]ᵐ (expr-var x) = Equality.≈-refl 𝕌
    [∘]ᵐ (expr-symb S es) = {!!}
    [∘]ᵐ (expr-meta M ts) = ≈-meta (λ i → [∘]ᵐ (ts i))
    [∘]ᵐ expr-eqty = Equality.≈-eqty 𝕌
    [∘]ᵐ expr-eqtm = Equality.≈-eqtm 𝕌

  -- Associativity of composition

  assocᵐ : ∀ {𝕊 𝕋 𝕌 𝕍} {f : 𝕊 →ᵐ 𝕋} {g : 𝕋 →ᵐ 𝕌} {h : 𝕌 →ᵐ 𝕍} →
           (h ∘ᵐ g) ∘ᵐ f ≈ᵐ h ∘ᵐ (g ∘ᵐ f)
  assocᵐ {f = f} S = [∘]ᵐ (f S)

  -- The category of signatures and syntax maps

  module _ where

   open Categories.Category

   SyntaxMaps : Category (suc zero) zero zero
   SyntaxMaps =
     record
       { Obj = SymbolSignature
       ; _⇒_ = _→ᵐ_
       ; _≈_ = _≈ᵐ_
       ; id = 𝟙ᵐ
       ; _∘_ = _∘ᵐ_
       ; assoc = λ {_} {_} {_} {_} {f} {_} {_} {_} S → [∘]ᵐ (f S)
       ; sym-assoc = λ {_} {_} {_} {𝕍} {f} {_} {_} {_} S → Equality.≈-sym 𝕍 ([∘]ᵐ (f S))
       ; identityˡ = λ S → [𝟙]ᵐ _
       ; identityʳ = λ {𝕊} {𝕋} {f} {cl} S → {!!}
       ; identity² = λ S → [𝟙]ᵐ _
       ; equiv = record { refl = λ {f} {cl} S → Equality.≈-refl _ ; sym = ≈ᵐ-sym ; trans = ≈ᵐ-trans }
       ; ∘-resp-≈ = {!!}
       }
