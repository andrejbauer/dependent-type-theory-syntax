open import Level
import Categories.Category
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)

open import Syntax
import Renaming
import Substitution
import Instantiation

module SyntaxMap where

  open SymbolSignature
  open Expression

  infix 5 _→ᵐ_

  -- syntax map

  _→ᵐ_ : SymbolSignature → SymbolSignature → Set
  𝕊 →ᵐ 𝕋 = ∀ {cl} (S : symb 𝕊 cl) → Expr 𝕋 (obj cl) (symb-arg 𝕊 S)  𝟘

  -- equality of syntax maps

  infix 4 _≈ᵐ_

  _≈ᵐ_ : ∀ {𝕊 𝕋} (f g : 𝕊 →ᵐ 𝕋) → Set
  _≈ᵐ_ {𝕊 = 𝕊} {𝕋 = 𝕋} f g =
    ∀ {cl} (S : symb 𝕊 cl) → Equality._≈_ 𝕋 (f S) (g S)

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
    let open Instantiation 𝕋 in
    let open Renaming 𝕋 in
        [ (λ M →  [ f ]ᵐ es M) ]ⁱ ([ 𝟘-initial ]ʳ f S)
  [ f ]ᵐ (expr-meta M ts) = expr-meta M (λ i → [ f ]ᵐ (ts i))
  [ f ]ᵐ expr-eqty = expr-eqty
  [ f ]ᵐ expr-eqtm = expr-eqtm

  -- Composition of raw syntax maps

  infixl 7 _∘ᵐ_

  _∘ᵐ_ : ∀ {𝕊 𝕋 𝕌} → (𝕋 →ᵐ 𝕌) → (𝕊 →ᵐ 𝕋) → (𝕊 →ᵐ 𝕌)
  (g ∘ᵐ f) S =  [ g ]ᵐ (f S)

  -- Action preserves identity
  module _ {𝕊} where
    open Equality 𝕊
    open Renaming 𝕊
    open Instantiation 𝕊

    [𝟙]ᵐ : ∀ {cl 𝕄 γ} (t : Expr 𝕊 cl 𝕄 γ) → [ 𝟙ᵐ ]ᵐ t ≈ t
    [𝟙]ᵐ (expr-var x) = ≈-refl
    [𝟙]ᵐ (expr-symb S es) = ≈-symb (λ i → {!!})
    [𝟙]ᵐ (expr-meta M ts) = ≈-meta λ i → [𝟙]ᵐ (ts i)
    [𝟙]ᵐ expr-eqty = ≈-eqty
    [𝟙]ᵐ expr-eqtm = ≈-eqtm

  -- Action preserves composition
  module _ {𝕊 𝕋 𝕌} where
    open Equality 𝕌

    [∘]ᵐ : ∀ {f : 𝕊 →ᵐ 𝕋} {g : 𝕋 →ᵐ 𝕌} {cl 𝕄 γ} (t : Expr 𝕊 𝕄 cl γ) → [ g ∘ᵐ f ]ᵐ t ≈ [ g ]ᵐ [ f ]ᵐ t
    [∘]ᵐ (expr-var x) = ≈-refl
    [∘]ᵐ (expr-symb S es) = {!!}
    [∘]ᵐ (expr-meta M ts) = ≈-meta (λ i → [∘]ᵐ (ts i))
    [∘]ᵐ expr-eqty = ≈-eqty
    [∘]ᵐ expr-eqtm = ≈-eqtm

  -- Associativity of composition

  assocᵐ : ∀ {𝕊 𝕋 𝕌 𝕍} {f : 𝕊 →ᵐ 𝕋} {g : 𝕋 →ᵐ 𝕌} {h : 𝕌 →ᵐ 𝕍} →
           (h ∘ᵐ g) ∘ᵐ f ≈ᵐ h ∘ᵐ (g ∘ᵐ f)
  assocᵐ {f = f} S = [∘]ᵐ (f S)

  -- The category of signatures and syntax maps

  module _ where

   open Categories.Category

   SyntaxMaps : Category (suc zero) {!!} {!!}
   SyntaxMaps =
     record
       { Obj = SymbolSignature
       ; _⇒_ = _→ᵐ_
       ; _≈_ = _≈ᵐ_
       ; id = 𝟙ᵐ
       ; _∘_ = _∘ᵐ_
       ; assoc = λ {_} {_} {_} {_} {f} {_} {_} {_} S → [∘]ᵐ (f S)
       ; sym-assoc = λ {_} {_} {_} {𝕍} {f} {_} {_} {_} S → Equality.≈-sym 𝕍 ([∘]ᵐ (f S))
       ; identityˡ = λ S → {!!}
       ; identityʳ = {!!}
       ; identity² = {!!}
       ; equiv = record { refl = ≈ᵐ-refl ; sym = ≈ᵐ-sym ; trans = ≈ᵐ-trans }
       ; ∘-resp-≈ = {!!}
       }
