open import Level
import Categories.Category
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)

open import Syntax
open import Renaming
open import Substitution
open import Instantiation

module SyntaxMap where

  open Signature
  open Expression
  open Equality

  infix 5 _→ᵐ_

  -- syntax map

  _→ᵐ_ : Signature → Signature → Set
  𝕊 →ᵐ 𝕋 = ∀ {cl} (S : symb 𝕊 cl) → Expr 𝕋 (obj cl) (symb-arg 𝕊 S) 𝟘

  -- equality of syntax maps

  infix 4 _≈ᵐ_

  _≈ᵐ_ : ∀ {𝕊 𝕋} (f g : 𝕊 →ᵐ 𝕋) → Set
  _≈ᵐ_ {𝕊 = 𝕊} {𝕋 = 𝕋} f g =
    ∀ {cl} (S : symb 𝕊 cl) → f S ≈ g S

  -- equality is an equivalence relation

  ≈ᵐ-refl : ∀ {𝕊 𝕋} {f : 𝕊 →ᵐ 𝕋} → f ≈ᵐ f
  ≈ᵐ-refl {𝕋 = 𝕋} S = ≈-refl

  ≈ᵐ-sym : ∀ {𝕊 𝕋} {f g : 𝕊 →ᵐ 𝕋} → f ≈ᵐ g → g ≈ᵐ f
  ≈ᵐ-sym {𝕋 = 𝕋} ξ S = ≈-sym (ξ S)

  ≈ᵐ-trans : ∀ {𝕊 𝕋} {f g h : 𝕊 →ᵐ 𝕋} → f ≈ᵐ g → g ≈ᵐ h → f ≈ᵐ h
  ≈ᵐ-trans {𝕋 = 𝕋} ζ ξ S = ≈-trans (ζ S) (ξ S)

  -- The identity raw syntax map

  𝟙ᵐ : ∀ {𝕊} → (𝕊 →ᵐ 𝕊)
  𝟙ᵐ {𝕊} S = expr-symb S (expr-meta-generic 𝕊)

  -- Action of a raw syntax map

  infixr 10 [_]ᵐ_

  [_]ᵐ_ : ∀ {𝕊 𝕋} → (𝕊 →ᵐ 𝕋) → ∀ {cl 𝕄 γ} → Expr 𝕊 𝕄 cl γ → Expr 𝕋 𝕄 cl γ
  [ f ]ᵐ (expr-var x) = expr-var x
  [_]ᵐ_ {𝕋 = 𝕋} f {𝕄 = 𝕄} (expr-symb S es) =
    𝕋 %[ (λ M → [ f ]ᵐ es M) ]ⁱ (𝕋 %[ 𝟘-initial ]ʳ f S)
  [ f ]ᵐ (expr-meta M ts) = expr-meta M (λ i → [ f ]ᵐ (ts i))
  [ f ]ᵐ expr-eqty = expr-eqty
  [ f ]ᵐ expr-eqtm = expr-eqtm

  -- Action preserves equality

  []ᵐ-resp-≈ : ∀ {𝕊 𝕋} {cl 𝕄 γ} (f : 𝕊 →ᵐ 𝕋) {t u : Expr 𝕊 𝕄 cl γ} →
               t ≈ u → [ f ]ᵐ t ≈ [ f ]ᵐ u
  []ᵐ-resp-≈ f (≈-≡ ξ) = ≈-≡ (cong ([ f ]ᵐ_) ξ)
  []ᵐ-resp-≈ {𝕋 = 𝕋} f (≈-symb {S = S} ξ) =
    []ⁱ-resp-≈ⁱ (𝕋 %[ 𝟘-initial ]ʳ f S) λ M → []ᵐ-resp-≈ f (ξ M)
  []ᵐ-resp-≈ f (≈-meta ξ) = ≈-meta (λ i → []ᵐ-resp-≈ f (ξ i))

  []ᵐ-resp-≈ᵐ : ∀ {𝕊 𝕋} {cl 𝕄 γ} {f g : 𝕊 →ᵐ 𝕋} (t : Expr 𝕊 𝕄 cl γ) →
               f ≈ᵐ g → [ f ]ᵐ t ≈ [ g ]ᵐ t
  []ᵐ-resp-≈ᵐ (expr-var x) ξ = ≈-refl
  []ᵐ-resp-≈ᵐ {f = f} {g = g} (expr-symb S es) ξ =
     []ⁱ-resp-≈ⁱ-≈ {I = λ M → [ f ]ᵐ es M} {J = λ M → [ g ]ᵐ es M}
       (λ M → []ᵐ-resp-≈ᵐ (es M) ξ)
       ([]ʳ-resp-≈ 𝟘-initial (ξ S))
  []ᵐ-resp-≈ᵐ (expr-meta M ts) ξ = ≈-meta (λ i → []ᵐ-resp-≈ᵐ (ts i) ξ)
  []ᵐ-resp-≈ᵐ expr-eqty ξ = ≈-eqty
  []ᵐ-resp-≈ᵐ expr-eqtm ξ = ≈-eqtm

  []ᵐ-resp-≈ᵐ-≈ : ∀ {𝕊 𝕋} {cl 𝕄 γ} {f g : 𝕊 →ᵐ 𝕋} {t u : Expr 𝕊 𝕄 cl γ} →
                  f ≈ᵐ g → t ≈ u → [ f ]ᵐ t ≈ [ g ]ᵐ u
  []ᵐ-resp-≈ᵐ-≈ {g = g} {t = t} ζ ξ = ≈-trans ([]ᵐ-resp-≈ᵐ t ζ) ([]ᵐ-resp-≈ g ξ)

  -- Composition of raw syntax maps

  infixl 7 _∘ᵐ_

  _∘ᵐ_ : ∀ {𝕊 𝕋 𝕌} → (𝕋 →ᵐ 𝕌) → (𝕊 →ᵐ 𝕋) → (𝕊 →ᵐ 𝕌)
  (g ∘ᵐ f) S =  [ g ]ᵐ (f S)

  -- Action preserves identity
  module _ {𝕊} where
    open Equality
    open Renaming
    open Substitution

    [𝟙]ᵐ : ∀ {cl 𝕄 γ} (t : Expr 𝕊 cl 𝕄 γ) → 𝕊 % [ 𝟙ᵐ ]ᵐ t ≈ t
    [𝟙]ᵐ (expr-var x) = ≈-refl
    [𝟙]ᵐ (expr-symb S es) =
      ≈-symb (λ {cⁱ γⁱ} i → [𝟙]ᵐ-arg cⁱ γⁱ i)
        where [𝟙]ᵐ-arg : ∀ cⁱ γⁱ (i : [ cⁱ , γⁱ ]∈ symb-arg 𝕊 S) → _
              [𝟙]ᵐ-arg (obj x) γⁱ i =
                ≈-trans
                  ([]ˢ-resp-≈ _ ([]ʳ-resp-≈ _ ([𝟙]ᵐ (es i))))
                  (≈-trans (≈-sym ([ˢ∘ʳ]ˢ (es i))) ([]ˢ-id (λ { (var-left _) → ≈-refl ; (var-right _) → ≈-refl })))
              [𝟙]ᵐ-arg EqTy γⁱ i = ≈-eqty
              [𝟙]ᵐ-arg EqTm γⁱ i = ≈-eqtm
    [𝟙]ᵐ (expr-meta M ts) = ≈-meta λ i → [𝟙]ᵐ (ts i)
    [𝟙]ᵐ expr-eqty = ≈-eqty
    [𝟙]ᵐ expr-eqtm = ≈-eqtm

  -- interaction of maps with instantiation and substitution
  module _ {𝕊 𝕋} where
    open Substitution

    infixl 7 _ᵐ∘ˢ_
    _ᵐ∘ˢ_ : ∀ {𝕊 𝕋} {𝕄 γ δ} (f : 𝕊 →ᵐ 𝕋) (σ : 𝕊 % 𝕄 ∥ γ →ˢ δ) → (𝕋 % 𝕄 ∥ γ →ˢ δ)
    (f ᵐ∘ˢ σ) x = [ f ]ᵐ σ x

    []ᵐ-[]ʳ : ∀ {f : 𝕊 →ᵐ 𝕋} {cl 𝕄 γ δ} {ρ : γ →ʳ δ} (t : Expr 𝕊 cl 𝕄 γ) →
              ([ f ]ᵐ ([ ρ ]ʳ t)) ≈ ([ ρ ]ʳ [ f ]ᵐ t)
    []ᵐ-[]ʳ (expr-var x) = ≈-refl
    []ᵐ-[]ʳ {f = f} {ρ = ρ} (expr-symb S es) =
      ≈-trans
        ([]ⁱ-resp-≈ⁱ ([ 𝟘-initial ]ʳ f S) λ M → []ᵐ-[]ʳ (es M))
        (≈-trans
           ([]ⁱ-resp-≈ⁱ-≈
              {t = [ 𝟘-initial ]ʳ f S}
              {u = [ ρ ]ʳ (𝕋 %[ 𝟘-initial ]ʳ f S)}
              (λ M → ≈-refl)
              (≈-trans ([]ʳ-resp-≡ʳ (f S) (λ {()})) ([∘ʳ] (f S))))
           (≈-sym ([ʳ∘ⁱ]ⁱ (𝕋 %[ 𝟘-initial ]ʳ f S))))
    []ᵐ-[]ʳ (expr-meta M ts) = ≈-meta (λ i → []ᵐ-[]ʳ (ts i))
    []ᵐ-[]ʳ expr-eqty = ≈-eqty
    []ᵐ-[]ʳ expr-eqtm = ≈-eqtm

    []ᵐ-[]ˢ : ∀ {cl 𝕄 γ δ} {f : 𝕊 →ᵐ 𝕋} {σ : 𝕊 % 𝕄 ∥ γ →ˢ δ} (t : Expr 𝕊 cl 𝕄 γ) →
              [ f ]ᵐ ([ σ ]ˢ t) ≈ [ f ᵐ∘ˢ σ ]ˢ [ f ]ᵐ t
    []ᵐ-[]ˢ (expr-var x) = ≈-refl
    []ᵐ-[]ˢ {f = f} {σ = σ} (expr-symb S es) =
      ≈-trans
        ([]ⁱ-resp-≈ⁱ ([ 𝟘-initial ]ʳ f S) (λ M → []ᵐ-[]ˢ (es M)))
        (≈-trans
           ([]ⁱ-resp-≈ⁱ
              ([ 𝟘-initial ]ʳ f S)
              (λ M → []ˢ-resp-≈ˢ
                       (λ { (var-left x) → []ᵐ-[]ʳ (σ x)
                          ; (var-right _) → ≈-refl})
                       ([ f ]ᵐ es M)))
           (≈-sym ([]ˢ-[]ⁱ {ρ = 𝟘-initial} (f S) λ {()})))
    []ᵐ-[]ˢ (expr-meta M ts) = ≈-meta (λ i → []ᵐ-[]ˢ (ts i))
    []ᵐ-[]ˢ expr-eqty = ≈-eqty
    []ᵐ-[]ˢ expr-eqtm = ≈-eqtm

    infixl 7 _ᵐ∘ⁱ_
    _ᵐ∘ⁱ_ : ∀ {𝕂 𝕄 γ} (f : 𝕊 →ᵐ 𝕋) (I : 𝕊 % 𝕂 →ⁱ 𝕄 ∥ γ) → 𝕋 % 𝕂 →ⁱ 𝕄 ∥ γ
    (f ᵐ∘ⁱ I) M =  [ f ]ᵐ I M

    ⇑ⁱ-resp-ᵐ∘ⁱ : ∀ {𝕂 𝕄 γ δ} {f : 𝕊 →ᵐ 𝕋} {I : 𝕊 % 𝕂 →ⁱ 𝕄 ∥ γ} →
                  ⇑ⁱ {δ = δ} (f ᵐ∘ⁱ I) ≈ⁱ f ᵐ∘ⁱ ⇑ⁱ I
    ⇑ⁱ-resp-ᵐ∘ⁱ {I = I} M = ≈-sym ([]ᵐ-[]ʳ (I M))

    []ᵐ-[]ⁱ : ∀ {cl 𝕂 𝕄 γ} {f : 𝕊 →ᵐ 𝕋} {I : 𝕊 % 𝕂 →ⁱ 𝕄 ∥ γ} (t : Expr 𝕊 cl 𝕂 γ) →
              [ f ]ᵐ (𝕊 %[ I ]ⁱ t) ≈ 𝕋 %[ f ᵐ∘ⁱ I ]ⁱ [ f ]ᵐ t
    []ᵐ-[]ⁱ (expr-var x) = ≈-refl
    []ᵐ-[]ⁱ {f = f} {I = I} (expr-symb S es) =
      ≈-trans
        ([]ⁱ-resp-≈ⁱ
           (𝕋 %[ 𝟘-initial ]ʳ f S)
           λ M → ≈-trans
                   ([]ᵐ-[]ⁱ (es M))
                   ([]ⁱ-resp-≈ⁱ ([ f ]ᵐ es M) (≈ⁱ-sym (⇑ⁱ-resp-ᵐ∘ⁱ {I = I}))))
        ([∘]ⁱ (𝕋 %[ 𝟘-initial ]ʳ f S))
    []ᵐ-[]ⁱ {f = f} {I = I} (expr-meta M ts) =
      ≈-trans
        ([]ᵐ-[]ˢ (I M))
        ([]ˢ-resp-≈ˢ (λ { (var-left _) → ≈-refl ; (var-right x) → []ᵐ-[]ⁱ (ts x)}) ([ f ]ᵐ I M))
    []ᵐ-[]ⁱ expr-eqty = ≈-eqty
    []ᵐ-[]ⁱ expr-eqtm = ≈-eqtm

  -- idenity is right-neutral

  []ᵐ-meta-generic : ∀ {𝕊 𝕋} {𝕄 γ} {f : 𝕊 →ᵐ 𝕋} {clᴹ γᴹ} {M : [ clᴹ , γᴹ ]∈ 𝕄} →
                     [ f ]ᵐ (expr-meta-generic 𝕊 {γ = γ} M) ≈ expr-meta-generic 𝕋 M
  []ᵐ-meta-generic {clᴹ = obj _} = ≈-refl
  []ᵐ-meta-generic {clᴹ = EqTy} = ≈-eqty
  []ᵐ-meta-generic {clᴹ = EqTm} = ≈-eqtm

  𝟙ᵐ-right : ∀ {𝕊 𝕋} {f : 𝕊 →ᵐ 𝕋} → f ∘ᵐ 𝟙ᵐ ≈ᵐ f
  𝟙ᵐ-right {f = f} S =
    ≈-trans
      ([]ⁱ-resp-≈ⁱ ([ 𝟘-initial ]ʳ (f S)) λ M → []ᵐ-meta-generic {M = M})
      (≈-trans ([𝟙]ⁱ ([ 𝟘-initial ]ʳ f S)) ([]ʳ-id (λ { ()})))

  -- Action preserves composition

  module _ {𝕊 𝕋 𝕌} where
    [∘]ᵐ : ∀ {f : 𝕊 →ᵐ 𝕋} {g : 𝕋 →ᵐ 𝕌} {cl 𝕄 γ} (t : Expr 𝕊 cl 𝕄 γ) → 𝕌 % [ g ∘ᵐ f ]ᵐ t ≈ [ g ]ᵐ [ f ]ᵐ t
    [∘]ᵐ (expr-var x) = ≈-refl
    [∘]ᵐ {f = f} {g = g} (expr-symb S es) =
      ≈-trans
        ([]ⁱ-resp-≈ⁱ-≈ (λ M → [∘]ᵐ (es M)) (≈-sym ([]ᵐ-[]ʳ (f S))))
        (≈-sym ([]ᵐ-[]ⁱ (𝕋 %[ 𝟘-initial ]ʳ f S)))
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

   SyntaxMaps : Category (suc zero) zero zero
   SyntaxMaps =
     record
       { Obj = Signature
       ; _⇒_ = _→ᵐ_
       ; _≈_ = _≈ᵐ_
       ; id = 𝟙ᵐ
       ; _∘_ = _∘ᵐ_
       ; assoc = λ {_} {_} {_} {_} {f} {_} {_} {_} S → [∘]ᵐ (f S)
       ; sym-assoc = λ {_} {_} {_} {𝕍} {f} {_} {_} {_} S → ≈-sym ([∘]ᵐ (f S))
       ; identityˡ = λ S → [𝟙]ᵐ _
       ; identityʳ = λ {_} {_} {f} {_} → 𝟙ᵐ-right {f = f}
       ; identity² = λ _ → [𝟙]ᵐ _
       ; equiv = record { refl = λ _ → ≈-refl ; sym = ≈ᵐ-sym ; trans = ≈ᵐ-trans }
       ; ∘-resp-≈ = λ ζ ξ S → []ᵐ-resp-≈ᵐ-≈ ζ (ξ S)
       }
