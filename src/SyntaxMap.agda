open import Syntax
import Renaming
import Substitution
import Instantiation

module SyntaxMap where

  open SymbolSignature
  open Expression

  infix 5 _→ᴹ_

  _→ᴹ_ : SymbolSignature → SymbolSignature → Set
  Σ →ᴹ Ψ = ∀ {cl} (S : sym Σ cl) → ExprObj Ψ (sym-shape Σ S) cl 𝟘

  -- The identity raw syntax map
  𝟙ᴹ : ∀ {Σ} → (Σ →ᴹ Σ)
  𝟙ᴹ {Σ} S = expr-symb S (generic-meta Σ (sym-shape Σ S))

  -- Action of a raw syntax map

  infix 10 [_]ᴹ_

  [_]ᴹ_ : ∀ {Σ Ψ} → (Σ →ᴹ Ψ) → ∀ {cl 𝕄 γ} → Expr Σ 𝕄 cl γ → Expr Ψ 𝕄 cl γ
  [ f ]ᴹ (expr-var x) = expr-var x
  [_]ᴹ_ {Ψ = Ψ} f {𝕄 = 𝕄} (expr-symb S es) =
    let open Instantiation Ψ in
    let open Renaming Ψ 𝕄 in
       [ 𝟘-neutral-lr ]ʳ ([ (λ M → [ f ]ᴹ (es M)) ]ⁱ f S)
  [ f ]ᴹ (expr-meta M ts) = expr-meta M (λ i → [ f ]ᴹ (ts i))
  [ f ]ᴹ expr-eqty = expr-eqty
  [ f ]ᴹ expr-eqtm = expr-eqtm

  -- Composition of raw syntax maps

  infixl 7 _∘ᴹ_

  _∘ᴹ_ : ∀ {Σ Ψ Ω} → (Ψ →ᴹ Ω) → (Σ →ᴹ Ψ) → (Σ →ᴹ Ω)
  (g ∘ᴹ f) S =  [ g ]ᴹ (f S)
