open import Relation.Binary.PropositionalEquality using (_â¡_; refl; sym; trans; subst; cong)

open import Syntax
import Renaming

-- Substitutions
module Substitution where

  module _ {ð : Signature} where

    open Expression ð
    open Renaming
    open Equality

    infix 5 _â¥_âË¢_

    -- the set of substitutions
    _â¥_âË¢_ : MShape â VShape â VShape â Set
    ð â¥ Î³ âË¢ Î´ = var Î³ â ExprTm ð Î´

    -- equality of substitutions

    infix 4 _âË¢_

    _âË¢_ : â {ð} {Î³ Î´} (Ï : ð â¥ Î³ âË¢ Î´) (Ï : ð â¥ Î³ âË¢ Î´) â Set
    Ï âË¢ Ï = â x â Ï x â Ï x

    -- equality is an equivalence relation

    âË¢-refl : â {ð} {Î³ Î´} {Ï : ð â¥ Î³ âË¢ Î´} â Ï âË¢ Ï
    âË¢-refl x = â-refl

    âË¢-sym : â {ð} {Î³ Î´} {Ï Ï : ð â¥ Î³ âË¢ Î´} â Ï âË¢ Ï â Ï âË¢ Ï
    âË¢-sym Î¾ x = â-sym (Î¾ x)

    âË¢-trans : â {ð} {Î³ Î´} {Ï Ï Ï : ð â¥ Î³ âË¢ Î´} â Ï âË¢ Ï â Ï âË¢ Ï â Ï âË¢ Ï
    âË¢-trans Î¶ Î¾ x = â-trans (Î¶ x) (Î¾ x)

    -- identity substitution
    ðË¢ : â {ð} {Î³} â ð â¥ Î³ âË¢ Î³
    ðË¢ = expr-var

    -- inclusions

    inlË¢ : â {ð} {Î³ Î´} â ð â¥ Î³ âË¢ Î³ â Î´
    inlË¢ x = expr-var (var-left x)

    inrË¢ : â {ð} {Î³ Î´} â ð â¥ Î´ âË¢ Î³ â Î´
    inrË¢ x = expr-var (var-right x)

    -- join of substitutions

    [_,_]Ë¢ : â {ð} {Î³ Î´ Î·} â (ð â¥ Î³ âË¢ Î·) â (ð â¥ Î´ âË¢ Î·) â (ð â¥ Î³ â Î´ âË¢ Î·)
    [ Î¾ , Ï ]Ë¢ (var-left x) = Î¾ x
    [ Î¾ , Ï ]Ë¢ (var-right y) = Ï y

    -- join respect equality

    [,]Ë¢-resp-âË¢ : â {ð} {Î³ Î´ Î·} {Ïâ Ïâ : ð â¥ Î³ âË¢ Î·} {Ïâ Ïâ : ð â¥ Î´ âË¢ Î·} â
                 Ïâ âË¢ Ïâ â Ïâ âË¢ Ïâ â [ Ïâ , Ïâ ]Ë¢ âË¢ [ Ïâ , Ïâ ]Ë¢
    [,]Ë¢-resp-âË¢ Î¶ Î¾ (var-left x) = Î¶ x
    [,]Ë¢-resp-âË¢ Î¶ Î¾ (var-right y) = Î¾ y

    -- substutution extension

    âË¢ : â {ð} {Î³ Î´ Î·} â (ð â¥ Î³ âË¢ Î´) â (ð â¥ Î³ â Î· âË¢ Î´ â Î·)
    âË¢ Ï (var-left x) = [ var-left ]Ê³ Ï x
    âË¢ Ï (var-right y) = expr-var (var-right y)

    -- extension preserves equality

    âË¢-resp-âË¢ : â {ð} {Î³ Î´ Î·} {Ï Ï : ð â¥ Î³ âË¢ Î´} â Ï âË¢ Ï â âË¢ {Î· = Î·} Ï âË¢ âË¢ Ï
    âË¢-resp-âË¢ Î¾ (var-left x) = []Ê³-resp-â var-left (Î¾ x)
    âË¢-resp-âË¢ Î¾ (var-right y) = â-refl

    -- extension preserves identity

    âË¢-ðË¢ : â {ð} {Î³ Î´} â âË¢ ðË¢ âË¢ ðË¢ {ð = ð} {Î³ = Î³ â Î´}
    âË¢-ðË¢ (var-left x) = â-refl
    âË¢-ðË¢ (var-right x) = â-refl

    -- action of a substitution

    infix 5 [_]Ë¢_

    [_]Ë¢_ : â {cl ð} {Î³ Î´} â (ð â¥ Î³ âË¢ Î´) â Expr cl ð Î³ â Expr cl ð Î´
    [ Ï ]Ë¢ (expr-var x) =  Ï x
    [ Ï ]Ë¢ (expr-symb S es) = expr-symb S (Î» i â [ âË¢ Ï ]Ë¢ es i)
    [ Ï ]Ë¢ (expr-meta M ts) = expr-meta M (Î» i â [ Ï ]Ë¢ ts i )
    [ Ï ]Ë¢ expr-eqty = expr-eqty
    [ Ï ]Ë¢ expr-eqtm = expr-eqtm

    -- the action respects equality

    []Ë¢-resp-â : â {cl ð} {Î³ Î´} (Ï : ð â¥ Î³ âË¢ Î´) {t u : Expr cl ð Î³} â t â u â [ Ï ]Ë¢ t â [ Ï ]Ë¢ u
    []Ë¢-resp-â Ï (â-â¡ Î¾) = â-â¡ (cong ([ Ï ]Ë¢_) Î¾)
    []Ë¢-resp-â Ï (â-symb Î¾) = â-symb (Î» i â []Ë¢-resp-â (âË¢ Ï) (Î¾ i))
    []Ë¢-resp-â Ï (â-meta Î¾) = â-meta (Î» i â []Ë¢-resp-â Ï (Î¾ i))

    []Ë¢-resp-âË¢ : â {cl ð} {Î³ Î´} {Ï Ï : ð â¥ Î³ âË¢ Î´} â Ï âË¢ Ï â â (t : Expr cl ð Î³) â [ Ï ]Ë¢ t â [ Ï ]Ë¢ t
    []Ë¢-resp-âË¢ Î¾ (expr-var x) = Î¾ x
    []Ë¢-resp-âË¢ Î¾ (expr-symb S es) = â-symb (Î» i â []Ë¢-resp-âË¢ (âË¢-resp-âË¢ Î¾) (es i))
    []Ë¢-resp-âË¢ Î¾ (expr-meta M ts) = â-meta (Î» i â []Ë¢-resp-âË¢ Î¾ (ts i))
    []Ë¢-resp-âË¢ Î¾ expr-eqty = â-eqty
    []Ë¢-resp-âË¢ Î¾ expr-eqtm = â-eqtm

    []Ë¢-resp-âË¢-â : â {cl ð} {Î³ Î´} {Ï Ï : ð â¥ Î³ âË¢ Î´} {t u : Expr cl ð Î³} â Ï âË¢ Ï â t â u â [ Ï ]Ë¢ t â [ Ï ]Ë¢ u
    []Ë¢-resp-âË¢-â {Ï = Ï} {t = t} Î¶ Î¾ = â-trans ([]Ë¢-resp-âË¢ Î¶ t) ([]Ë¢-resp-â Ï Î¾)

    -- composition of substitutions

    infixl 7 _âË¢_

    _âË¢_ : â {ð} {Î³ Î´ Î·} â (ð â¥ Î´ âË¢ Î·) â (ð â¥ Î³ âË¢ Î´) â (ð â¥ Î³ âË¢ Î·)
    (Î¾ âË¢ Ï) x = [ Î¾ ]Ë¢ (Ï x)

    -- sum of substitutions

    infixl 8 _âË¢_

    _âË¢_ : â {ð} {Î³ Î´ Î· Ï} â (ð â¥ Î³ âË¢ Î´) â (ð â¥ Î· âË¢ Ï) â (ð â¥ Î³ â Î· âË¢ Î´ â Ï)
    Ï âË¢ Ï = [ inlË¢ âË¢ Ï , inrË¢ âË¢ Ï  ]Ë¢

    -- composition of renaming and substitition

    infixr 7 _Ê³âË¢_

    _Ê³âË¢_ : â {ð} {Î³ Î´ Î·} â (Î´ âÊ³ Î·) â (ð â¥ Î³ âË¢ Î´) â (ð â¥ Î³ âË¢ Î·)
    (Ï Ê³âË¢ Ï) x = [ Ï ]Ê³ Ï x

    infixl 7 _Ë¢âÊ³_

    _Ë¢âÊ³_ : â {ð} {Î³ Î´ Î·} â (ð â¥ Î´ âË¢ Î·) â (Î³ âÊ³ Î´) â (ð â¥ Î³ âË¢ Î·)
    (Ï Ë¢âÊ³ Ï) x =  Ï (Ï x)

    -- extension commutes with the composition of renaming and substitution

    âË¢-resp-Ê³âË¢ : â {ð} {Î³ Î´ Î· Î¸} {Ï : Î´ âÊ³ Î·} â {Ï : ð â¥ Î³ âË¢ Î´} â
                  âË¢ {Î· = Î¸} (Ï Ê³âË¢ Ï) âË¢ âÊ³ Ï Ê³âË¢ âË¢ Ï
    âË¢-resp-Ê³âË¢ {Ï = Ï} (var-left x) =
      â-trans
        (â-sym ([âÊ³] (Ï x)))
        (â-trans
           ([]Ê³-resp-â¡Ê³ (Ï x) â¡Ê³-refl)
           ([âÊ³] (Ï x)))
    âË¢-resp-Ê³âË¢ (var-right y) = â-refl

    âË¢-resp-Ë¢âÊ³ : â {ð} {Î² Î³ Î´ Î·} {Ï : Î² âÊ³ Î³} {Ï : ð â¥ Î³ âË¢ Î´} â âË¢ {Î· = Î·} (Ï Ë¢âÊ³ Ï) âË¢ âË¢ Ï Ë¢âÊ³ âÊ³ Ï
    âË¢-resp-Ë¢âÊ³ (var-left x) = â-refl
    âË¢-resp-Ë¢âÊ³ (var-right y) = â-refl

    âË¢-Ê³âË¢ : â {ð} {Î² Î³ Î´ Î·} {Ï : ð â¥ Î² âË¢ Î³} {Ï : Î³ âÊ³ Î´} â âË¢ {Î· = Î·} (Ï Ê³âË¢ Ï) âË¢ âÊ³ Ï Ê³âË¢ âË¢ Ï
    âË¢-Ê³âË¢ (var-left x) = â-trans (â-trans (â-sym ([âÊ³] _)) ([]Ê³-resp-â¡Ê³ _ Î» x â refl)) ([âÊ³] _)
    âË¢-Ê³âË¢ (var-right x) = â-refl

    -- action of a composition of a renaming and a substitition

    [Ë¢âÊ³] : â {ð cl} {Î³ Î´ Î·} â {Ï : ð â¥ Î´ âË¢ Î·} â {Ï : Î³ âÊ³ Î´} (t : Expr cl ð Î³) â [ Ï Ë¢âÊ³ Ï ]Ë¢ t  â [ Ï ]Ë¢ [ Ï ]Ê³ t
    [Ë¢âÊ³] (expr-var x) = â-refl
    [Ë¢âÊ³] (expr-symb S es) = â-symb (Î» i â â-trans ([]Ë¢-resp-âË¢ âË¢-resp-Ë¢âÊ³ (es i)) ([Ë¢âÊ³] (es i)))
    [Ë¢âÊ³] (expr-meta M ts) = â-meta (Î» i â [Ë¢âÊ³] (ts i))
    [Ë¢âÊ³] expr-eqty = â-eqty
    [Ë¢âÊ³] expr-eqtm = â-eqtm

    [Ê³âË¢] : â {ð cl} {Î³ Î´ Î·} â {Ï : ð â¥ Î³ âË¢ Î´} â {Ï : Î´ âÊ³ Î·} (t : Expr cl ð Î³) â [ Ï Ê³âË¢ Ï ]Ë¢ t â [ Ï ]Ê³ ([ Ï ]Ë¢  t)
    [Ê³âË¢] (expr-var x) = â-refl
    [Ê³âË¢] (expr-symb S es) = â-symb (Î» i â â-trans ([]Ë¢-resp-âË¢ âË¢-Ê³âË¢ (es i)) ([Ê³âË¢] (es i)))
    [Ê³âË¢] (expr-meta M ts) = â-meta (Î» i â [Ê³âË¢] (ts i))
    [Ê³âË¢] expr-eqty = â-eqty
    [Ê³âË¢] expr-eqtm = â-eqtm

    -- composition commutes with extensions

    âË¢-resp-âË¢ : â {ð} {Î² Î³ Î´ Î·} {Ï : ð â¥ Î² âË¢ Î³} {Ï : ð â¥ Î³ âË¢ Î´} â âË¢ {Î· = Î·} (Ï âË¢ Ï) âË¢ âË¢ Ï âË¢ âË¢ Ï
    âË¢-resp-âË¢ {Ï = Ï} (var-left x) = â-trans (â-trans (â-sym ([Ê³âË¢] (Ï x))) ([]Ë¢-resp-âË¢ (Î» xâ â â-refl) (Ï x))) ([Ë¢âÊ³] (Ï x))
    âË¢-resp-âË¢ (var-right y) = â-refl

    -- action of substitutions is functorial

    [ðË¢] : â {cl ð Î³} (t : Expr cl ð Î³) â [ ðË¢ ]Ë¢ t â t
    [ðË¢] (expr-var x) = â-refl
    [ðË¢] (expr-symb S es) = â-symb (Î» i â â-trans ([]Ë¢-resp-âË¢ âË¢-ðË¢ (es i)) ([ðË¢] (es i)))
    [ðË¢] (expr-meta M ts) = â-meta (Î» i â [ðË¢] (ts i))
    [ðË¢] expr-eqty = â-eqty
    [ðË¢] expr-eqtm = â-eqtm

    [âË¢] : â {cl ð} {Î³ Î´ Î·} {Ï : ð â¥ Î³ âË¢ Î´} {Ï : ð â¥ Î´ âË¢ Î·} (t : Expr cl ð Î³) â [ Ï âË¢ Ï ]Ë¢ t â [ Ï ]Ë¢ [ Ï ]Ë¢ t
    [âË¢] (expr-var x) = â-refl
    [âË¢] (expr-symb S es) = â-symb (Î» i â â-trans ([]Ë¢-resp-âË¢ âË¢-resp-âË¢ (es i)) ([âË¢] (es i)))
    [âË¢] (expr-meta M ts) = â-meta (Î» i â [âË¢] (ts i))
    [âË¢] expr-eqty = â-eqty
    [âË¢] expr-eqtm = â-eqtm

    []Ë¢-id : â {cl ð Î³} {Ï : ð â¥ Î³ âË¢ Î³} {t : Expr cl ð Î³} â Ï âË¢ ðË¢ â [ Ï ]Ë¢ t â t
    []Ë¢-id {t = t} Î¾ = â-trans ([]Ë¢-resp-âË¢ Î¾ t) ([ðË¢] t)

    []Ë¢-ð-initial : â {cl ð Î³} {Ï : ð â¥ Î³ âË¢ ð} (t : Expr cl ð ð) â [ Ï ]Ë¢ [ ð-initial ]Ê³ t â t
    []Ë¢-ð-initial (expr-symb S es) =
      â-symb (Î» i â â-trans (â-sym ([Ë¢âÊ³] (es i))) ([]Ë¢-id (Î» {(var-right x) â â-refl})))
    []Ë¢-ð-initial (expr-meta M ts) = â-meta (Î» i â []Ë¢-ð-initial (ts i))
    []Ë¢-ð-initial expr-eqty = â-eqty
    []Ë¢-ð-initial expr-eqtm = â-eqtm

  infix 5 _%_â¥_âË¢_
  _%_â¥_âË¢_ : â (ð : Signature) â MShape â VShape â VShape â Set
  _%_â¥_âË¢_ ð = _â¥_âË¢_ {ð = ð}
