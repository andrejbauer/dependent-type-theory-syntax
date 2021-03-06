open import Relation.Binary.PropositionalEquality using (_β‘_; refl; sym; trans; subst; cong)

open import Syntax
import Renaming
import Substitution

module Instantiation where

  module _ {π : Signature} where

    open Expression π
    open Substitution
    open Renaming
    open Equality

    -- the set of instantiations

    infix 5 _ββ±_β₯_

    _ββ±_β₯_ : MShape β MShape β VShape β Set
    π ββ± π β₯ Ξ³ = β {clα΄Ή Ξ³α΄Ή} (M : [ clα΄Ή , Ξ³α΄Ή ]β π) β Arg clα΄Ή π Ξ³ Ξ³α΄Ή

    -- equality of instantiations

    infix 4 _ββ±_

    _ββ±_ : β {π π} {Ξ³} (I J : π ββ± π β₯ Ξ³) β Set
    I ββ± J = β {clα΄Ή Ξ³α΄Ή} (M : [ clα΄Ή , Ξ³α΄Ή ]β _) β I M β J M

    -- equality of instaniations is an equivalence relation

    ββ±-refl : β {π π} {Ξ³} {I : π ββ± π β₯ Ξ³} β I ββ± I
    ββ±-refl M = β-refl

    ββ±-sym : β {π π} {Ξ³} {I J : π ββ± π β₯ Ξ³} β I ββ± J β J ββ± I
    ββ±-sym ΞΎ M = β-sym (ΞΎ M)

    ββ±-trans : β {π π} {Ξ³} {I J K : π ββ± π β₯ Ξ³} β I ββ± J β J ββ± K β I ββ± K
    ββ±-trans ΞΆ ΞΎ M = β-trans (ΞΆ M) (ΞΎ M)

    -- identity instantiation

    πβ± : β {π Ξ³} β π ββ± π β₯ Ξ³
    πβ± M = expr-meta-generic M

    -- instantiation extension

    ββ± : β {π π Ξ³ Ξ΄} β π ββ± π β₯ Ξ³ β π ββ± π β₯ Ξ³ β Ξ΄
    ββ± I M = [ βΚ³ var-left ]Κ³ (I M)

    -- extension respects equality

    ββ±-resp-ββ± : β {π π} {Ξ³ Ξ΄} β {I J : π ββ± π β₯ Ξ³} β I ββ± J β ββ± {Ξ΄ = Ξ΄} I ββ± ββ± J
    ββ±-resp-ββ± ΞΎ M = []Κ³-resp-β (βΚ³ var-left) (ΞΎ M)

    -- the action of an instantiation on an expression

    infix 6 [_]β±_

    [_]β±_ : β {cl π π} {Ξ³} β (π ββ± π β₯ Ξ³) β Expr cl π Ξ³ β Expr cl π Ξ³
    [ I ]β± (expr-var x) = expr-var x
    [ I ]β± (expr-symb S es) = expr-symb S (Ξ» i β [ ββ± I ]β± es i)
    [ I ]β± (expr-meta M ts) = [ [ πΛ’ , (Ξ» i β [ I ]β± ts i) ]Λ’ ]Λ’ I M
    [ I ]β± expr-eqty = expr-eqty
    [ I ]β± expr-eqtm = expr-eqtm

    -- instantiations respects equality

    []β±-resp-β : β {cl} {π π} {Ξ³} (I : π ββ± π β₯ Ξ³) {t u : Expr cl π Ξ³} β t β u β [ I ]β± t β [ I ]β± u
    []β±-resp-β I (β-β‘ ΞΎ) = β-β‘ (cong [ I ]β±_ ΞΎ)
    []β±-resp-β I (β-symb ΞΎ) = β-symb (Ξ» i β []β±-resp-β (ββ± I) (ΞΎ i))
    []β±-resp-β I (β-meta ΞΎ) = []Λ’-resp-βΛ’ ([,]Λ’-resp-βΛ’ βΛ’-refl (Ξ» i β []β±-resp-β I (ΞΎ i))) (I _)

    []β±-resp-ββ± : β {cl} {π π} {Ξ³} {I J : π ββ± π β₯ Ξ³} (t : Expr cl π Ξ³) β I ββ± J β [ I ]β± t β [ J ]β± t
    []β±-resp-ββ± (expr-var x) ΞΎ = β-refl
    []β±-resp-ββ± (expr-symb S es) ΞΎ = β-symb (Ξ» i β []β±-resp-ββ± (es i) (ββ±-resp-ββ± ΞΎ))
    []β±-resp-ββ± (expr-meta M ts) ΞΎ = []Λ’-resp-βΛ’-β ([,]Λ’-resp-βΛ’ βΛ’-refl (Ξ» i β []β±-resp-ββ± (ts i) ΞΎ)) (ΞΎ M)
    []β±-resp-ββ± expr-eqty ΞΎ = β-eqty
    []β±-resp-ββ± expr-eqtm ΞΎ = β-eqtm


    []β±-resp-ββ±-β : β {cl} {π π} {Ξ³} {I J : π ββ± π β₯ Ξ³} {t u : Expr cl π Ξ³} β
                    I ββ± J β t β u β [ I ]β± t β [ J ]β± u
    []β±-resp-ββ±-β {J = J} {t = t} ΞΆ ΞΎ = β-trans ([]β±-resp-ββ± t ΞΆ) ([]β±-resp-β J ΞΎ)

    -- composition of instantiations

    infixl 7 _ββ±_

    _ββ±_ : β {π π π} {Ξ³} β π ββ± π β₯ Ξ³ β π ββ± π β₯ Ξ³ β π ββ± π β₯ Ξ³
    (J ββ± I) M = [ ββ± J ]β± I M

    -- composition of a renaming and instantiation

    infixr 7 _Κ³ββ±_

    _Κ³ββ±_ : β {π π} {Ξ³ Ξ΄} β (Ο : Ξ³ βΚ³ Ξ΄) β (I : π ββ± π β₯ Ξ³) β π ββ± π β₯ Ξ΄
    (Ο Κ³ββ± I) M =  [ βΚ³ Ο ]Κ³ I M

    ββ±-resp-Κ³ββ± : β {π π} {Ξ³ Ξ΄ Ξ·} {Ο : Ξ³ βΚ³ Ξ΄} β {I : π ββ± π β₯ Ξ³} β
                  ββ± {Ξ΄ = Ξ·} (Ο Κ³ββ± I) ββ± βΚ³ Ο Κ³ββ± ββ± I
    ββ±-resp-Κ³ββ± {I = I} M =
      β-trans
        (β-trans
          (β-sym ([βΚ³] (I M)))
          ([]Κ³-resp-β‘Κ³ (I M) (Ξ» {(var-left x) β refl ; (var-right y) β refl})))
        ([βΚ³] (I M))

    [Κ³ββ±] : β {cl π π} {Ξ³ Ξ΄} {Ο : Ξ³ βΚ³ Ξ΄} {I : π ββ± π β₯ Ξ³} (t : Expr cl π Ξ³) β
             [ Ο ]Κ³ ([ I ]β± t) β [ Ο Κ³ββ± I ]β± [ Ο ]Κ³ t
    [Κ³ββ±] (expr-var x) = β-refl
    [Κ³ββ±] {Ο = Ο} {I = I} (expr-symb S es) =
      β-symb (Ξ» i β β-trans
                     ([Κ³ββ±] (es i))
                     ([]β±-resp-ββ±
                        ([ βΚ³ Ο ]Κ³ es i)
                        (ββ±-sym (ββ±-resp-Κ³ββ± {I = I}))))
    [Κ³ββ±] {Ο = Ο} {I = I} (expr-meta M ts) =
      β-trans
        (β-sym ([Κ³βΛ’] (I M)))
        (β-trans
          ([]Λ’-resp-βΛ’ (Ξ» { (var-left x) β β-refl ; (var-right y) β  [Κ³ββ±] (ts y)}) (I M))
          ([Λ’βΚ³] (I M)))
    [Κ³ββ±] expr-eqty = β-eqty
    [Κ³ββ±] expr-eqtm = β-eqtm

    -- composition of an instantiation and substitution

    infixr 7 _β±βΛ’_

    _β±βΛ’_ : β {π π} {Ξ³ Ξ΄} (I : π ββ± π β₯ Ξ΄) (Ο : π β₯ Ξ³ βΛ’ Ξ΄) β (π β₯ Ξ³ βΛ’ Ξ΄)
    (I β±βΛ’ Ο) x = [ I ]β± Ο x

    -- extension respects identity

    ββ±-resp-πβ± : β {π Ξ³ Ξ΄} β ββ± {Ξ΄ = Ξ΄} πβ± ββ± πβ± {π = π} {Ξ³ = Ξ³ β Ξ΄}
    ββ±-resp-πβ± {clα΄Ή = obj _} M = β-refl
    ββ±-resp-πβ± {clα΄Ή = EqTy} M = β-eqty
    ββ±-resp-πβ± {clα΄Ή = EqTm} M = β-eqtm

    -- extension respects composition

    ββ±-resp-ββ± : β {π π π Ξ³ Ξ΄} {I : π ββ± π β₯ Ξ³} {J : π ββ± π β₯ Ξ³} β ββ± {Ξ΄ = Ξ΄} (J ββ± I) ββ± ββ± J ββ± ββ± I
    ββ±-resp-ββ± {I = I} {J = J} M =
      β-trans
        ([Κ³ββ±] (I M))
        ([]β±-resp-ββ± ([ βΚ³ var-left ]Κ³ I M)
          Ξ» N β β-trans (β-sym ([βΚ³] (J N)))
                  (β-trans ([]Κ³-resp-β‘Κ³ (J N)  Ξ» {(var-left x) β refl ; (var-right y) β refl}) ([βΚ³] (J N))))

    ββ±-resp-β±βΛ’ : β {π π} {Ξ³ Ξ΄ Ξ·} {I : π ββ± π β₯ Ξ΄} {Ο : π β₯ Ξ³ βΛ’ Ξ΄} β
                  βΛ’ {Ξ· = Ξ·} (I β±βΛ’ Ο ) βΛ’ ββ± I β±βΛ’ βΛ’ Ο
    ββ±-resp-β±βΛ’ {Ο = Ο}(var-left x) = β-trans ([Κ³ββ±] (Ο x)) ([]β±-resp-ββ± ([ var-left ]Κ³ Ο x) (Ξ» _ β β-refl))
    ββ±-resp-β±βΛ’ (var-right y) = β-refl


    -- the action of an instantiation on a generic metavariable application

    []β±-meta-generic : β {π π} {Ξ³} {I : π ββ± π β₯ Ξ³} {clα΄Ή Ξ³α΄Ή} {M : [ clα΄Ή , Ξ³α΄Ή ]β π} β [ ββ± I ]β± (expr-meta-generic {Ξ³ = Ξ³} M) β I M
    []β±-meta-generic {I = I} {clα΄Ή = obj _} {M = M} =
      β-trans (β-sym ([Λ’βΚ³] (I M))) ([]Λ’-id (Ξ» { (var-left _) β β-refl ; (var-right _) β β-refl}))
    []β±-meta-generic {clα΄Ή = EqTy} = β-eqty
    []β±-meta-generic {clα΄Ή = EqTm} = β-eqtm

    -- action of the identity

    [πβ±] : β {cl π Ξ³} (t : Expr cl π Ξ³) β [ πβ± ]β± t β t
    [πβ±] (expr-var x) = β-refl
    [πβ±] (expr-symb S es) = β-symb (Ξ» i β β-trans ([]β±-resp-ββ± (es i) ββ±-resp-πβ±) ([πβ±] (es i)))
    [πβ±] (expr-meta M ts) = β-meta (Ξ» i β [πβ±] (ts i))
    [πβ±] (expr-eqty) = β-eqty
    [πβ±] (expr-eqtm) = β-eqtm

    -- interaction of instantiation, substitution and renaming

    []β±-[]Λ’ : β {cl π π Ξ³ Ξ΄} {I : π ββ± π β₯ Ξ΄} {Ο : π β₯ Ξ³ βΛ’ Ξ΄} {Ο : Ξ΄ βΚ³ Ξ³} (t : Expr cl π Ξ³) β
          Ο Λ’βΚ³ Ο βΛ’ πΛ’ β ([ I ]β± ([ Ο ]Λ’ t)) β ([ I β±βΛ’ Ο ]Λ’ [ Ο Κ³ββ± I ]β± t)
    []β±-[]Λ’ (expr-var x) ΞΎ = β-refl
    []β±-[]Λ’ {I = I} {Ο = Ο} {Ο = Ο} (expr-symb S es) ΞΎ =
      β-symb (Ξ» i β
        β-trans
          ([]β±-[]Λ’ {Ο = βΚ³ Ο} (es i)
            Ξ» where
              (var-left x) β []Κ³-resp-β var-left (ΞΎ x)
              (var-right x) β β-refl)
          (β-sym ([]Λ’-resp-βΛ’-β (ββ±-resp-β±βΛ’) (([]β±-resp-ββ± (es i) (ββ±-resp-Κ³ββ± {I = I}))))))
    []β±-[]Λ’ {I = I} {Ο = Ο} (expr-meta M ts) ΞΎ =
      β-trans
        (β-trans
          ([]Λ’-resp-βΛ’ (Ξ» where
                          (var-left x) β β-sym ([]β±-resp-β I (ΞΎ x))
                          (var-right x) β []β±-[]Λ’ (ts x) ΞΎ)
                       (I M))
          ([βΛ’] (I M)))
        (β-sym ([]Λ’-resp-β (I β±βΛ’ Ο) (β-sym ([Λ’βΚ³] (I M))) ))
    []β±-[]Λ’ expr-eqty _ = β-eqty
    []β±-[]Λ’ expr-eqtm _ = β-eqtm

    _Λ’ββ±_ : β {π π Ξ³ Ξ΄} β π % π β₯ Ξ³ βΛ’ Ξ΄ β π ββ± π β₯ Ξ³ β π ββ± π β₯ Ξ΄
    (Ο Λ’ββ± I) M =  [ βΛ’ Ο ]Λ’ I M

    ββ±-resp-Λ’ββ± : β {π π Ξ³ Ξ΄ Ξ·} {Ο : π % π β₯ Ξ³ βΛ’ Ξ΄} {I : π ββ± π β₯ Ξ³} β
                  ββ± {Ξ΄ = Ξ·} (Ο Λ’ββ± I) ββ± βΛ’ Ο Λ’ββ± ββ± I
    ββ±-resp-Λ’ββ± {I = I} M =
      β-trans
        (β-sym ([Κ³βΛ’] (I M)))
        (β-trans
           ([]Λ’-resp-βΛ’ (βΛ’-sym βΛ’-resp-Κ³βΛ’) (I M))
           (β-trans
              ([]Λ’-resp-βΛ’
                 (Ξ» { (var-left x) β β-refl ; (var-right y) β β-refl})
                 (I M))
              ([Λ’βΚ³] (I M))))

    []Λ’-[]β± : β {cl π π Ξ³ Ξ΄ Ξ·} {I : π ββ± π β₯ Ξ³} {Ο : π % π β₯ Ξ³ βΛ’ Ξ΄} {Ο : Ξ· βΚ³ Ξ΄} {Ο : Ξ· βΚ³ Ξ³} (t : Expr cl π Ξ·) β
              (β x β Ο (Ο x) β expr-var (Ο x)) β [ Ο ]Λ’ ([ I ]β± ([ Ο ]Κ³ t)) β [ Ο Λ’ββ± I ]β± ([ Ο ]Κ³ t)
    []Λ’-[]β± (expr-var x) ΞΎ = ΞΎ x
    []Λ’-[]β± {I = I} {Ο = Ο} {Ο = Ο} (expr-symb S es) ΞΎ =
      β-symb
        (Ξ» i β
           β-trans
             ([]Λ’-[]β± {I = ββ± I} {Ο = βΛ’ Ο} {Ο = βΚ³ Ο} (es i)
                (Ξ» { (var-left x) β []Κ³-resp-β var-left (ΞΎ x)
                   ; (var-right x) β β-refl}))
             ([]β±-resp-ββ± ([ βΚ³ Ο ]Κ³ es i) (ββ±-sym (ββ±-resp-Λ’ββ± {Ο = Ο} {I = I}))))
    []Λ’-[]β± {I = I} {Ο = Ο} (expr-meta M ts) ΞΎ =
      β-trans
        (β-sym ([βΛ’] (I M)))
        (β-trans
           ([]Λ’-resp-βΛ’
              (Ξ» { (var-left x) β β-trans (β-sym ([πΛ’] (Ο x))) ([Λ’βΚ³] (Ο x))
                 ; (var-right j) β []Λ’-[]β± (ts j) ΞΎ}) (I M))
           ([βΛ’] (I M)))
    []Λ’-[]β± expr-eqty ΞΎ = β-eqty
    []Λ’-[]β± expr-eqtm ΞΎ = β-eqtm

    -- action of composition

    [ββ±] : β {cl π π π Ξ³} {I : π ββ± π β₯ Ξ³} {J : πΒ ββ± π β₯ Ξ³} (t : Expr cl π Ξ³) β [ J ββ± I ]β± t β [ J ]β± [ I ]β± t
    [ββ±] (expr-var _) = β-refl
    [ββ±] {I = I} {J = J} (expr-symb S es) =
      β-symb (Ξ» i β β-trans ([]β±-resp-ββ± (es i) (ββ±-resp-ββ± {I = I})) ([ββ±] (es i)))
    [ββ±] {I = I} {J = J} (expr-meta M ts) =
      β-sym (β-trans
               ([]β±-[]Λ’ {I = J} {Ο = var-left} (I M) Ξ» _ β β-refl)
               ([]Λ’-resp-βΛ’
                 (Ξ» { (var-left x) β β-refl ; (var-right x) β β-sym ([ββ±] (ts x))})
                 ([ ββ± J ]β± (I M))))
    [ββ±] expr-eqty = β-eqty
    [ββ±] expr-eqtm = β-eqtm

  -- Notation for working with multiple signatures

  infix 5 _%_ββ±_β₯_
  _%_ββ±_β₯_ : β (π : Signature) β MShape β MShape β VShape β Set
  _%_ββ±_β₯_ π = _ββ±_β₯_ {π = π}
