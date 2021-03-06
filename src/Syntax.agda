open import Agda.Primitive using (lzero; lsuc; _โ_; Level)
open import Relation.Binary.PropositionalEquality using (_โก_; refl; subst)
open import Relation.Binary using (Setoid)

-- A formalization of raw syntax

module Syntax where

  -- Syntactic classes

  data ObjectClass : Set where
    Ty Tm : ObjectClass

  data Class : Set where
    obj : ObjectClass โ Class
    EqTy EqTm : Class

  -- Variable context shape

  infixl 6 _โ_

  data VShape : Set where
    ๐ : VShape
    ๐ : VShape
    _โ_ : VShape โ VShape โ VShape

  data var : VShape โ Set where
    var-here : var ๐
    var-left : โ {ฮณ ฮด} โ var ฮณ โ var (ฮณ โ ฮด)
    var-right : โ {ฮณ ฮด} โ var ฮด โ var (ฮณ โ ฮด)

  -- Metavariable context shapes

  infixl 9 _โแตแต_

  data MShape : Set where
    ๐แตแต : MShape
    ๐แตแต : โ (cl : Class) (ฮณ : VShape) โ MShape
    _โแตแต_ : MShape โ MShape โ MShape

  infix 8 [_,_]โ_

  data [_,_]โ_ : Class โ VShape โ MShape โ Set where
    mv-here : โ cl ฮณ โ [ cl , ฮณ ]โ ๐แตแต cl ฮณ
    mv-left : โ {๐ ๐} cl ฮณ โ [ cl , ฮณ ]โ ๐ โ [ cl , ฮณ ]โ ๐ โแตแต ๐
    mv-right : โ {๐ ๐} cl ฮณ โ [ cl , ฮณ ]โ ๐ โ [ cl , ฮณ ]โ ๐ โแตแต ๐

  -- Symbol signature

  record Signature : Setโ where
    field
      symb : ObjectClass โ Set -- a set of symbol names, one for each class
      symb-arg : โ {cl} โ symb cl โ MShape

  -- Expressions

  module Expression (๐ : Signature) where
    open Signature ๐

    data Expr : Class โ (๐ : MShape) โ (ฮณ : VShape) โ Set

    Arg : โ (cl : Class) (๐ : MShape) (ฮณ : VShape) (ฮด : VShape) โ Set
    Arg cl ๐ ฮณ ฮด = Expr cl ๐ (ฮณ โ ฮด)

    ExprObj : โ (cl : ObjectClass) (๐ : MShape) (ฮณ : VShape) โ Set
    ExprObj cl = Expr (obj cl)

    ExprTm = ExprObj Tm
    ExprTy = ExprObj Ty

    data Expr where
      expr-var : โ {๐} {ฮณ} (x : var ฮณ) โ ExprTm ๐ ฮณ
      expr-symb : โ {cl ๐ ฮณ} (S : symb cl) โ
                    (es : โ {clโฑ ฮณโฑ} (i : [ clโฑ , ฮณโฑ ]โ symb-arg S) โ Arg clโฑ ๐ ฮณ ฮณโฑ) โ
                    ExprObj cl ๐ ฮณ
      expr-meta : โ {cl ๐ ฮณ} {ฮณแดน} (M : [ obj cl , ฮณแดน ]โ ๐) โ (ts : โ (i : var ฮณแดน) โ ExprTm ๐ ฮณ) โ ExprObj cl ๐ ฮณ
      expr-eqty : โ {ฮณ} {๐} โ Expr EqTy ๐ ฮณ
      expr-eqtm : โ {ฮณ} {๐} โ Expr EqTm ๐ ฮณ

    expr-meta-generic : โ {๐} {cl} {ฮณ ฮณแดน} (M : [ cl , ฮณแดน ]โ ๐) โ Arg cl ๐ ฮณ ฮณแดน
    expr-meta-generic {cl = obj _} M = expr-meta M (ฮป i โ expr-var (var-right i))
    expr-meta-generic {cl = EqTy} M = expr-eqty
    expr-meta-generic {cl = EqTm} M = expr-eqtm

  -- Syntactic equality

  module Equality {๐ : Signature} where

    open Signature ๐
    open Expression ๐

    infix 4 _โ_

    data _โ_ : โ {cl ๐ ฮณ} โ Expr cl ๐ ฮณ โ Expr cl ๐ ฮณ โ Set where
      โ-โก : โ {cl ๐ ฮณ} {t u : Expr cl ๐ ฮณ} (ฮพ : t โก u) โ t โ u
      โ-symb : โ {cl ๐ ฮณ} {S : symb cl} โ
                {ds es : โ {cโฑ ฮณโฑ} (i : [ cโฑ , ฮณโฑ ]โ symb-arg S) โ Arg cโฑ ๐ ฮณ ฮณโฑ}
                (ฮพ : โ {cโฑ ฮณโฑ} (i : [ cโฑ , ฮณโฑ ]โ symb-arg S) โ ds i โ es i) โ expr-symb S ds โ expr-symb S es
      โ-meta : โ {cl ๐ ฮณ} {ฮณแดน} {M : [ obj cl , ฮณแดน ]โ ๐} โ {ts us : โ (i : var ฮณแดน) โ ExprTm ๐ ฮณ}
                (ฮพ : โ i โ ts i โ us i) โ expr-meta M ts โ expr-meta M us

    โ-refl : โ {cl ๐ ฮณ} {t : Expr cl ๐ ฮณ} โ t โ t
    โ-refl = โ-โก refl

    โ-eqty : โ {๐ ฮณ} {s t : Expr EqTy ๐  ฮณ} โ s โ t
    โ-eqty {s = expr-eqty} {t = expr-eqty} = โ-refl

    โ-eqtm : โ {๐ ฮณ} {s t : Expr EqTm ๐ ฮณ} โ s โ t
    โ-eqtm {s = expr-eqtm} {t = expr-eqtm} = โ-refl

    โ-sym : โ {cl ๐ ฮณ} {t u : Expr cl ๐ ฮณ} โ t โ u โ u โ t
    โ-sym (โ-โก refl) = โ-โก refl
    โ-sym (โ-symb ฮต) = โ-symb (ฮป i โ โ-sym (ฮต i))
    โ-sym (โ-meta ฮต) = โ-meta (ฮป i โ โ-sym (ฮต i))

    โ-trans : โ {cl ๐ ฮณ} {t u v : Expr cl ๐ ฮณ} โ t โ u โ u โ v โ t โ v
    โ-trans (โ-โก refl) ฮพ = ฮพ
    โ-trans (โ-symb ฮถ) (โ-โก refl) = โ-symb ฮถ
    โ-trans (โ-symb ฮถ) (โ-symb ฮพ) = โ-symb (ฮป i โ โ-trans (ฮถ i) (ฮพ i))
    โ-trans (โ-meta ฮถ) (โ-โก refl) = โ-meta ฮถ
    โ-trans (โ-meta ฮถ) (โ-meta ฮพ) = โ-meta (ฮป i โ โ-trans (ฮถ i) (ฮพ i))

    -- the setoid of expressions

    Expr-setoid : โ (cl : Class) (๐ : MShape) (ฮณ : VShape) โ  Setoid lzero lzero
    Expr-setoid cl ๐ ฮณ =
      record
        { Carrier =  Expr cl ๐ ฮณ
        ; _โ_ = _โ_
        ; isEquivalence = record { refl = โ-refl ; sym = โ-sym ; trans = โ-trans }
        }

  infix 4 _%_โ_

  _%_โ_ : โ (๐ : Signature) {cl ๐ ฮณ} โ (t u : Expression.Expr ๐ cl ๐ ฮณ) โ Set
  _%_โ_ ๐ = Equality._โ_ {๐ = ๐}
