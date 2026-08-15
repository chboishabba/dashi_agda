module DASHI.Physics.YangMills.BalabanP33RationalQuaternionFlatCurlPolynomialShapeExact where

------------------------------------------------------------------------
-- DASHI CONTRIBUTION
-- The scalar polynomial shape shared by the atom recursion and the three
-- coordinate curl leaves.  All normalization lemmas below involve at most six
-- rational variables; no twelve-coordinate normalization is present.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base as ℚ using (ℚ; _+_; -_)
import Data.Rational.Tactic.RingSolver as ℚRing

row0Shape : ℚ → ℚ → ℚ → ℚ
row0Shape ab ac ad = ab + ((- ac) + (- ad))

row1Shape : ℚ → ℚ → ℚ
row1Shape bc bd = (- bc) + (- bd)

tail23Shape : ℚ → ℚ → ℚ → ℚ
tail23Shape cc cd dd = cc + (cd + (cd + dd))

doubleWithTail : ℚ → ℚ → ℚ
doubleWithTail value tail = value + (value + tail)

addWithTail : ℚ → ℚ → ℚ
addWithTail value tail = value + tail

flatRecursionShape :
  ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ
flatRecursionShape aa ab ac ad bb bc bd cc cd dd =
  addWithTail aa
    (doubleWithTail (row0Shape ab ac ad)
      (addWithTail bb
        (doubleWithTail (row1Shape bc bd)
          (tail23Shape cc cd dd))))

row0ShapeAdd : ∀ ab₁ ab₂ ac₁ ac₂ ad₁ ad₂ →
  row0Shape (ab₁ + ab₂) (ac₁ + ac₂) (ad₁ + ad₂)
  ≡ row0Shape ab₁ ac₁ ad₁ + row0Shape ab₂ ac₂ ad₂
row0ShapeAdd ab₁ ab₂ ac₁ ac₂ ad₁ ad₂ =
  ℚRing.solve (ab₁ ∷ ab₂ ∷ ac₁ ∷ ac₂ ∷ ad₁ ∷ ad₂ ∷ [])

row1ShapeAdd : ∀ bc₁ bc₂ bd₁ bd₂ →
  row1Shape (bc₁ + bc₂) (bd₁ + bd₂)
  ≡ row1Shape bc₁ bd₁ + row1Shape bc₂ bd₂
row1ShapeAdd bc₁ bc₂ bd₁ bd₂ =
  ℚRing.solve (bc₁ ∷ bc₂ ∷ bd₁ ∷ bd₂ ∷ [])

tail23ShapeAdd : ∀ cc₁ cc₂ cd₁ cd₂ dd₁ dd₂ →
  tail23Shape (cc₁ + cc₂) (cd₁ + cd₂) (dd₁ + dd₂)
  ≡ tail23Shape cc₁ cd₁ dd₁ + tail23Shape cc₂ cd₂ dd₂
tail23ShapeAdd cc₁ cc₂ cd₁ cd₂ dd₁ dd₂ =
  ℚRing.solve (cc₁ ∷ cc₂ ∷ cd₁ ∷ cd₂ ∷ dd₁ ∷ dd₂ ∷ [])

doubleWithTailAdd : ∀ value₁ value₂ tail₁ tail₂ →
  doubleWithTail (value₁ + value₂) (tail₁ + tail₂)
  ≡ doubleWithTail value₁ tail₁ + doubleWithTail value₂ tail₂
doubleWithTailAdd value₁ value₂ tail₁ tail₂ =
  ℚRing.solve (value₁ ∷ value₂ ∷ tail₁ ∷ tail₂ ∷ [])

addWithTailAdd : ∀ value₁ value₂ tail₁ tail₂ →
  addWithTail (value₁ + value₂) (tail₁ + tail₂)
  ≡ addWithTail value₁ tail₁ + addWithTail value₂ tail₂
addWithTailAdd value₁ value₂ tail₁ tail₂ =
  ℚRing.solve (value₁ ∷ value₂ ∷ tail₁ ∷ tail₂ ∷ [])

flatRecursionShapeAdd :
  ∀ aa₁ aa₂ ab₁ ab₂ ac₁ ac₂ ad₁ ad₂ bb₁ bb₂
    bc₁ bc₂ bd₁ bd₂ cc₁ cc₂ cd₁ cd₂ dd₁ dd₂ →
  flatRecursionShape
    (aa₁ + aa₂) (ab₁ + ab₂) (ac₁ + ac₂) (ad₁ + ad₂)
    (bb₁ + bb₂) (bc₁ + bc₂) (bd₁ + bd₂)
    (cc₁ + cc₂) (cd₁ + cd₂) (dd₁ + dd₂)
  ≡ flatRecursionShape aa₁ ab₁ ac₁ ad₁ bb₁ bc₁ bd₁ cc₁ cd₁ dd₁
    + flatRecursionShape aa₂ ab₂ ac₂ ad₂ bb₂ bc₂ bd₂ cc₂ cd₂ dd₂
flatRecursionShapeAdd
    aa₁ aa₂ ab₁ ab₂ ac₁ ac₂ ad₁ ad₂ bb₁ bb₂
    bc₁ bc₂ bd₁ bd₂ cc₁ cc₂ cd₁ cd₂ dd₁ dd₂
  rewrite row0ShapeAdd ab₁ ab₂ ac₁ ac₂ ad₁ ad₂
    | row1ShapeAdd bc₁ bc₂ bd₁ bd₂
    | tail23ShapeAdd cc₁ cc₂ cd₁ cd₂ dd₁ dd₂
    | doubleWithTailAdd
        (row1Shape bc₁ bd₁) (row1Shape bc₂ bd₂)
        (tail23Shape cc₁ cd₁ dd₁) (tail23Shape cc₂ cd₂ dd₂)
    | addWithTailAdd bb₁ bb₂
        (doubleWithTail (row1Shape bc₁ bd₁) (tail23Shape cc₁ cd₁ dd₁))
        (doubleWithTail (row1Shape bc₂ bd₂) (tail23Shape cc₂ cd₂ dd₂))
    | doubleWithTailAdd
        (row0Shape ab₁ ac₁ ad₁) (row0Shape ab₂ ac₂ ad₂)
        (addWithTail bb₁
          (doubleWithTail (row1Shape bc₁ bd₁) (tail23Shape cc₁ cd₁ dd₁)))
        (addWithTail bb₂
          (doubleWithTail (row1Shape bc₂ bd₂) (tail23Shape cc₂ cd₂ dd₂)))
    | addWithTailAdd aa₁ aa₂
        (doubleWithTail (row0Shape ab₁ ac₁ ad₁)
          (addWithTail bb₁
            (doubleWithTail (row1Shape bc₁ bd₁) (tail23Shape cc₁ cd₁ dd₁))))
        (doubleWithTail (row0Shape ab₂ ac₂ ad₂)
          (addWithTail bb₂
            (doubleWithTail (row1Shape bc₂ bd₂) (tail23Shape cc₂ cd₂ dd₂)))) = refl
