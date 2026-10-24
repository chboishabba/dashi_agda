module DASHI.Biology.IITF81F9ConcreteQuarticTowerExact where

open import DASHI.Core.Prelude

import DASHI.Algebra.Trit as Trit
import DASHI.Codec.TriadicPAdicCodec as Codec
import DASHI.Analysis.RiemannQuarticTriadicCodecKernelBridgeExact as K4
import DASHI.Moonshine.OggSSPP3F9FrobeniusCandidateNoGoExact as Ogg
open Codec using ([]ᵥ; _∷ᵥ_)

------------------------------------------------------------------------
-- CONCRETE F81 FIELD ON EXACT REPO OWNER K4.Kernel4 = Vec Trit 4
-- via the exact source F9-shaped Ogg.F9Point coordinate carrier.
--
-- Original quartic owner: X^4+X+2 over F3, basis gamma=(0,1,2,2),
-- beta=(0,0,1,1), gamma²=-1, beta²=1+gamma.
-- Tower F81 = F9[beta] / (beta²-(1+gamma)).
--
-- All 81 coordinate roundtrips, 80 punctured Fermat and inverse laws,
-- and 81 Frobenius/norm laws are finite *closed reduction proofs* below.
-- Source-written: exact-head Agda compiler/kernel receipt still required.
-- Source-literal P4.Kernel4 is NOT an inferred/new cardinality alias.
------------------------------------------------------------------------

infixl 6 _+₃_ _−₃_
infixl 7 _×₃_

_+₃_ : Trit.Trit → Trit.Trit → Trit.Trit
Trit.zer +₃ x = x
Trit.pos +₃ Trit.zer = Trit.pos
Trit.pos +₃ Trit.pos = Trit.neg
Trit.pos +₃ Trit.neg = Trit.zer
Trit.neg +₃ Trit.zer = Trit.neg
Trit.neg +₃ Trit.pos = Trit.zer
Trit.neg +₃ Trit.neg = Trit.pos

_−₃_ : Trit.Trit → Trit.Trit → Trit.Trit
x −₃ y = x +₃ Trit.inv y

_×₃_ : Trit.Trit → Trit.Trit → Trit.Trit
Trit.zer ×₃ y = Trit.zer
Trit.pos ×₃ y = y
Trit.neg ×₃ y = Trit.inv y

toTrit : Ogg.F3 → Trit.Trit
toTrit Ogg.z3 = Trit.zer
toTrit Ogg.o3 = Trit.pos
toTrit Ogg.t3 = Trit.neg

fromTrit : Trit.Trit → Ogg.F3
fromTrit Trit.zer = Ogg.z3
fromTrit Trit.pos = Ogg.o3
fromTrit Trit.neg = Ogg.t3

data Tower81 : Set where
  tower81 : Ogg.F9Point → Ogg.F9Point → Tower81

zero9 : Ogg.F9Point
zero9 = Ogg.f9 Ogg.z3 Ogg.z3

one9 : Ogg.F9Point
one9 = Ogg.f9 Ogg.o3 Ogg.z3

delta9 : Ogg.F9Point
delta9 = Ogg.f9 Ogg.o3 Ogg.o3

plus9 : Ogg.F9Point → Ogg.F9Point → Ogg.F9Point
plus9 (Ogg.f9 a b) (Ogg.f9 c d) =
  Ogg.f9
    (fromTrit (toTrit a +₃ toTrit c))
    (fromTrit (toTrit b +₃ toTrit d))

negate9 : Ogg.F9Point → Ogg.F9Point
negate9 (Ogg.f9 a b) =
  Ogg.f9 (fromTrit (Trit.inv (toTrit a)))
         (fromTrit (Trit.inv (toTrit b)))

minus9 : Ogg.F9Point → Ogg.F9Point → Ogg.F9Point
minus9 a b = plus9 a (negate9 b)

times9 : Ogg.F9Point → Ogg.F9Point → Ogg.F9Point
times9 (Ogg.f9 a b) (Ogg.f9 c d) =
  Ogg.f9
    (fromTrit ((toTrit a ×₃ toTrit c) −₃ (toTrit b ×₃ toTrit d)))
    (fromTrit ((toTrit a ×₃ toTrit d) +₃ (toTrit b ×₃ toTrit c)))

plus81 : Tower81 → Tower81 → Tower81
plus81 (tower81 a b) (tower81 c d) =
  tower81 (plus9 a c) (plus9 b d)

times81 : Tower81 → Tower81 → Tower81
times81 (tower81 a b) (tower81 c d) =
  tower81
    (plus9 (times9 a c) (times9 delta9 (times9 b d)))
    (plus9 (times9 a d) (times9 b c))

zero81 : Tower81
zero81 = tower81 zero9 zero9

one81 : Tower81
one81 = tower81 one9 zero9

gamma81 : Tower81
gamma81 = tower81 (Ogg.f9 Ogg.z3 Ogg.o3) zero9

beta81 : Tower81
beta81 = tower81 zero9 one9

negOne81 : Tower81
negOne81 = tower81 (Ogg.f9 Ogg.t3 Ogg.z3) zero9

onePlusGamma81 : Tower81
onePlusGamma81 =
  tower81 (Ogg.f9 Ogg.o3 Ogg.o3) zero9

gammaSquareIsNegativeOne :
  times81 gamma81 gamma81 ≡ negOne81
gammaSquareIsNegativeOne = refl

betaSquareIsOnePlusGamma :
  times81 beta81 beta81 ≡ onePlusGamma81
betaSquareIsOnePlusGamma = refl

-- Source-aligned quartic basis:
-- 1=(1,0,0,0), gamma=(0,1,-1,-1),
-- beta=(0,0,1,1), gamma*beta=(0,1,1,-1).
-- Exact forward coordinates:
--   c0=a0
--   c1=a1+b1
--   c2=-a1+b0+b1
--   c3=-a1+b0-b1
-- Exact inverse:
--   a0=c0
--   a1=c1+c2-c3
--   b0=c1+c3
--   b1=c3-c2

toOriginalKernel4 : Tower81 → K4.Kernel4
toOriginalKernel4 (tower81 (Ogg.f9 a0 a1) (Ogg.f9 b0 b1)) =
  toTrit a0
  ∷ᵥ (toTrit a1 +₃ toTrit b1)
  ∷ᵥ ((Trit.inv (toTrit a1) +₃ toTrit b0) +₃ toTrit b1)
  ∷ᵥ ((Trit.inv (toTrit a1) +₃ toTrit b0) −₃ toTrit b1)
  ∷ᵥ []ᵥ

fromOriginalKernel4 : K4.Kernel4 → Tower81
fromOriginalKernel4
  (c0 ∷ᵥ c1 ∷ᵥ c2 ∷ᵥ c3 ∷ᵥ []ᵥ) =
  tower81
    (Ogg.f9
      (fromTrit c0)
      (fromTrit ((c1 +₃ c2) −₃ c3)))
    (Ogg.f9
      (fromTrit (c1 +₃ c3))
      (fromTrit (c3 −₃ c2)))

toOriginalGamma :
  toOriginalKernel4 gamma81
  ≡ Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ
toOriginalGamma = refl

toOriginalBeta :
  toOriginalKernel4 beta81
  ≡ Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ
toOriginalBeta = refl

-- Multiplication and addition on the literal OLD quartic Kernel4
-- are transported through the checked same-object coordinate chart.
quarticAdd : K4.Kernel4 → K4.Kernel4 → K4.Kernel4
quarticAdd x y =
  toOriginalKernel4
    (plus81 (fromOriginalKernel4 x) (fromOriginalKernel4 y))

quarticMultiply : K4.Kernel4 → K4.Kernel4 → K4.Kernel4
quarticMultiply x y =
  toOriginalKernel4
    (times81 (fromOriginalKernel4 x) (fromOriginalKernel4 y))

square81 : Tower81 → Tower81
square81 x = times81 x x

power2 : Tower81 → Tower81
power2 = square81

power4 : Tower81 → Tower81
power4 x = square81 (power2 x)

power8 : Tower81 → Tower81
power8 x = square81 (power4 x)

power16 : Tower81 → Tower81
power16 x = square81 (power8 x)

power32 : Tower81 → Tower81
power32 x = square81 (power16 x)

power64 : Tower81 → Tower81
power64 x = square81 (power32 x)

power9 : Tower81 → Tower81
power9 x = times81 (power8 x) x

power10 : Tower81 → Tower81
power10 x = times81 (power8 x) (power2 x)

power79 : Tower81 → Tower81
power79 x =
  times81 (power64 x)
    (times81 (power8 x)
      (times81 (power4 x)
        (times81 (power2 x) x)))

power80 : Tower81 → Tower81
power80 x = times81 (power64 x) (power16 x)

relativeConjugate : Tower81 → Tower81
relativeConjugate (tower81 a b) = tower81 a (negate9 b)

quadraticNorm : Tower81 → Tower81
quadraticNorm (tower81 a b) =
  tower81
    (minus9 (times9 a a) (times9 delta9 (times9 b b)))
    zero9

------------------------------------------------------------------------
-- Below are generated exhaustive, CLOSED normal-form reductions.
-- If a user changes source Trit or F9 semantics these clauses fail,
-- rather than silently treating a value coincidence as a theorem.
------------------------------------------------------------------------


fromAfterToTower :
  (x : Tower81) → fromOriginalKernel4 (toOriginalKernel4 x) ≡ x
fromAfterToTower (tower81 (Ogg.f9 Ogg.z3 Ogg.z3) (Ogg.f9 Ogg.z3 Ogg.z3)) = refl
fromAfterToTower (tower81 (Ogg.f9 Ogg.z3 Ogg.z3) (Ogg.f9 Ogg.z3 Ogg.o3)) = refl
fromAfterToTower (tower81 (Ogg.f9 Ogg.z3 Ogg.z3) (Ogg.f9 Ogg.z3 Ogg.t3)) = refl
fromAfterToTower (tower81 (Ogg.f9 Ogg.z3 Ogg.z3) (Ogg.f9 Ogg.o3 Ogg.z3)) = refl
fromAfterToTower (tower81 (Ogg.f9 Ogg.z3 Ogg.z3) (Ogg.f9 Ogg.o3 Ogg.o3)) = refl
fromAfterToTower (tower81 (Ogg.f9 Ogg.z3 Ogg.z3) (Ogg.f9 Ogg.o3 Ogg.t3)) = refl
fromAfterToTower (tower81 (Ogg.f9 Ogg.z3 Ogg.z3) (Ogg.f9 Ogg.t3 Ogg.z3)) = refl
fromAfterToTower (tower81 (Ogg.f9 Ogg.z3 Ogg.z3) (Ogg.f9 Ogg.t3 Ogg.o3)) = refl
fromAfterToTower (tower81 (Ogg.f9 Ogg.z3 Ogg.z3) (Ogg.f9 Ogg.t3 Ogg.t3)) = refl
fromAfterToTower (tower81 (Ogg.f9 Ogg.z3 Ogg.o3) (Ogg.f9 Ogg.z3 Ogg.z3)) = refl
fromAfterToTower (tower81 (Ogg.f9 Ogg.z3 Ogg.o3) (Ogg.f9 Ogg.z3 Ogg.o3)) = refl
fromAfterToTower (tower81 (Ogg.f9 Ogg.z3 Ogg.o3) (Ogg.f9 Ogg.z3 Ogg.t3)) = refl
fromAfterToTower (tower81 (Ogg.f9 Ogg.z3 Ogg.o3) (Ogg.f9 Ogg.o3 Ogg.z3)) = refl
fromAfterToTower (tower81 (Ogg.f9 Ogg.z3 Ogg.o3) (Ogg.f9 Ogg.o3 Ogg.o3)) = refl
fromAfterToTower (tower81 (Ogg.f9 Ogg.z3 Ogg.o3) (Ogg.f9 Ogg.o3 Ogg.t3)) = refl
fromAfterToTower (tower81 (Ogg.f9 Ogg.z3 Ogg.o3) (Ogg.f9 Ogg.t3 Ogg.z3)) = refl
fromAfterToTower (tower81 (Ogg.f9 Ogg.z3 Ogg.o3) (Ogg.f9 Ogg.t3 Ogg.o3)) = refl
fromAfterToTower (tower81 (Ogg.f9 Ogg.z3 Ogg.o3) (Ogg.f9 Ogg.t3 Ogg.t3)) = refl
fromAfterToTower (tower81 (Ogg.f9 Ogg.z3 Ogg.t3) (Ogg.f9 Ogg.z3 Ogg.z3)) = refl
fromAfterToTower (tower81 (Ogg.f9 Ogg.z3 Ogg.t3) (Ogg.f9 Ogg.z3 Ogg.o3)) = refl
fromAfterToTower (tower81 (Ogg.f9 Ogg.z3 Ogg.t3) (Ogg.f9 Ogg.z3 Ogg.t3)) = refl
fromAfterToTower (tower81 (Ogg.f9 Ogg.z3 Ogg.t3) (Ogg.f9 Ogg.o3 Ogg.z3)) = refl
fromAfterToTower (tower81 (Ogg.f9 Ogg.z3 Ogg.t3) (Ogg.f9 Ogg.o3 Ogg.o3)) = refl
fromAfterToTower (tower81 (Ogg.f9 Ogg.z3 Ogg.t3) (Ogg.f9 Ogg.o3 Ogg.t3)) = refl
fromAfterToTower (tower81 (Ogg.f9 Ogg.z3 Ogg.t3) (Ogg.f9 Ogg.t3 Ogg.z3)) = refl
fromAfterToTower (tower81 (Ogg.f9 Ogg.z3 Ogg.t3) (Ogg.f9 Ogg.t3 Ogg.o3)) = refl
fromAfterToTower (tower81 (Ogg.f9 Ogg.z3 Ogg.t3) (Ogg.f9 Ogg.t3 Ogg.t3)) = refl
fromAfterToTower (tower81 (Ogg.f9 Ogg.o3 Ogg.z3) (Ogg.f9 Ogg.z3 Ogg.z3)) = refl
fromAfterToTower (tower81 (Ogg.f9 Ogg.o3 Ogg.z3) (Ogg.f9 Ogg.z3 Ogg.o3)) = refl
fromAfterToTower (tower81 (Ogg.f9 Ogg.o3 Ogg.z3) (Ogg.f9 Ogg.z3 Ogg.t3)) = refl
fromAfterToTower (tower81 (Ogg.f9 Ogg.o3 Ogg.z3) (Ogg.f9 Ogg.o3 Ogg.z3)) = refl
fromAfterToTower (tower81 (Ogg.f9 Ogg.o3 Ogg.z3) (Ogg.f9 Ogg.o3 Ogg.o3)) = refl
fromAfterToTower (tower81 (Ogg.f9 Ogg.o3 Ogg.z3) (Ogg.f9 Ogg.o3 Ogg.t3)) = refl
fromAfterToTower (tower81 (Ogg.f9 Ogg.o3 Ogg.z3) (Ogg.f9 Ogg.t3 Ogg.z3)) = refl
fromAfterToTower (tower81 (Ogg.f9 Ogg.o3 Ogg.z3) (Ogg.f9 Ogg.t3 Ogg.o3)) = refl
fromAfterToTower (tower81 (Ogg.f9 Ogg.o3 Ogg.z3) (Ogg.f9 Ogg.t3 Ogg.t3)) = refl
fromAfterToTower (tower81 (Ogg.f9 Ogg.o3 Ogg.o3) (Ogg.f9 Ogg.z3 Ogg.z3)) = refl
fromAfterToTower (tower81 (Ogg.f9 Ogg.o3 Ogg.o3) (Ogg.f9 Ogg.z3 Ogg.o3)) = refl
fromAfterToTower (tower81 (Ogg.f9 Ogg.o3 Ogg.o3) (Ogg.f9 Ogg.z3 Ogg.t3)) = refl
fromAfterToTower (tower81 (Ogg.f9 Ogg.o3 Ogg.o3) (Ogg.f9 Ogg.o3 Ogg.z3)) = refl
fromAfterToTower (tower81 (Ogg.f9 Ogg.o3 Ogg.o3) (Ogg.f9 Ogg.o3 Ogg.o3)) = refl
fromAfterToTower (tower81 (Ogg.f9 Ogg.o3 Ogg.o3) (Ogg.f9 Ogg.o3 Ogg.t3)) = refl
fromAfterToTower (tower81 (Ogg.f9 Ogg.o3 Ogg.o3) (Ogg.f9 Ogg.t3 Ogg.z3)) = refl
fromAfterToTower (tower81 (Ogg.f9 Ogg.o3 Ogg.o3) (Ogg.f9 Ogg.t3 Ogg.o3)) = refl
fromAfterToTower (tower81 (Ogg.f9 Ogg.o3 Ogg.o3) (Ogg.f9 Ogg.t3 Ogg.t3)) = refl
fromAfterToTower (tower81 (Ogg.f9 Ogg.o3 Ogg.t3) (Ogg.f9 Ogg.z3 Ogg.z3)) = refl
fromAfterToTower (tower81 (Ogg.f9 Ogg.o3 Ogg.t3) (Ogg.f9 Ogg.z3 Ogg.o3)) = refl
fromAfterToTower (tower81 (Ogg.f9 Ogg.o3 Ogg.t3) (Ogg.f9 Ogg.z3 Ogg.t3)) = refl
fromAfterToTower (tower81 (Ogg.f9 Ogg.o3 Ogg.t3) (Ogg.f9 Ogg.o3 Ogg.z3)) = refl
fromAfterToTower (tower81 (Ogg.f9 Ogg.o3 Ogg.t3) (Ogg.f9 Ogg.o3 Ogg.o3)) = refl
fromAfterToTower (tower81 (Ogg.f9 Ogg.o3 Ogg.t3) (Ogg.f9 Ogg.o3 Ogg.t3)) = refl
fromAfterToTower (tower81 (Ogg.f9 Ogg.o3 Ogg.t3) (Ogg.f9 Ogg.t3 Ogg.z3)) = refl
fromAfterToTower (tower81 (Ogg.f9 Ogg.o3 Ogg.t3) (Ogg.f9 Ogg.t3 Ogg.o3)) = refl
fromAfterToTower (tower81 (Ogg.f9 Ogg.o3 Ogg.t3) (Ogg.f9 Ogg.t3 Ogg.t3)) = refl
fromAfterToTower (tower81 (Ogg.f9 Ogg.t3 Ogg.z3) (Ogg.f9 Ogg.z3 Ogg.z3)) = refl
fromAfterToTower (tower81 (Ogg.f9 Ogg.t3 Ogg.z3) (Ogg.f9 Ogg.z3 Ogg.o3)) = refl
fromAfterToTower (tower81 (Ogg.f9 Ogg.t3 Ogg.z3) (Ogg.f9 Ogg.z3 Ogg.t3)) = refl
fromAfterToTower (tower81 (Ogg.f9 Ogg.t3 Ogg.z3) (Ogg.f9 Ogg.o3 Ogg.z3)) = refl
fromAfterToTower (tower81 (Ogg.f9 Ogg.t3 Ogg.z3) (Ogg.f9 Ogg.o3 Ogg.o3)) = refl
fromAfterToTower (tower81 (Ogg.f9 Ogg.t3 Ogg.z3) (Ogg.f9 Ogg.o3 Ogg.t3)) = refl
fromAfterToTower (tower81 (Ogg.f9 Ogg.t3 Ogg.z3) (Ogg.f9 Ogg.t3 Ogg.z3)) = refl
fromAfterToTower (tower81 (Ogg.f9 Ogg.t3 Ogg.z3) (Ogg.f9 Ogg.t3 Ogg.o3)) = refl
fromAfterToTower (tower81 (Ogg.f9 Ogg.t3 Ogg.z3) (Ogg.f9 Ogg.t3 Ogg.t3)) = refl
fromAfterToTower (tower81 (Ogg.f9 Ogg.t3 Ogg.o3) (Ogg.f9 Ogg.z3 Ogg.z3)) = refl
fromAfterToTower (tower81 (Ogg.f9 Ogg.t3 Ogg.o3) (Ogg.f9 Ogg.z3 Ogg.o3)) = refl
fromAfterToTower (tower81 (Ogg.f9 Ogg.t3 Ogg.o3) (Ogg.f9 Ogg.z3 Ogg.t3)) = refl
fromAfterToTower (tower81 (Ogg.f9 Ogg.t3 Ogg.o3) (Ogg.f9 Ogg.o3 Ogg.z3)) = refl
fromAfterToTower (tower81 (Ogg.f9 Ogg.t3 Ogg.o3) (Ogg.f9 Ogg.o3 Ogg.o3)) = refl
fromAfterToTower (tower81 (Ogg.f9 Ogg.t3 Ogg.o3) (Ogg.f9 Ogg.o3 Ogg.t3)) = refl
fromAfterToTower (tower81 (Ogg.f9 Ogg.t3 Ogg.o3) (Ogg.f9 Ogg.t3 Ogg.z3)) = refl
fromAfterToTower (tower81 (Ogg.f9 Ogg.t3 Ogg.o3) (Ogg.f9 Ogg.t3 Ogg.o3)) = refl
fromAfterToTower (tower81 (Ogg.f9 Ogg.t3 Ogg.o3) (Ogg.f9 Ogg.t3 Ogg.t3)) = refl
fromAfterToTower (tower81 (Ogg.f9 Ogg.t3 Ogg.t3) (Ogg.f9 Ogg.z3 Ogg.z3)) = refl
fromAfterToTower (tower81 (Ogg.f9 Ogg.t3 Ogg.t3) (Ogg.f9 Ogg.z3 Ogg.o3)) = refl
fromAfterToTower (tower81 (Ogg.f9 Ogg.t3 Ogg.t3) (Ogg.f9 Ogg.z3 Ogg.t3)) = refl
fromAfterToTower (tower81 (Ogg.f9 Ogg.t3 Ogg.t3) (Ogg.f9 Ogg.o3 Ogg.z3)) = refl
fromAfterToTower (tower81 (Ogg.f9 Ogg.t3 Ogg.t3) (Ogg.f9 Ogg.o3 Ogg.o3)) = refl
fromAfterToTower (tower81 (Ogg.f9 Ogg.t3 Ogg.t3) (Ogg.f9 Ogg.o3 Ogg.t3)) = refl
fromAfterToTower (tower81 (Ogg.f9 Ogg.t3 Ogg.t3) (Ogg.f9 Ogg.t3 Ogg.z3)) = refl
fromAfterToTower (tower81 (Ogg.f9 Ogg.t3 Ogg.t3) (Ogg.f9 Ogg.t3 Ogg.o3)) = refl
fromAfterToTower (tower81 (Ogg.f9 Ogg.t3 Ogg.t3) (Ogg.f9 Ogg.t3 Ogg.t3)) = refl

toAfterFromOriginal :
  (x : K4.Kernel4) → toOriginalKernel4 (fromOriginalKernel4 x) ≡ x
toAfterFromOriginal (Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ []ᵥ) = refl
toAfterFromOriginal (Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) = refl
toAfterFromOriginal (Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) = refl
toAfterFromOriginal (Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) = refl
toAfterFromOriginal (Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) = refl
toAfterFromOriginal (Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) = refl
toAfterFromOriginal (Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) = refl
toAfterFromOriginal (Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) = refl
toAfterFromOriginal (Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) = refl
toAfterFromOriginal (Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ []ᵥ) = refl
toAfterFromOriginal (Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) = refl
toAfterFromOriginal (Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) = refl
toAfterFromOriginal (Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) = refl
toAfterFromOriginal (Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) = refl
toAfterFromOriginal (Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) = refl
toAfterFromOriginal (Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) = refl
toAfterFromOriginal (Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) = refl
toAfterFromOriginal (Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) = refl
toAfterFromOriginal (Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ []ᵥ) = refl
toAfterFromOriginal (Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) = refl
toAfterFromOriginal (Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) = refl
toAfterFromOriginal (Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) = refl
toAfterFromOriginal (Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) = refl
toAfterFromOriginal (Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) = refl
toAfterFromOriginal (Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) = refl
toAfterFromOriginal (Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) = refl
toAfterFromOriginal (Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) = refl
toAfterFromOriginal (Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ []ᵥ) = refl
toAfterFromOriginal (Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) = refl
toAfterFromOriginal (Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) = refl
toAfterFromOriginal (Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) = refl
toAfterFromOriginal (Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) = refl
toAfterFromOriginal (Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) = refl
toAfterFromOriginal (Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) = refl
toAfterFromOriginal (Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) = refl
toAfterFromOriginal (Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) = refl
toAfterFromOriginal (Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ []ᵥ) = refl
toAfterFromOriginal (Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) = refl
toAfterFromOriginal (Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) = refl
toAfterFromOriginal (Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) = refl
toAfterFromOriginal (Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) = refl
toAfterFromOriginal (Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) = refl
toAfterFromOriginal (Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) = refl
toAfterFromOriginal (Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) = refl
toAfterFromOriginal (Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) = refl
toAfterFromOriginal (Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ []ᵥ) = refl
toAfterFromOriginal (Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) = refl
toAfterFromOriginal (Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) = refl
toAfterFromOriginal (Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) = refl
toAfterFromOriginal (Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) = refl
toAfterFromOriginal (Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) = refl
toAfterFromOriginal (Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) = refl
toAfterFromOriginal (Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) = refl
toAfterFromOriginal (Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) = refl
toAfterFromOriginal (Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ []ᵥ) = refl
toAfterFromOriginal (Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) = refl
toAfterFromOriginal (Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) = refl
toAfterFromOriginal (Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) = refl
toAfterFromOriginal (Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) = refl
toAfterFromOriginal (Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) = refl
toAfterFromOriginal (Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) = refl
toAfterFromOriginal (Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) = refl
toAfterFromOriginal (Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) = refl
toAfterFromOriginal (Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ []ᵥ) = refl
toAfterFromOriginal (Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) = refl
toAfterFromOriginal (Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) = refl
toAfterFromOriginal (Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) = refl
toAfterFromOriginal (Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) = refl
toAfterFromOriginal (Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) = refl
toAfterFromOriginal (Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) = refl
toAfterFromOriginal (Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) = refl
toAfterFromOriginal (Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) = refl
toAfterFromOriginal (Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ []ᵥ) = refl
toAfterFromOriginal (Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) = refl
toAfterFromOriginal (Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) = refl
toAfterFromOriginal (Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) = refl
toAfterFromOriginal (Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) = refl
toAfterFromOriginal (Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) = refl
toAfterFromOriginal (Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) = refl
toAfterFromOriginal (Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) = refl
toAfterFromOriginal (Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) = refl

relativeFrobeniusIsConjugation :
  (x : Tower81) → power9 x ≡ relativeConjugate x
relativeFrobeniusIsConjugation (tower81 (Ogg.f9 Ogg.z3 Ogg.z3) (Ogg.f9 Ogg.z3 Ogg.z3)) = refl
relativeFrobeniusIsConjugation (tower81 (Ogg.f9 Ogg.z3 Ogg.z3) (Ogg.f9 Ogg.z3 Ogg.o3)) = refl
relativeFrobeniusIsConjugation (tower81 (Ogg.f9 Ogg.z3 Ogg.z3) (Ogg.f9 Ogg.z3 Ogg.t3)) = refl
relativeFrobeniusIsConjugation (tower81 (Ogg.f9 Ogg.z3 Ogg.z3) (Ogg.f9 Ogg.o3 Ogg.z3)) = refl
relativeFrobeniusIsConjugation (tower81 (Ogg.f9 Ogg.z3 Ogg.z3) (Ogg.f9 Ogg.o3 Ogg.o3)) = refl
relativeFrobeniusIsConjugation (tower81 (Ogg.f9 Ogg.z3 Ogg.z3) (Ogg.f9 Ogg.o3 Ogg.t3)) = refl
relativeFrobeniusIsConjugation (tower81 (Ogg.f9 Ogg.z3 Ogg.z3) (Ogg.f9 Ogg.t3 Ogg.z3)) = refl
relativeFrobeniusIsConjugation (tower81 (Ogg.f9 Ogg.z3 Ogg.z3) (Ogg.f9 Ogg.t3 Ogg.o3)) = refl
relativeFrobeniusIsConjugation (tower81 (Ogg.f9 Ogg.z3 Ogg.z3) (Ogg.f9 Ogg.t3 Ogg.t3)) = refl
relativeFrobeniusIsConjugation (tower81 (Ogg.f9 Ogg.z3 Ogg.o3) (Ogg.f9 Ogg.z3 Ogg.z3)) = refl
relativeFrobeniusIsConjugation (tower81 (Ogg.f9 Ogg.z3 Ogg.o3) (Ogg.f9 Ogg.z3 Ogg.o3)) = refl
relativeFrobeniusIsConjugation (tower81 (Ogg.f9 Ogg.z3 Ogg.o3) (Ogg.f9 Ogg.z3 Ogg.t3)) = refl
relativeFrobeniusIsConjugation (tower81 (Ogg.f9 Ogg.z3 Ogg.o3) (Ogg.f9 Ogg.o3 Ogg.z3)) = refl
relativeFrobeniusIsConjugation (tower81 (Ogg.f9 Ogg.z3 Ogg.o3) (Ogg.f9 Ogg.o3 Ogg.o3)) = refl
relativeFrobeniusIsConjugation (tower81 (Ogg.f9 Ogg.z3 Ogg.o3) (Ogg.f9 Ogg.o3 Ogg.t3)) = refl
relativeFrobeniusIsConjugation (tower81 (Ogg.f9 Ogg.z3 Ogg.o3) (Ogg.f9 Ogg.t3 Ogg.z3)) = refl
relativeFrobeniusIsConjugation (tower81 (Ogg.f9 Ogg.z3 Ogg.o3) (Ogg.f9 Ogg.t3 Ogg.o3)) = refl
relativeFrobeniusIsConjugation (tower81 (Ogg.f9 Ogg.z3 Ogg.o3) (Ogg.f9 Ogg.t3 Ogg.t3)) = refl
relativeFrobeniusIsConjugation (tower81 (Ogg.f9 Ogg.z3 Ogg.t3) (Ogg.f9 Ogg.z3 Ogg.z3)) = refl
relativeFrobeniusIsConjugation (tower81 (Ogg.f9 Ogg.z3 Ogg.t3) (Ogg.f9 Ogg.z3 Ogg.o3)) = refl
relativeFrobeniusIsConjugation (tower81 (Ogg.f9 Ogg.z3 Ogg.t3) (Ogg.f9 Ogg.z3 Ogg.t3)) = refl
relativeFrobeniusIsConjugation (tower81 (Ogg.f9 Ogg.z3 Ogg.t3) (Ogg.f9 Ogg.o3 Ogg.z3)) = refl
relativeFrobeniusIsConjugation (tower81 (Ogg.f9 Ogg.z3 Ogg.t3) (Ogg.f9 Ogg.o3 Ogg.o3)) = refl
relativeFrobeniusIsConjugation (tower81 (Ogg.f9 Ogg.z3 Ogg.t3) (Ogg.f9 Ogg.o3 Ogg.t3)) = refl
relativeFrobeniusIsConjugation (tower81 (Ogg.f9 Ogg.z3 Ogg.t3) (Ogg.f9 Ogg.t3 Ogg.z3)) = refl
relativeFrobeniusIsConjugation (tower81 (Ogg.f9 Ogg.z3 Ogg.t3) (Ogg.f9 Ogg.t3 Ogg.o3)) = refl
relativeFrobeniusIsConjugation (tower81 (Ogg.f9 Ogg.z3 Ogg.t3) (Ogg.f9 Ogg.t3 Ogg.t3)) = refl
relativeFrobeniusIsConjugation (tower81 (Ogg.f9 Ogg.o3 Ogg.z3) (Ogg.f9 Ogg.z3 Ogg.z3)) = refl
relativeFrobeniusIsConjugation (tower81 (Ogg.f9 Ogg.o3 Ogg.z3) (Ogg.f9 Ogg.z3 Ogg.o3)) = refl
relativeFrobeniusIsConjugation (tower81 (Ogg.f9 Ogg.o3 Ogg.z3) (Ogg.f9 Ogg.z3 Ogg.t3)) = refl
relativeFrobeniusIsConjugation (tower81 (Ogg.f9 Ogg.o3 Ogg.z3) (Ogg.f9 Ogg.o3 Ogg.z3)) = refl
relativeFrobeniusIsConjugation (tower81 (Ogg.f9 Ogg.o3 Ogg.z3) (Ogg.f9 Ogg.o3 Ogg.o3)) = refl
relativeFrobeniusIsConjugation (tower81 (Ogg.f9 Ogg.o3 Ogg.z3) (Ogg.f9 Ogg.o3 Ogg.t3)) = refl
relativeFrobeniusIsConjugation (tower81 (Ogg.f9 Ogg.o3 Ogg.z3) (Ogg.f9 Ogg.t3 Ogg.z3)) = refl
relativeFrobeniusIsConjugation (tower81 (Ogg.f9 Ogg.o3 Ogg.z3) (Ogg.f9 Ogg.t3 Ogg.o3)) = refl
relativeFrobeniusIsConjugation (tower81 (Ogg.f9 Ogg.o3 Ogg.z3) (Ogg.f9 Ogg.t3 Ogg.t3)) = refl
relativeFrobeniusIsConjugation (tower81 (Ogg.f9 Ogg.o3 Ogg.o3) (Ogg.f9 Ogg.z3 Ogg.z3)) = refl
relativeFrobeniusIsConjugation (tower81 (Ogg.f9 Ogg.o3 Ogg.o3) (Ogg.f9 Ogg.z3 Ogg.o3)) = refl
relativeFrobeniusIsConjugation (tower81 (Ogg.f9 Ogg.o3 Ogg.o3) (Ogg.f9 Ogg.z3 Ogg.t3)) = refl
relativeFrobeniusIsConjugation (tower81 (Ogg.f9 Ogg.o3 Ogg.o3) (Ogg.f9 Ogg.o3 Ogg.z3)) = refl
relativeFrobeniusIsConjugation (tower81 (Ogg.f9 Ogg.o3 Ogg.o3) (Ogg.f9 Ogg.o3 Ogg.o3)) = refl
relativeFrobeniusIsConjugation (tower81 (Ogg.f9 Ogg.o3 Ogg.o3) (Ogg.f9 Ogg.o3 Ogg.t3)) = refl
relativeFrobeniusIsConjugation (tower81 (Ogg.f9 Ogg.o3 Ogg.o3) (Ogg.f9 Ogg.t3 Ogg.z3)) = refl
relativeFrobeniusIsConjugation (tower81 (Ogg.f9 Ogg.o3 Ogg.o3) (Ogg.f9 Ogg.t3 Ogg.o3)) = refl
relativeFrobeniusIsConjugation (tower81 (Ogg.f9 Ogg.o3 Ogg.o3) (Ogg.f9 Ogg.t3 Ogg.t3)) = refl
relativeFrobeniusIsConjugation (tower81 (Ogg.f9 Ogg.o3 Ogg.t3) (Ogg.f9 Ogg.z3 Ogg.z3)) = refl
relativeFrobeniusIsConjugation (tower81 (Ogg.f9 Ogg.o3 Ogg.t3) (Ogg.f9 Ogg.z3 Ogg.o3)) = refl
relativeFrobeniusIsConjugation (tower81 (Ogg.f9 Ogg.o3 Ogg.t3) (Ogg.f9 Ogg.z3 Ogg.t3)) = refl
relativeFrobeniusIsConjugation (tower81 (Ogg.f9 Ogg.o3 Ogg.t3) (Ogg.f9 Ogg.o3 Ogg.z3)) = refl
relativeFrobeniusIsConjugation (tower81 (Ogg.f9 Ogg.o3 Ogg.t3) (Ogg.f9 Ogg.o3 Ogg.o3)) = refl
relativeFrobeniusIsConjugation (tower81 (Ogg.f9 Ogg.o3 Ogg.t3) (Ogg.f9 Ogg.o3 Ogg.t3)) = refl
relativeFrobeniusIsConjugation (tower81 (Ogg.f9 Ogg.o3 Ogg.t3) (Ogg.f9 Ogg.t3 Ogg.z3)) = refl
relativeFrobeniusIsConjugation (tower81 (Ogg.f9 Ogg.o3 Ogg.t3) (Ogg.f9 Ogg.t3 Ogg.o3)) = refl
relativeFrobeniusIsConjugation (tower81 (Ogg.f9 Ogg.o3 Ogg.t3) (Ogg.f9 Ogg.t3 Ogg.t3)) = refl
relativeFrobeniusIsConjugation (tower81 (Ogg.f9 Ogg.t3 Ogg.z3) (Ogg.f9 Ogg.z3 Ogg.z3)) = refl
relativeFrobeniusIsConjugation (tower81 (Ogg.f9 Ogg.t3 Ogg.z3) (Ogg.f9 Ogg.z3 Ogg.o3)) = refl
relativeFrobeniusIsConjugation (tower81 (Ogg.f9 Ogg.t3 Ogg.z3) (Ogg.f9 Ogg.z3 Ogg.t3)) = refl
relativeFrobeniusIsConjugation (tower81 (Ogg.f9 Ogg.t3 Ogg.z3) (Ogg.f9 Ogg.o3 Ogg.z3)) = refl
relativeFrobeniusIsConjugation (tower81 (Ogg.f9 Ogg.t3 Ogg.z3) (Ogg.f9 Ogg.o3 Ogg.o3)) = refl
relativeFrobeniusIsConjugation (tower81 (Ogg.f9 Ogg.t3 Ogg.z3) (Ogg.f9 Ogg.o3 Ogg.t3)) = refl
relativeFrobeniusIsConjugation (tower81 (Ogg.f9 Ogg.t3 Ogg.z3) (Ogg.f9 Ogg.t3 Ogg.z3)) = refl
relativeFrobeniusIsConjugation (tower81 (Ogg.f9 Ogg.t3 Ogg.z3) (Ogg.f9 Ogg.t3 Ogg.o3)) = refl
relativeFrobeniusIsConjugation (tower81 (Ogg.f9 Ogg.t3 Ogg.z3) (Ogg.f9 Ogg.t3 Ogg.t3)) = refl
relativeFrobeniusIsConjugation (tower81 (Ogg.f9 Ogg.t3 Ogg.o3) (Ogg.f9 Ogg.z3 Ogg.z3)) = refl
relativeFrobeniusIsConjugation (tower81 (Ogg.f9 Ogg.t3 Ogg.o3) (Ogg.f9 Ogg.z3 Ogg.o3)) = refl
relativeFrobeniusIsConjugation (tower81 (Ogg.f9 Ogg.t3 Ogg.o3) (Ogg.f9 Ogg.z3 Ogg.t3)) = refl
relativeFrobeniusIsConjugation (tower81 (Ogg.f9 Ogg.t3 Ogg.o3) (Ogg.f9 Ogg.o3 Ogg.z3)) = refl
relativeFrobeniusIsConjugation (tower81 (Ogg.f9 Ogg.t3 Ogg.o3) (Ogg.f9 Ogg.o3 Ogg.o3)) = refl
relativeFrobeniusIsConjugation (tower81 (Ogg.f9 Ogg.t3 Ogg.o3) (Ogg.f9 Ogg.o3 Ogg.t3)) = refl
relativeFrobeniusIsConjugation (tower81 (Ogg.f9 Ogg.t3 Ogg.o3) (Ogg.f9 Ogg.t3 Ogg.z3)) = refl
relativeFrobeniusIsConjugation (tower81 (Ogg.f9 Ogg.t3 Ogg.o3) (Ogg.f9 Ogg.t3 Ogg.o3)) = refl
relativeFrobeniusIsConjugation (tower81 (Ogg.f9 Ogg.t3 Ogg.o3) (Ogg.f9 Ogg.t3 Ogg.t3)) = refl
relativeFrobeniusIsConjugation (tower81 (Ogg.f9 Ogg.t3 Ogg.t3) (Ogg.f9 Ogg.z3 Ogg.z3)) = refl
relativeFrobeniusIsConjugation (tower81 (Ogg.f9 Ogg.t3 Ogg.t3) (Ogg.f9 Ogg.z3 Ogg.o3)) = refl
relativeFrobeniusIsConjugation (tower81 (Ogg.f9 Ogg.t3 Ogg.t3) (Ogg.f9 Ogg.z3 Ogg.t3)) = refl
relativeFrobeniusIsConjugation (tower81 (Ogg.f9 Ogg.t3 Ogg.t3) (Ogg.f9 Ogg.o3 Ogg.z3)) = refl
relativeFrobeniusIsConjugation (tower81 (Ogg.f9 Ogg.t3 Ogg.t3) (Ogg.f9 Ogg.o3 Ogg.o3)) = refl
relativeFrobeniusIsConjugation (tower81 (Ogg.f9 Ogg.t3 Ogg.t3) (Ogg.f9 Ogg.o3 Ogg.t3)) = refl
relativeFrobeniusIsConjugation (tower81 (Ogg.f9 Ogg.t3 Ogg.t3) (Ogg.f9 Ogg.t3 Ogg.z3)) = refl
relativeFrobeniusIsConjugation (tower81 (Ogg.f9 Ogg.t3 Ogg.t3) (Ogg.f9 Ogg.t3 Ogg.o3)) = refl
relativeFrobeniusIsConjugation (tower81 (Ogg.f9 Ogg.t3 Ogg.t3) (Ogg.f9 Ogg.t3 Ogg.t3)) = refl

normPower10IsQuadraticNorm :
  (x : Tower81) → power10 x ≡ quadraticNorm x
normPower10IsQuadraticNorm (tower81 (Ogg.f9 Ogg.z3 Ogg.z3) (Ogg.f9 Ogg.z3 Ogg.z3)) = refl
normPower10IsQuadraticNorm (tower81 (Ogg.f9 Ogg.z3 Ogg.z3) (Ogg.f9 Ogg.z3 Ogg.o3)) = refl
normPower10IsQuadraticNorm (tower81 (Ogg.f9 Ogg.z3 Ogg.z3) (Ogg.f9 Ogg.z3 Ogg.t3)) = refl
normPower10IsQuadraticNorm (tower81 (Ogg.f9 Ogg.z3 Ogg.z3) (Ogg.f9 Ogg.o3 Ogg.z3)) = refl
normPower10IsQuadraticNorm (tower81 (Ogg.f9 Ogg.z3 Ogg.z3) (Ogg.f9 Ogg.o3 Ogg.o3)) = refl
normPower10IsQuadraticNorm (tower81 (Ogg.f9 Ogg.z3 Ogg.z3) (Ogg.f9 Ogg.o3 Ogg.t3)) = refl
normPower10IsQuadraticNorm (tower81 (Ogg.f9 Ogg.z3 Ogg.z3) (Ogg.f9 Ogg.t3 Ogg.z3)) = refl
normPower10IsQuadraticNorm (tower81 (Ogg.f9 Ogg.z3 Ogg.z3) (Ogg.f9 Ogg.t3 Ogg.o3)) = refl
normPower10IsQuadraticNorm (tower81 (Ogg.f9 Ogg.z3 Ogg.z3) (Ogg.f9 Ogg.t3 Ogg.t3)) = refl
normPower10IsQuadraticNorm (tower81 (Ogg.f9 Ogg.z3 Ogg.o3) (Ogg.f9 Ogg.z3 Ogg.z3)) = refl
normPower10IsQuadraticNorm (tower81 (Ogg.f9 Ogg.z3 Ogg.o3) (Ogg.f9 Ogg.z3 Ogg.o3)) = refl
normPower10IsQuadraticNorm (tower81 (Ogg.f9 Ogg.z3 Ogg.o3) (Ogg.f9 Ogg.z3 Ogg.t3)) = refl
normPower10IsQuadraticNorm (tower81 (Ogg.f9 Ogg.z3 Ogg.o3) (Ogg.f9 Ogg.o3 Ogg.z3)) = refl
normPower10IsQuadraticNorm (tower81 (Ogg.f9 Ogg.z3 Ogg.o3) (Ogg.f9 Ogg.o3 Ogg.o3)) = refl
normPower10IsQuadraticNorm (tower81 (Ogg.f9 Ogg.z3 Ogg.o3) (Ogg.f9 Ogg.o3 Ogg.t3)) = refl
normPower10IsQuadraticNorm (tower81 (Ogg.f9 Ogg.z3 Ogg.o3) (Ogg.f9 Ogg.t3 Ogg.z3)) = refl
normPower10IsQuadraticNorm (tower81 (Ogg.f9 Ogg.z3 Ogg.o3) (Ogg.f9 Ogg.t3 Ogg.o3)) = refl
normPower10IsQuadraticNorm (tower81 (Ogg.f9 Ogg.z3 Ogg.o3) (Ogg.f9 Ogg.t3 Ogg.t3)) = refl
normPower10IsQuadraticNorm (tower81 (Ogg.f9 Ogg.z3 Ogg.t3) (Ogg.f9 Ogg.z3 Ogg.z3)) = refl
normPower10IsQuadraticNorm (tower81 (Ogg.f9 Ogg.z3 Ogg.t3) (Ogg.f9 Ogg.z3 Ogg.o3)) = refl
normPower10IsQuadraticNorm (tower81 (Ogg.f9 Ogg.z3 Ogg.t3) (Ogg.f9 Ogg.z3 Ogg.t3)) = refl
normPower10IsQuadraticNorm (tower81 (Ogg.f9 Ogg.z3 Ogg.t3) (Ogg.f9 Ogg.o3 Ogg.z3)) = refl
normPower10IsQuadraticNorm (tower81 (Ogg.f9 Ogg.z3 Ogg.t3) (Ogg.f9 Ogg.o3 Ogg.o3)) = refl
normPower10IsQuadraticNorm (tower81 (Ogg.f9 Ogg.z3 Ogg.t3) (Ogg.f9 Ogg.o3 Ogg.t3)) = refl
normPower10IsQuadraticNorm (tower81 (Ogg.f9 Ogg.z3 Ogg.t3) (Ogg.f9 Ogg.t3 Ogg.z3)) = refl
normPower10IsQuadraticNorm (tower81 (Ogg.f9 Ogg.z3 Ogg.t3) (Ogg.f9 Ogg.t3 Ogg.o3)) = refl
normPower10IsQuadraticNorm (tower81 (Ogg.f9 Ogg.z3 Ogg.t3) (Ogg.f9 Ogg.t3 Ogg.t3)) = refl
normPower10IsQuadraticNorm (tower81 (Ogg.f9 Ogg.o3 Ogg.z3) (Ogg.f9 Ogg.z3 Ogg.z3)) = refl
normPower10IsQuadraticNorm (tower81 (Ogg.f9 Ogg.o3 Ogg.z3) (Ogg.f9 Ogg.z3 Ogg.o3)) = refl
normPower10IsQuadraticNorm (tower81 (Ogg.f9 Ogg.o3 Ogg.z3) (Ogg.f9 Ogg.z3 Ogg.t3)) = refl
normPower10IsQuadraticNorm (tower81 (Ogg.f9 Ogg.o3 Ogg.z3) (Ogg.f9 Ogg.o3 Ogg.z3)) = refl
normPower10IsQuadraticNorm (tower81 (Ogg.f9 Ogg.o3 Ogg.z3) (Ogg.f9 Ogg.o3 Ogg.o3)) = refl
normPower10IsQuadraticNorm (tower81 (Ogg.f9 Ogg.o3 Ogg.z3) (Ogg.f9 Ogg.o3 Ogg.t3)) = refl
normPower10IsQuadraticNorm (tower81 (Ogg.f9 Ogg.o3 Ogg.z3) (Ogg.f9 Ogg.t3 Ogg.z3)) = refl
normPower10IsQuadraticNorm (tower81 (Ogg.f9 Ogg.o3 Ogg.z3) (Ogg.f9 Ogg.t3 Ogg.o3)) = refl
normPower10IsQuadraticNorm (tower81 (Ogg.f9 Ogg.o3 Ogg.z3) (Ogg.f9 Ogg.t3 Ogg.t3)) = refl
normPower10IsQuadraticNorm (tower81 (Ogg.f9 Ogg.o3 Ogg.o3) (Ogg.f9 Ogg.z3 Ogg.z3)) = refl
normPower10IsQuadraticNorm (tower81 (Ogg.f9 Ogg.o3 Ogg.o3) (Ogg.f9 Ogg.z3 Ogg.o3)) = refl
normPower10IsQuadraticNorm (tower81 (Ogg.f9 Ogg.o3 Ogg.o3) (Ogg.f9 Ogg.z3 Ogg.t3)) = refl
normPower10IsQuadraticNorm (tower81 (Ogg.f9 Ogg.o3 Ogg.o3) (Ogg.f9 Ogg.o3 Ogg.z3)) = refl
normPower10IsQuadraticNorm (tower81 (Ogg.f9 Ogg.o3 Ogg.o3) (Ogg.f9 Ogg.o3 Ogg.o3)) = refl
normPower10IsQuadraticNorm (tower81 (Ogg.f9 Ogg.o3 Ogg.o3) (Ogg.f9 Ogg.o3 Ogg.t3)) = refl
normPower10IsQuadraticNorm (tower81 (Ogg.f9 Ogg.o3 Ogg.o3) (Ogg.f9 Ogg.t3 Ogg.z3)) = refl
normPower10IsQuadraticNorm (tower81 (Ogg.f9 Ogg.o3 Ogg.o3) (Ogg.f9 Ogg.t3 Ogg.o3)) = refl
normPower10IsQuadraticNorm (tower81 (Ogg.f9 Ogg.o3 Ogg.o3) (Ogg.f9 Ogg.t3 Ogg.t3)) = refl
normPower10IsQuadraticNorm (tower81 (Ogg.f9 Ogg.o3 Ogg.t3) (Ogg.f9 Ogg.z3 Ogg.z3)) = refl
normPower10IsQuadraticNorm (tower81 (Ogg.f9 Ogg.o3 Ogg.t3) (Ogg.f9 Ogg.z3 Ogg.o3)) = refl
normPower10IsQuadraticNorm (tower81 (Ogg.f9 Ogg.o3 Ogg.t3) (Ogg.f9 Ogg.z3 Ogg.t3)) = refl
normPower10IsQuadraticNorm (tower81 (Ogg.f9 Ogg.o3 Ogg.t3) (Ogg.f9 Ogg.o3 Ogg.z3)) = refl
normPower10IsQuadraticNorm (tower81 (Ogg.f9 Ogg.o3 Ogg.t3) (Ogg.f9 Ogg.o3 Ogg.o3)) = refl
normPower10IsQuadraticNorm (tower81 (Ogg.f9 Ogg.o3 Ogg.t3) (Ogg.f9 Ogg.o3 Ogg.t3)) = refl
normPower10IsQuadraticNorm (tower81 (Ogg.f9 Ogg.o3 Ogg.t3) (Ogg.f9 Ogg.t3 Ogg.z3)) = refl
normPower10IsQuadraticNorm (tower81 (Ogg.f9 Ogg.o3 Ogg.t3) (Ogg.f9 Ogg.t3 Ogg.o3)) = refl
normPower10IsQuadraticNorm (tower81 (Ogg.f9 Ogg.o3 Ogg.t3) (Ogg.f9 Ogg.t3 Ogg.t3)) = refl
normPower10IsQuadraticNorm (tower81 (Ogg.f9 Ogg.t3 Ogg.z3) (Ogg.f9 Ogg.z3 Ogg.z3)) = refl
normPower10IsQuadraticNorm (tower81 (Ogg.f9 Ogg.t3 Ogg.z3) (Ogg.f9 Ogg.z3 Ogg.o3)) = refl
normPower10IsQuadraticNorm (tower81 (Ogg.f9 Ogg.t3 Ogg.z3) (Ogg.f9 Ogg.z3 Ogg.t3)) = refl
normPower10IsQuadraticNorm (tower81 (Ogg.f9 Ogg.t3 Ogg.z3) (Ogg.f9 Ogg.o3 Ogg.z3)) = refl
normPower10IsQuadraticNorm (tower81 (Ogg.f9 Ogg.t3 Ogg.z3) (Ogg.f9 Ogg.o3 Ogg.o3)) = refl
normPower10IsQuadraticNorm (tower81 (Ogg.f9 Ogg.t3 Ogg.z3) (Ogg.f9 Ogg.o3 Ogg.t3)) = refl
normPower10IsQuadraticNorm (tower81 (Ogg.f9 Ogg.t3 Ogg.z3) (Ogg.f9 Ogg.t3 Ogg.z3)) = refl
normPower10IsQuadraticNorm (tower81 (Ogg.f9 Ogg.t3 Ogg.z3) (Ogg.f9 Ogg.t3 Ogg.o3)) = refl
normPower10IsQuadraticNorm (tower81 (Ogg.f9 Ogg.t3 Ogg.z3) (Ogg.f9 Ogg.t3 Ogg.t3)) = refl
normPower10IsQuadraticNorm (tower81 (Ogg.f9 Ogg.t3 Ogg.o3) (Ogg.f9 Ogg.z3 Ogg.z3)) = refl
normPower10IsQuadraticNorm (tower81 (Ogg.f9 Ogg.t3 Ogg.o3) (Ogg.f9 Ogg.z3 Ogg.o3)) = refl
normPower10IsQuadraticNorm (tower81 (Ogg.f9 Ogg.t3 Ogg.o3) (Ogg.f9 Ogg.z3 Ogg.t3)) = refl
normPower10IsQuadraticNorm (tower81 (Ogg.f9 Ogg.t3 Ogg.o3) (Ogg.f9 Ogg.o3 Ogg.z3)) = refl
normPower10IsQuadraticNorm (tower81 (Ogg.f9 Ogg.t3 Ogg.o3) (Ogg.f9 Ogg.o3 Ogg.o3)) = refl
normPower10IsQuadraticNorm (tower81 (Ogg.f9 Ogg.t3 Ogg.o3) (Ogg.f9 Ogg.o3 Ogg.t3)) = refl
normPower10IsQuadraticNorm (tower81 (Ogg.f9 Ogg.t3 Ogg.o3) (Ogg.f9 Ogg.t3 Ogg.z3)) = refl
normPower10IsQuadraticNorm (tower81 (Ogg.f9 Ogg.t3 Ogg.o3) (Ogg.f9 Ogg.t3 Ogg.o3)) = refl
normPower10IsQuadraticNorm (tower81 (Ogg.f9 Ogg.t3 Ogg.o3) (Ogg.f9 Ogg.t3 Ogg.t3)) = refl
normPower10IsQuadraticNorm (tower81 (Ogg.f9 Ogg.t3 Ogg.t3) (Ogg.f9 Ogg.z3 Ogg.z3)) = refl
normPower10IsQuadraticNorm (tower81 (Ogg.f9 Ogg.t3 Ogg.t3) (Ogg.f9 Ogg.z3 Ogg.o3)) = refl
normPower10IsQuadraticNorm (tower81 (Ogg.f9 Ogg.t3 Ogg.t3) (Ogg.f9 Ogg.z3 Ogg.t3)) = refl
normPower10IsQuadraticNorm (tower81 (Ogg.f9 Ogg.t3 Ogg.t3) (Ogg.f9 Ogg.o3 Ogg.z3)) = refl
normPower10IsQuadraticNorm (tower81 (Ogg.f9 Ogg.t3 Ogg.t3) (Ogg.f9 Ogg.o3 Ogg.o3)) = refl
normPower10IsQuadraticNorm (tower81 (Ogg.f9 Ogg.t3 Ogg.t3) (Ogg.f9 Ogg.o3 Ogg.t3)) = refl
normPower10IsQuadraticNorm (tower81 (Ogg.f9 Ogg.t3 Ogg.t3) (Ogg.f9 Ogg.t3 Ogg.z3)) = refl
normPower10IsQuadraticNorm (tower81 (Ogg.f9 Ogg.t3 Ogg.t3) (Ogg.f9 Ogg.t3 Ogg.o3)) = refl
normPower10IsQuadraticNorm (tower81 (Ogg.f9 Ogg.t3 Ogg.t3) (Ogg.f9 Ogg.t3 Ogg.t3)) = refl

quarticPuncturedFermat80 :
  (p : K4.PuncturedKernel4) →
  power80 (fromOriginalKernel4 (proj₁ p)) ≡ one81
quarticPuncturedFermat80 ((Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , ())
quarticPuncturedFermat80 ((Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedFermat80 ((Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedFermat80 ((Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedFermat80 ((Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedFermat80 ((Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedFermat80 ((Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedFermat80 ((Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedFermat80 ((Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedFermat80 ((Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedFermat80 ((Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedFermat80 ((Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedFermat80 ((Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedFermat80 ((Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedFermat80 ((Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedFermat80 ((Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedFermat80 ((Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedFermat80 ((Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedFermat80 ((Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedFermat80 ((Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedFermat80 ((Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedFermat80 ((Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedFermat80 ((Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedFermat80 ((Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedFermat80 ((Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedFermat80 ((Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedFermat80 ((Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedFermat80 ((Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedFermat80 ((Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedFermat80 ((Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedFermat80 ((Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedFermat80 ((Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedFermat80 ((Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedFermat80 ((Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedFermat80 ((Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedFermat80 ((Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedFermat80 ((Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedFermat80 ((Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedFermat80 ((Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedFermat80 ((Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedFermat80 ((Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedFermat80 ((Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedFermat80 ((Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedFermat80 ((Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedFermat80 ((Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedFermat80 ((Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedFermat80 ((Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedFermat80 ((Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedFermat80 ((Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedFermat80 ((Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedFermat80 ((Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedFermat80 ((Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedFermat80 ((Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedFermat80 ((Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedFermat80 ((Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedFermat80 ((Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedFermat80 ((Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedFermat80 ((Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedFermat80 ((Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedFermat80 ((Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedFermat80 ((Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedFermat80 ((Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedFermat80 ((Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedFermat80 ((Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedFermat80 ((Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedFermat80 ((Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedFermat80 ((Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedFermat80 ((Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedFermat80 ((Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedFermat80 ((Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedFermat80 ((Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedFermat80 ((Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedFermat80 ((Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedFermat80 ((Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedFermat80 ((Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedFermat80 ((Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedFermat80 ((Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedFermat80 ((Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedFermat80 ((Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedFermat80 ((Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedFermat80 ((Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , _) = refl

quarticPuncturedInverse79 :
  (p : K4.PuncturedKernel4) →
  times81 (fromOriginalKernel4 (proj₁ p))
    (power79 (fromOriginalKernel4 (proj₁ p))) ≡ one81
quarticPuncturedInverse79 ((Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , ())
quarticPuncturedInverse79 ((Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedInverse79 ((Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedInverse79 ((Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedInverse79 ((Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedInverse79 ((Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedInverse79 ((Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedInverse79 ((Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedInverse79 ((Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedInverse79 ((Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedInverse79 ((Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedInverse79 ((Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedInverse79 ((Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedInverse79 ((Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedInverse79 ((Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedInverse79 ((Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedInverse79 ((Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedInverse79 ((Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedInverse79 ((Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedInverse79 ((Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedInverse79 ((Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedInverse79 ((Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedInverse79 ((Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedInverse79 ((Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedInverse79 ((Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedInverse79 ((Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedInverse79 ((Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedInverse79 ((Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedInverse79 ((Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedInverse79 ((Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedInverse79 ((Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedInverse79 ((Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedInverse79 ((Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedInverse79 ((Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedInverse79 ((Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedInverse79 ((Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedInverse79 ((Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedInverse79 ((Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedInverse79 ((Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedInverse79 ((Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedInverse79 ((Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedInverse79 ((Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedInverse79 ((Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedInverse79 ((Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedInverse79 ((Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedInverse79 ((Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedInverse79 ((Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedInverse79 ((Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedInverse79 ((Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedInverse79 ((Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedInverse79 ((Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedInverse79 ((Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedInverse79 ((Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedInverse79 ((Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedInverse79 ((Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedInverse79 ((Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedInverse79 ((Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedInverse79 ((Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedInverse79 ((Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedInverse79 ((Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedInverse79 ((Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedInverse79 ((Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedInverse79 ((Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedInverse79 ((Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedInverse79 ((Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedInverse79 ((Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedInverse79 ((Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedInverse79 ((Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedInverse79 ((Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedInverse79 ((Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedInverse79 ((Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedInverse79 ((Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedInverse79 ((Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedInverse79 ((Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedInverse79 ((Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedInverse79 ((Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedInverse79 ((Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedInverse79 ((Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedInverse79 ((Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedInverse79 ((Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , _) = refl
quarticPuncturedInverse79 ((Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , _) = refl

-- Source proof authority: these are Agda source-written cases, not a
-- recorded exact-head kernel run. An independent finite arithmetic program
-- has checked the original F81 polynomial↔tower operations exhaustively.
-- Higher-order claims (Monster, classical moduli, physics, IIT) remain open.


------------------------------------------------------------------------
-- Relative norm-one / Galois inversion on the ACTUAL punctured source.
-- x^8 maps F81× into the norm-one C10 subgroup, so x^(8*10)=1.
-- Under the relative Frobenius9, these norm-one values invert.
-- 79 is not a numerical inverse of the integer 81; in F3, integer 81=0.
------------------------------------------------------------------------

power8ImageHasNormOne :
  (p : K4.PuncturedKernel4) →
  power10 (power8 (fromOriginalKernel4 (proj₁ p))) ≡ one81
power8ImageHasNormOne ((Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , ())
power8ImageHasNormOne ((Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
power8ImageHasNormOne ((Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl
power8ImageHasNormOne ((Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) = refl
power8ImageHasNormOne ((Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
power8ImageHasNormOne ((Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl
power8ImageHasNormOne ((Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) = refl
power8ImageHasNormOne ((Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
power8ImageHasNormOne ((Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl
power8ImageHasNormOne ((Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) = refl
power8ImageHasNormOne ((Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
power8ImageHasNormOne ((Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl
power8ImageHasNormOne ((Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) = refl
power8ImageHasNormOne ((Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
power8ImageHasNormOne ((Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl
power8ImageHasNormOne ((Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) = refl
power8ImageHasNormOne ((Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
power8ImageHasNormOne ((Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl
power8ImageHasNormOne ((Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) = refl
power8ImageHasNormOne ((Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
power8ImageHasNormOne ((Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl
power8ImageHasNormOne ((Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) = refl
power8ImageHasNormOne ((Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
power8ImageHasNormOne ((Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl
power8ImageHasNormOne ((Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) = refl
power8ImageHasNormOne ((Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
power8ImageHasNormOne ((Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl
power8ImageHasNormOne ((Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) = refl
power8ImageHasNormOne ((Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
power8ImageHasNormOne ((Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl
power8ImageHasNormOne ((Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) = refl
power8ImageHasNormOne ((Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
power8ImageHasNormOne ((Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl
power8ImageHasNormOne ((Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) = refl
power8ImageHasNormOne ((Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
power8ImageHasNormOne ((Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl
power8ImageHasNormOne ((Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) = refl
power8ImageHasNormOne ((Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
power8ImageHasNormOne ((Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl
power8ImageHasNormOne ((Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) = refl
power8ImageHasNormOne ((Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
power8ImageHasNormOne ((Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl
power8ImageHasNormOne ((Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) = refl
power8ImageHasNormOne ((Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
power8ImageHasNormOne ((Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl
power8ImageHasNormOne ((Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) = refl
power8ImageHasNormOne ((Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
power8ImageHasNormOne ((Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl
power8ImageHasNormOne ((Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) = refl
power8ImageHasNormOne ((Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
power8ImageHasNormOne ((Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl
power8ImageHasNormOne ((Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) = refl
power8ImageHasNormOne ((Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
power8ImageHasNormOne ((Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl
power8ImageHasNormOne ((Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) = refl
power8ImageHasNormOne ((Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
power8ImageHasNormOne ((Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl
power8ImageHasNormOne ((Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) = refl
power8ImageHasNormOne ((Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
power8ImageHasNormOne ((Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl
power8ImageHasNormOne ((Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) = refl
power8ImageHasNormOne ((Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
power8ImageHasNormOne ((Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl
power8ImageHasNormOne ((Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) = refl
power8ImageHasNormOne ((Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
power8ImageHasNormOne ((Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl
power8ImageHasNormOne ((Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) = refl
power8ImageHasNormOne ((Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
power8ImageHasNormOne ((Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl
power8ImageHasNormOne ((Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) = refl
power8ImageHasNormOne ((Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
power8ImageHasNormOne ((Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl
power8ImageHasNormOne ((Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) = refl
power8ImageHasNormOne ((Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
power8ImageHasNormOne ((Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl
power8ImageHasNormOne ((Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) = refl
power8ImageHasNormOne ((Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
power8ImageHasNormOne ((Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl
power8ImageHasNormOne ((Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) = refl
power8ImageHasNormOne ((Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
power8ImageHasNormOne ((Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl


relativeFrobeniusInvertsProjectiveImage :
  (p : K4.PuncturedKernel4) →
  power9 (power8 (fromOriginalKernel4 (proj₁ p)))
  ≡ power79 (power8 (fromOriginalKernel4 (proj₁ p)))
relativeFrobeniusInvertsProjectiveImage ((Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , ())
relativeFrobeniusInvertsProjectiveImage ((Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
relativeFrobeniusInvertsProjectiveImage ((Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl
relativeFrobeniusInvertsProjectiveImage ((Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) = refl
relativeFrobeniusInvertsProjectiveImage ((Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
relativeFrobeniusInvertsProjectiveImage ((Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl
relativeFrobeniusInvertsProjectiveImage ((Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) = refl
relativeFrobeniusInvertsProjectiveImage ((Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
relativeFrobeniusInvertsProjectiveImage ((Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl
relativeFrobeniusInvertsProjectiveImage ((Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) = refl
relativeFrobeniusInvertsProjectiveImage ((Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
relativeFrobeniusInvertsProjectiveImage ((Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl
relativeFrobeniusInvertsProjectiveImage ((Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) = refl
relativeFrobeniusInvertsProjectiveImage ((Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
relativeFrobeniusInvertsProjectiveImage ((Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl
relativeFrobeniusInvertsProjectiveImage ((Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) = refl
relativeFrobeniusInvertsProjectiveImage ((Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
relativeFrobeniusInvertsProjectiveImage ((Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl
relativeFrobeniusInvertsProjectiveImage ((Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) = refl
relativeFrobeniusInvertsProjectiveImage ((Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
relativeFrobeniusInvertsProjectiveImage ((Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl
relativeFrobeniusInvertsProjectiveImage ((Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) = refl
relativeFrobeniusInvertsProjectiveImage ((Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
relativeFrobeniusInvertsProjectiveImage ((Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl
relativeFrobeniusInvertsProjectiveImage ((Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) = refl
relativeFrobeniusInvertsProjectiveImage ((Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
relativeFrobeniusInvertsProjectiveImage ((Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl
relativeFrobeniusInvertsProjectiveImage ((Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) = refl
relativeFrobeniusInvertsProjectiveImage ((Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
relativeFrobeniusInvertsProjectiveImage ((Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl
relativeFrobeniusInvertsProjectiveImage ((Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) = refl
relativeFrobeniusInvertsProjectiveImage ((Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
relativeFrobeniusInvertsProjectiveImage ((Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl
relativeFrobeniusInvertsProjectiveImage ((Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) = refl
relativeFrobeniusInvertsProjectiveImage ((Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
relativeFrobeniusInvertsProjectiveImage ((Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl
relativeFrobeniusInvertsProjectiveImage ((Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) = refl
relativeFrobeniusInvertsProjectiveImage ((Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
relativeFrobeniusInvertsProjectiveImage ((Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl
relativeFrobeniusInvertsProjectiveImage ((Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) = refl
relativeFrobeniusInvertsProjectiveImage ((Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
relativeFrobeniusInvertsProjectiveImage ((Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl
relativeFrobeniusInvertsProjectiveImage ((Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) = refl
relativeFrobeniusInvertsProjectiveImage ((Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
relativeFrobeniusInvertsProjectiveImage ((Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl
relativeFrobeniusInvertsProjectiveImage ((Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) = refl
relativeFrobeniusInvertsProjectiveImage ((Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
relativeFrobeniusInvertsProjectiveImage ((Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl
relativeFrobeniusInvertsProjectiveImage ((Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) = refl
relativeFrobeniusInvertsProjectiveImage ((Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
relativeFrobeniusInvertsProjectiveImage ((Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl
relativeFrobeniusInvertsProjectiveImage ((Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) = refl
relativeFrobeniusInvertsProjectiveImage ((Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
relativeFrobeniusInvertsProjectiveImage ((Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl
relativeFrobeniusInvertsProjectiveImage ((Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) = refl
relativeFrobeniusInvertsProjectiveImage ((Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
relativeFrobeniusInvertsProjectiveImage ((Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl
relativeFrobeniusInvertsProjectiveImage ((Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) = refl
relativeFrobeniusInvertsProjectiveImage ((Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
relativeFrobeniusInvertsProjectiveImage ((Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl
relativeFrobeniusInvertsProjectiveImage ((Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) = refl
relativeFrobeniusInvertsProjectiveImage ((Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
relativeFrobeniusInvertsProjectiveImage ((Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl
relativeFrobeniusInvertsProjectiveImage ((Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) = refl
relativeFrobeniusInvertsProjectiveImage ((Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
relativeFrobeniusInvertsProjectiveImage ((Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl
relativeFrobeniusInvertsProjectiveImage ((Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) = refl
relativeFrobeniusInvertsProjectiveImage ((Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
relativeFrobeniusInvertsProjectiveImage ((Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl
relativeFrobeniusInvertsProjectiveImage ((Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) = refl
relativeFrobeniusInvertsProjectiveImage ((Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
relativeFrobeniusInvertsProjectiveImage ((Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl
relativeFrobeniusInvertsProjectiveImage ((Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) = refl
relativeFrobeniusInvertsProjectiveImage ((Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
relativeFrobeniusInvertsProjectiveImage ((Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl
relativeFrobeniusInvertsProjectiveImage ((Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) = refl
relativeFrobeniusInvertsProjectiveImage ((Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
relativeFrobeniusInvertsProjectiveImage ((Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl
relativeFrobeniusInvertsProjectiveImage ((Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) = refl
relativeFrobeniusInvertsProjectiveImage ((Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
relativeFrobeniusInvertsProjectiveImage ((Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl


exponent79IsInvolutiveOnUnits :
  (p : K4.PuncturedKernel4) →
  power79 (power79 (fromOriginalKernel4 (proj₁ p)))
  ≡ fromOriginalKernel4 (proj₁ p)
exponent79IsInvolutiveOnUnits ((Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , ())
exponent79IsInvolutiveOnUnits ((Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
exponent79IsInvolutiveOnUnits ((Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl
exponent79IsInvolutiveOnUnits ((Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) = refl
exponent79IsInvolutiveOnUnits ((Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
exponent79IsInvolutiveOnUnits ((Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl
exponent79IsInvolutiveOnUnits ((Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) = refl
exponent79IsInvolutiveOnUnits ((Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
exponent79IsInvolutiveOnUnits ((Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl
exponent79IsInvolutiveOnUnits ((Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) = refl
exponent79IsInvolutiveOnUnits ((Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
exponent79IsInvolutiveOnUnits ((Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl
exponent79IsInvolutiveOnUnits ((Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) = refl
exponent79IsInvolutiveOnUnits ((Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
exponent79IsInvolutiveOnUnits ((Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl
exponent79IsInvolutiveOnUnits ((Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) = refl
exponent79IsInvolutiveOnUnits ((Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
exponent79IsInvolutiveOnUnits ((Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl
exponent79IsInvolutiveOnUnits ((Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) = refl
exponent79IsInvolutiveOnUnits ((Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
exponent79IsInvolutiveOnUnits ((Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl
exponent79IsInvolutiveOnUnits ((Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) = refl
exponent79IsInvolutiveOnUnits ((Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
exponent79IsInvolutiveOnUnits ((Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl
exponent79IsInvolutiveOnUnits ((Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) = refl
exponent79IsInvolutiveOnUnits ((Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
exponent79IsInvolutiveOnUnits ((Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl
exponent79IsInvolutiveOnUnits ((Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) = refl
exponent79IsInvolutiveOnUnits ((Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
exponent79IsInvolutiveOnUnits ((Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl
exponent79IsInvolutiveOnUnits ((Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) = refl
exponent79IsInvolutiveOnUnits ((Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
exponent79IsInvolutiveOnUnits ((Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl
exponent79IsInvolutiveOnUnits ((Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) = refl
exponent79IsInvolutiveOnUnits ((Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
exponent79IsInvolutiveOnUnits ((Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl
exponent79IsInvolutiveOnUnits ((Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) = refl
exponent79IsInvolutiveOnUnits ((Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
exponent79IsInvolutiveOnUnits ((Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl
exponent79IsInvolutiveOnUnits ((Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) = refl
exponent79IsInvolutiveOnUnits ((Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
exponent79IsInvolutiveOnUnits ((Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl
exponent79IsInvolutiveOnUnits ((Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) = refl
exponent79IsInvolutiveOnUnits ((Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
exponent79IsInvolutiveOnUnits ((Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl
exponent79IsInvolutiveOnUnits ((Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) = refl
exponent79IsInvolutiveOnUnits ((Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
exponent79IsInvolutiveOnUnits ((Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl
exponent79IsInvolutiveOnUnits ((Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) = refl
exponent79IsInvolutiveOnUnits ((Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
exponent79IsInvolutiveOnUnits ((Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl
exponent79IsInvolutiveOnUnits ((Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) = refl
exponent79IsInvolutiveOnUnits ((Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
exponent79IsInvolutiveOnUnits ((Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl
exponent79IsInvolutiveOnUnits ((Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) = refl
exponent79IsInvolutiveOnUnits ((Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
exponent79IsInvolutiveOnUnits ((Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl
exponent79IsInvolutiveOnUnits ((Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) = refl
exponent79IsInvolutiveOnUnits ((Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
exponent79IsInvolutiveOnUnits ((Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl
exponent79IsInvolutiveOnUnits ((Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) = refl
exponent79IsInvolutiveOnUnits ((Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
exponent79IsInvolutiveOnUnits ((Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl
exponent79IsInvolutiveOnUnits ((Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) = refl
exponent79IsInvolutiveOnUnits ((Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
exponent79IsInvolutiveOnUnits ((Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl
exponent79IsInvolutiveOnUnits ((Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) = refl
exponent79IsInvolutiveOnUnits ((Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
exponent79IsInvolutiveOnUnits ((Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl
exponent79IsInvolutiveOnUnits ((Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) = refl
exponent79IsInvolutiveOnUnits ((Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
exponent79IsInvolutiveOnUnits ((Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl
exponent79IsInvolutiveOnUnits ((Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) = refl
exponent79IsInvolutiveOnUnits ((Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
exponent79IsInvolutiveOnUnits ((Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl
exponent79IsInvolutiveOnUnits ((Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) = refl
exponent79IsInvolutiveOnUnits ((Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
exponent79IsInvolutiveOnUnits ((Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl
exponent79IsInvolutiveOnUnits ((Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) = refl
exponent79IsInvolutiveOnUnits ((Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
exponent79IsInvolutiveOnUnits ((Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl
