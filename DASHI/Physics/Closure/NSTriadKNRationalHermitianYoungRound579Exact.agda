module DASHI.Physics.Closure.NSTriadKNRationalHermitianYoungRound579Exact where

------------------------------------------------------------------------
-- ROUND579 / SQUARE-ROOT-FREE LOCAL HERMITIAN YOUNG ENVELOPE
--
-- For the exact rational C^3 carrier, prove the deliberately loose but useful
-- local inequality
--
--   | Re <u,v> | <= ||u||^2 + ||v||^2.
--
-- The proof uses only R179 polarization and nonnegativity of the squared norms
-- of u+v and u-v.  No square root, norm (as opposed to norm-squared), spectral
-- theorem, or analytic Cauchy authority is introduced.
--
-- IMPORTANT: this is a LOCAL two-cell envelope only.  R179 already warns that
-- a mass-only envelope can recreate multiplicity when summed over a coherent
-- same-output fibre.  Therefore this owner does NOT claim the R29 cross-shell
-- decay certificate or leaf-A closure.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; -_; ∣_∣)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNRationalComplex3Separation as Separation
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramRound179Exact as R179

F = R179.F

two : ℚ
two = 1ℚ + 1ℚ

negVector : C3.Complex3 F → C3.Complex3 F
negVector = C3.complex3Negate

negVectorNormSquared :
  (v : C3.Complex3 F) →
  L2.complex3NormSquared (negVector v)
  ≡ L2.complex3NormSquared v
negVectorNormSquared
    (C3.complex3
      (C3.complex vx vxi) (C3.complex vy vyi) (C3.complex vz vzi)) =
  solve (vx ∷ vxi ∷ vy ∷ vyi ∷ vz ∷ vzi ∷ [])

realCrossNegRight :
  (u v : C3.Complex3 F) →
  R179.realHermitianCross u (negVector v)
  ≡ - (R179.realHermitianCross u v)
realCrossNegRight
    (C3.complex3
      (C3.complex ux uxi) (C3.complex uy uyi) (C3.complex uz uzi))
    (C3.complex3
      (C3.complex vx vxi) (C3.complex vy vyi) (C3.complex vz vzi)) =
  solve
    ( ux ∷ uxi ∷ uy ∷ uyi ∷ uz ∷ uzi
    ∷ vx ∷ vxi ∷ vy ∷ vyi ∷ vz ∷ vzi ∷ [])

-- Nonnegativity of ||u-v||^2 gives 2 Re<u,v> <= ||u||^2+||v||^2.
twoRealCrossUpper :
  (u v : C3.Complex3 F) →
  two * R179.realHermitianCross u v
  ≤ L2.complex3NormSquared u + L2.complex3NormSquared v
twoRealCrossUpper u v =
  let
    x = L2.complex3NormSquared u
    y = L2.complex3NormSquared v
    c = R179.realHermitianCross u v

    minusNN :
      0ℚ ≤ L2.complex3NormSquared (C3.complex3Add u (negVector v))
    minusNN = Separation.complex3NormSquaredNonnegative _

    minusMeaning :
      L2.complex3NormSquared (C3.complex3Add u (negVector v))
      ≡ x + y + two * (- c)
    minusMeaning =
      trans
        (R179.complex3Polarization u (negVector v))
        (trans
          (cong
            (λ yn → x + yn + two * R179.realHermitianCross u (negVector v))
            (negVectorNormSquared v))
          (cong (λ cn → x + y + two * cn) (realCrossNegRight u v)))

    base : 0ℚ ≤ x + y + two * (- c)
    base = subst (0ℚ ≤_) minusMeaning minusNN

    shifted : two * c + 0ℚ ≤ two * c + (x + y + two * (- c))
    shifted = ℚP.+-monoʳ-≤ (two * c) base
  in
  subst
    (two * c ≤_)
    (solve (x ∷ y ∷ c ∷ []))
    shifted

-- Nonnegativity of ||u+v||^2 gives -2 Re<u,v> <= ||u||^2+||v||^2.
negTwoRealCrossUpper :
  (u v : C3.Complex3 F) →
  - (two * R179.realHermitianCross u v)
  ≤ L2.complex3NormSquared u + L2.complex3NormSquared v
negTwoRealCrossUpper u v =
  let
    x = L2.complex3NormSquared u
    y = L2.complex3NormSquared v
    c = R179.realHermitianCross u v

    plusNN : 0ℚ ≤ L2.complex3NormSquared (C3.complex3Add u v)
    plusNN = Separation.complex3NormSquaredNonnegative _

    plusMeaning :
      L2.complex3NormSquared (C3.complex3Add u v)
      ≡ x + y + two * c
    plusMeaning = R179.complex3Polarization u v

    base : 0ℚ ≤ x + y + two * c
    base = subst (0ℚ ≤_) plusMeaning plusNN

    shifted : (-(two * c)) + 0ℚ ≤ (-(two * c)) + (x + y + two * c)
    shifted = ℚP.+-monoʳ-≤ (-(two * c)) base
  in
  subst
    ((-(two * c)) ≤_)
    (solve (x ∷ y ∷ c ∷ []))
    shifted

-- If z is nonnegative then z <= 2z.  Kept explicit so no division by two is
-- needed anywhere in the final Young envelope.
nonnegativeBelowDouble :
  (z : ℚ) → 0ℚ ≤ z → z ≤ two * z
nonnegativeBelowDouble z zNN =
  let
    added : z + 0ℚ ≤ z + z
    added = ℚP.+-monoʳ-≤ z zNN
  in
  subst (z ≤_) (solve (z ∷ [])) added

rationalRealHermitianYoung :
  (u v : C3.Complex3 F) →
  ∣ R179.realHermitianCross u v ∣
  ≤ L2.complex3NormSquared u + L2.complex3NormSquared v
rationalRealHermitianYoung u v
  with ℚP.∣p∣≡p∨∣p∣≡-p (R179.realHermitianCross u v)
... | inj₁ absIsPositive =
  let
    c = R179.realHermitianCross u v
    absNN : 0ℚ ≤ ∣ c ∣
    absNN = ℚP.0≤∣p∣ c
    cNN : 0ℚ ≤ c
    cNN = subst (0ℚ ≤_) absIsPositive absNN
    cBelowTwo = nonnegativeBelowDouble c cNN
    cBelowMass = ℚP.≤-trans cBelowTwo (twoRealCrossUpper u v)
  in
  subst
    (_≤ L2.complex3NormSquared u + L2.complex3NormSquared v)
    (sym absIsPositive)
    cBelowMass
... | inj₂ absIsNegative =
  let
    c = R179.realHermitianCross u v
    absNN : 0ℚ ≤ ∣ c ∣
    absNN = ℚP.0≤∣p∣ c
    negCNN : 0ℚ ≤ - c
    negCNN = subst (0ℚ ≤_) absIsNegative absNN
    negCBelowDouble : - c ≤ two * (- c)
    negCBelowDouble = nonnegativeBelowDouble (- c) negCNN
    doubleMeaning : two * (- c) ≡ - (two * c)
    doubleMeaning = solve (c ∷ [])
    negCBelowMass : - c ≤ L2.complex3NormSquared u + L2.complex3NormSquared v
    negCBelowMass =
      ℚP.≤-trans
        negCBelowDouble
        (subst
          (_≤ L2.complex3NormSquared u + L2.complex3NormSquared v)
          doubleMeaning
          (negTwoRealCrossUpper u v))
  in
  subst
    (_≤ L2.complex3NormSquared u + L2.complex3NormSquared v)
    (sym absIsNegative)
    negCBelowMass

round579SquareRootUsed : Bool
round579SquareRootUsed = false

round579LocalHermitianEnvelopeClosed : Bool
round579LocalHermitianEnvelopeClosed = true

round579CrossShellDecayCertificateClosed : Bool
round579CrossShellDecayCertificateClosed = false

round579LeafAClosed : Bool
round579LeafAClosed = false

round579ClayPromotion : Bool
round579ClayPromotion = false

round579LocalHermitianEnvelopeClosedIsTrue :
  round579LocalHermitianEnvelopeClosed ≡ true
round579LocalHermitianEnvelopeClosedIsTrue = refl

round579ClayPromotionIsFalse : round579ClayPromotion ≡ false
round579ClayPromotionIsFalse = refl
