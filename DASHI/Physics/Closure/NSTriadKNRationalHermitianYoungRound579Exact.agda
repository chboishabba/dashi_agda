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

-- The two directed inequalities needed by the absolute-value case split.
realCrossUpper :
  (u v : C3.Complex3 F) →
  R179.realHermitianCross u v
  ≤ L2.complex3NormSquared u + L2.complex3NormSquared v
realCrossUpper u v =
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

    directed : two * c ≤ x + y
    directed =
      let
        base : 0ℚ ≤ x + y + two * (- c)
        base = subst (0ℚ ≤_) minusMeaning minusNN
        shifted = ℚP.+-monoʳ-≤ (two * c) base
      in
      subst
        (two * c ≤_)
        (solve (x ∷ y ∷ c ∷ []))
        shifted

    cNNFromAbs : 0ℚ ≤ c → c ≤ two * c
    cNNFromAbs cNN =
      let
        added : c + 0ℚ ≤ c + c
        added = ℚP.+-monoˡ-≤ c cNN
      in
      subst (c ≤_) (solve (c ∷ [])) added
  in
  -- If c<0 the desired upper bound is automatic from nonnegative x+y; if
  -- c>=0, c<=2c and the stronger directed estimate applies.
  case ℚP.0≤? c of λ where
    (yes cNN) → ℚP.≤-trans (cNNFromAbs cNN) directed
    (no notCNN) →
      let
        cNonPos : c ≤ 0ℚ
        cNonPos = ℚP.≰⇒≥ notCNN
        sumNN = ℚP.+-mono-≤
          (Separation.complex3NormSquaredNonnegative u)
          (Separation.complex3NormSquaredNonnegative v)
      in ℚP.≤-trans cNonPos sumNN
  where
  open import Relation.Nullary.Decidable.Core using (yes; no)
  case : ∀ {a b : Set} → a → (a → b) → b
  case x f = f x

negRealCrossUpper :
  (u v : C3.Complex3 F) →
  - (R179.realHermitianCross u v)
  ≤ L2.complex3NormSquared u + L2.complex3NormSquared v
negRealCrossUpper u v =
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
    shifted = ℚP.+-monoʳ-≤ (-(two * c)) base
    directed : -(two * c) ≤ x + y
    directed = subst (_≤ x + y) (solve (c ∷ [])) shifted

    negCNN : 0ℚ ≤ - c → - c ≤ -(two * c)
    negCNN ncNN =
      let
        added : (- c) + 0ℚ ≤ (- c) + (- c)
        added = ℚP.+-monoˡ-≤ (- c) ncNN
      in subst ((- c) ≤_) (solve (c ∷ [])) added
  in
  case ℚP.0≤? (- c) of λ where
    (yes ncNN) → ℚP.≤-trans (negCNN ncNN) directed
    (no notNCNN) →
      let
        negCNonPos : - c ≤ 0ℚ
        negCNonPos = ℚP.≰⇒≥ notNCNN
        sumNN = ℚP.+-mono-≤
          (Separation.complex3NormSquaredNonnegative u)
          (Separation.complex3NormSquaredNonnegative v)
      in ℚP.≤-trans negCNonPos sumNN
  where
  open import Relation.Nullary.Decidable.Core using (yes; no)
  case : ∀ {a b : Set} → a → (a → b) → b
  case x f = f x

rationalRealHermitianYoung :
  (u v : C3.Complex3 F) →
  ∣ R179.realHermitianCross u v ∣
  ≤ L2.complex3NormSquared u + L2.complex3NormSquared v
rationalRealHermitianYoung u v
  with ℚP.∣p∣≡p∨∣p∣≡-p (R179.realHermitianCross u v)
... | inj₁ absIsPositive =
  subst
    (_≤ L2.complex3NormSquared u + L2.complex3NormSquared v)
    (sym absIsPositive)
    (realCrossUpper u v)
... | inj₂ absIsNegative =
  subst
    (_≤ L2.complex3NormSquared u + L2.complex3NormSquared v)
    (sym absIsNegative)
    (negRealCrossUpper u v)

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
