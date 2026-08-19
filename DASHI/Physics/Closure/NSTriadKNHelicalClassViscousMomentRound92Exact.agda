module DASHI.Physics.Closure.NSTriadKNHelicalClassViscousMomentRound92Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCE / CONTEXT
--
-- Author: Fabian Waleffe.
-- Title: "The nature of triad interactions in homogeneous turbulence".
-- Physics of Fluids A 4 (1992), 350--363.
-- DOI: 10.1063/1.858309.
--
-- ROUND92 / FOUR HELICAL SIGN CLASSES
--
-- Simultaneous reversal of all three helicity signs leaves the signed-helicity
-- conservation equation equivalent, so there are four essential sign classes.
-- For p <= q <= r and modal nonlinear energy transfers Tp,Tq,Tr, impose
--
--   E = Tp + Tq + Tr = 0
--
-- and the class-specific signed-helicity invariant.  Then the Laplacian-
-- weighted transfer W = p^2 Tp + q^2 Tq + r^2 Tr collapses exactly to:
--
--   +++ :  W = +(q-p)(r-p) Tp
--   ++- :  W = -(q-p)(p+r) Tp
--   +-+ :  W = -(p+q)(r-p) Tp
--   +-- :  W = +(p+q)(p+r) Tp.
--
-- Thus the coefficient has positive sign exactly when the TWO HIGHER legs
-- have the same helicity, and negative sign when they have opposite helicity.
-- This gives an exact candidate good/bad helical class split before absolute
-- values or total-variation aggregation.
--
-- No turbulence-statistical conclusion is imported from Waleffe.  The file is
-- finite ordered-field algebra.  Physical promotion still requires the literal
-- helical Fourier decomposition and triadwise signed-helicity conservation on
-- the same NS transfer carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; _+_; _-_; _*_; -_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

record TriadTransfer : Set where
  constructor triad-transfer
  field
    p q r : ℚ
    transferP transferQ transferR : ℚ

open TriadTransfer public

energyDefect : TriadTransfer → ℚ
energyDefect t = transferP t + transferQ t + transferR t

viscousMoment : TriadTransfer → ℚ
viscousMoment t =
  p t * p t * transferP t
  + q t * q t * transferQ t
  + r t * r t * transferR t

hPPP hPPM hPMP hPMM : TriadTransfer → ℚ
hPPP t =
  p t * transferP t + q t * transferQ t + r t * transferR t
hPPM t =
  p t * transferP t + q t * transferQ t - r t * transferR t
hPMP t =
  p t * transferP t - q t * transferQ t + r t * transferR t
hPMM t =
  p t * transferP t - q t * transferQ t - r t * transferR t

coeffPPP coeffPPM coeffPMP coeffPMM : TriadTransfer → ℚ
coeffPPP t = (q t - p t) * (r t - p t)
coeffPPM t = - ((q t - p t) * (p t + r t))
coeffPMP t = - ((p t + q t) * (r t - p t))
coeffPMM t = (p t + q t) * (p t + r t)

-- Stronger defect decompositions.  Each displayed invariant formula reduces to
-- the corresponding class coefficient when E=H=0.
pppDefectDecomposition : (t : TriadTransfer) →
  viscousMoment t
  ≡ coeffPPP t * transferP t
      + (- (q t * r t)) * energyDefect t
      + (q t + r t) * hPPP t
pppDefectDecomposition t =
  solve
    (p t ∷ q t ∷ r t ∷ transferP t ∷ transferQ t ∷ transferR t ∷ [])

ppmDefectDecomposition : (t : TriadTransfer) →
  viscousMoment t
  ≡ coeffPPM t * transferP t
      + (q t * r t) * energyDefect t
      + (q t - r t) * hPPM t
ppmDefectDecomposition t =
  solve
    (p t ∷ q t ∷ r t ∷ transferP t ∷ transferQ t ∷ transferR t ∷ [])

pmpDefectDecomposition : (t : TriadTransfer) →
  viscousMoment t
  ≡ coeffPMP t * transferP t
      + (q t * r t) * energyDefect t
      + (- (q t + r t)) * hPMP t
pmpDefectDecomposition t =
  solve
    (p t ∷ q t ∷ r t ∷ transferP t ∷ transferQ t ∷ transferR t ∷ [])

pmmDefectDecomposition : (t : TriadTransfer) →
  viscousMoment t
  ≡ coeffPMM t * transferP t
      + (- (q t * r t)) * energyDefect t
      + (r t - q t) * hPMM t
pmmDefectDecomposition t =
  solve
    (p t ∷ q t ∷ r t ∷ transferP t ∷ transferQ t ∷ transferR t ∷ [])

record PPPConserved (t : TriadTransfer) : Set where
  constructor ppp-conserved
  field
    energyZero : energyDefect t ≡ 0ℚ
    helicityZero : hPPP t ≡ 0ℚ

record PPMConserved (t : TriadTransfer) : Set where
  constructor ppm-conserved
  field
    energyZero : energyDefect t ≡ 0ℚ
    helicityZero : hPPM t ≡ 0ℚ

record PMPConserved (t : TriadTransfer) : Set where
  constructor pmp-conserved
  field
    energyZero : energyDefect t ≡ 0ℚ
    helicityZero : hPMP t ≡ 0ℚ

record PMMConserved (t : TriadTransfer) : Set where
  constructor pmm-conserved
  field
    energyZero : energyDefect t ≡ 0ℚ
    helicityZero : hPMM t ≡ 0ℚ

viscousMomentPPP : ∀ {t} → PPPConserved t →
  viscousMoment t ≡ coeffPPP t * transferP t
viscousMomentPPP {t} c
  rewrite pppDefectDecomposition t
        | PPPConserved.energyZero c
        | PPPConserved.helicityZero c = solve (coeffPPP t ∷ transferP t ∷ [])

viscousMomentPPM : ∀ {t} → PPMConserved t →
  viscousMoment t ≡ coeffPPM t * transferP t
viscousMomentPPM {t} c
  rewrite ppmDefectDecomposition t
        | PPMConserved.energyZero c
        | PPMConserved.helicityZero c = solve (coeffPPM t ∷ transferP t ∷ [])

viscousMomentPMP : ∀ {t} → PMPConserved t →
  viscousMoment t ≡ coeffPMP t * transferP t
viscousMomentPMP {t} c
  rewrite pmpDefectDecomposition t
        | PMPConserved.energyZero c
        | PMPConserved.helicityZero c = solve (coeffPMP t ∷ transferP t ∷ [])

viscousMomentPMM : ∀ {t} → PMMConserved t →
  viscousMoment t ≡ coeffPMM t * transferP t
viscousMomentPMM {t} c
  rewrite pmmDefectDecomposition t
        | PMMConserved.energyZero c
        | PMMConserved.helicityZero c = solve (coeffPMM t ∷ transferP t ∷ [])

record OrderedMagnitudes (t : TriadTransfer) : Set where
  constructor ordered-magnitudes
  field
    pNonnegative : 0ℚ ≤ p t
    pBelowQ : p t ≤ q t
    qBelowR : q t ≤ r t

open OrderedMagnitudes public

differenceNonnegative : ∀ {a b : ℚ} → a ≤ b → 0ℚ ≤ b - a
differenceNonnegative {a} {b} a≤b =
  let
    shifted = ℚP.+-monoʳ-≤ (- a) a≤b
    leftMeaning : a + (- a) ≡ 0ℚ
    leftMeaning = solve (a ∷ [])
    rightMeaning : b + (- a) ≡ b - a
    rightMeaning = solve (a ∷ b ∷ [])
  in
  subst
    (λ left → left ≤ b - a)
    leftMeaning
    (subst (λ right → a + (- a) ≤ right) rightMeaning shifted)

qNonnegative : ∀ {t} → OrderedMagnitudes t → 0ℚ ≤ q t
qNonnegative order = ℚP.≤-trans (pNonnegative order) (pBelowQ order)

rNonnegative : ∀ {t} → OrderedMagnitudes t → 0ℚ ≤ r t
rNonnegative order = ℚP.≤-trans (qNonnegative order) (qBelowR order)

sumNonnegative : ∀ {a b : ℚ} → 0ℚ ≤ a → 0ℚ ≤ b → 0ℚ ≤ a + b
sumNonnegative = ℚP.+-mono-≤

coeffPPPNN : ∀ {t} → OrderedMagnitudes t → 0ℚ ≤ coeffPPP t
coeffPPPNN {t} order =
  let
    qGap = differenceNonnegative (pBelowQ order)
    pBelowR = ℚP.≤-trans (pBelowQ order) (qBelowR order)
    rGap = differenceNonnegative pBelowR
    instance
      qGapI = nonNegative qGap
      rGapI = nonNegative rGap
      prodI = ℚP.nonNeg*nonNeg⇒nonNeg (q t - p t) (r t - p t)
  in ℚP.nonNegative⁻¹ (coeffPPP t)

coeffPMMNN : ∀ {t} → OrderedMagnitudes t → 0ℚ ≤ coeffPMM t
coeffPMMNN {t} order =
  let
    pq = sumNonnegative (pNonnegative order) (qNonnegative order)
    pr = sumNonnegative (pNonnegative order) (rNonnegative order)
    instance
      pqI = nonNegative pq
      prI = nonNegative pr
      prodI = ℚP.nonNeg*nonNeg⇒nonNeg (p t + q t) (p t + r t)
  in ℚP.nonNegative⁻¹ (coeffPMM t)

oppositeHigherPPMCoefficientNonpositive : ∀ {t} → OrderedMagnitudes t →
  coeffPPM t ≤ 0ℚ
oppositeHigherPPMCoefficientNonpositive {t} order =
  let
    qGap = differenceNonnegative (pBelowQ order)
    pr = sumNonnegative (pNonnegative order) (rNonnegative order)
    productNN : 0ℚ ≤ (q t - p t) * (p t + r t)
    productNN =
      let instance
        qGapI = nonNegative qGap
        prI = nonNegative pr
        productI = ℚP.nonNeg*nonNeg⇒nonNeg (q t - p t) (p t + r t)
      in ℚP.nonNegative⁻¹ ((q t - p t) * (p t + r t))
    shifted = ℚP.+-monoʳ-≤ (- ((q t - p t) * (p t + r t))) productNN
  in
  subst
    (λ right → coeffPPM t ≤ right)
    (solve ((q t - p t) * (p t + r t) ∷ []))
    (subst
      (λ left → left ≤ ((q t - p t) * (p t + r t))
          + (- ((q t - p t) * (p t + r t))))
      (solve ((q t - p t) * (p t + r t) ∷ []))
      shifted)

oppositeHigherPMPCoefficientNonpositive : ∀ {t} → OrderedMagnitudes t →
  coeffPMP t ≤ 0ℚ
oppositeHigherPMPCoefficientNonpositive {t} order =
  let
    pq = sumNonnegative (pNonnegative order) (qNonnegative order)
    pBelowR = ℚP.≤-trans (pBelowQ order) (qBelowR order)
    rGap = differenceNonnegative pBelowR
    productNN : 0ℚ ≤ (p t + q t) * (r t - p t)
    productNN =
      let instance
        pqI = nonNegative pq
        rGapI = nonNegative rGap
        productI = ℚP.nonNeg*nonNeg⇒nonNeg (p t + q t) (r t - p t)
      in ℚP.nonNegative⁻¹ ((p t + q t) * (r t - p t))
    shifted = ℚP.+-monoʳ-≤ (- ((p t + q t) * (r t - p t))) productNN
  in
  subst
    (λ right → coeffPMP t ≤ right)
    (solve ((p t + q t) * (r t - p t) ∷ []))
    (subst
      (λ left → left ≤ ((p t + q t) * (r t - p t))
          + (- ((p t + q t) * (r t - p t))))
      (solve ((p t + q t) * (r t - p t) ∷ []))
      shifted)

round92HigherLegSameHelicityGivesNonnegativeLowTransferCoefficient : Bool
round92HigherLegSameHelicityGivesNonnegativeLowTransferCoefficient = true

round92HigherLegOppositeHelicityGivesNonpositiveLowTransferCoefficient : Bool
round92HigherLegOppositeHelicityGivesNonpositiveLowTransferCoefficient = true

round92LiteralHelicalTriadClassificationConstructed : Bool
round92LiteralHelicalTriadClassificationConstructed = false

round92HigherLegSameHelicityGivesNonnegativeLowTransferCoefficientIsTrue :
  round92HigherLegSameHelicityGivesNonnegativeLowTransferCoefficient ≡ true
round92HigherLegSameHelicityGivesNonnegativeLowTransferCoefficientIsTrue = refl

round92HigherLegOppositeHelicityGivesNonpositiveLowTransferCoefficientIsTrue :
  round92HigherLegOppositeHelicityGivesNonpositiveLowTransferCoefficient ≡ true
round92HigherLegOppositeHelicityGivesNonpositiveLowTransferCoefficientIsTrue = refl
