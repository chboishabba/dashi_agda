{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650DyadicDifferenceOrientedGapRound754Exact where

------------------------------------------------------------------------
-- ROUND754 / ORIENT THE TWO R748 DYADIC DIFFERENCES BY SHELL GAP
--
-- R748 uses q as the reference leg:
--
--   (lambda~_k-lambda~_q) PairPower_k
-- + (lambda~_p-lambda~_q) PairPower_p.
--
-- R753 turns each signed difference into an exact shell-gap factor.
--
-- If q lies above both k and p:
--
--   j_q = j_k + r_k,
--   j_q = j_p + r_p,
--
-- then both coefficients are NEGATIVE:
--
--   -lambda~_k (2^r_k - 1),
--   -lambda~_p (2^r_p - 1).
--
-- If q lies below both:
--
--   j_k = j_q + r_k,
--   j_p = j_q + r_p,
--
-- then both coefficients are POSITIVE and share lambda~_q:
--
--   lambda~_q (2^r_k - 1),
--   lambda~_q (2^r_p - 1).
--
-- These are exact identities. No sign of PairPower itself is asserted.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 1ℚ; _+_; _-_; _*_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadOrbitConstruction as Orbit
import DASHI.Physics.Closure.NSTriadKNPhysicalGalerkinIncidencePermutationRound38Exact as R38
import DASHI.Physics.Closure.NSTriadKNLiteralDyadicShellConstants as Shell
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNR650DyadicPairedProductionDifferenceRound748Exact as R748
import DASHI.Physics.Closure.NSTriadKNR650DyadicDifferenceGapFactorRound753Exact as R753

F : C3.RealField _
F = Rational.rationalRealField

qHighFactoredCell :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  (system : Audit.FiniteComplex3GalerkinSystem F E I) →
  (tau : Physical.PhysicalTriadIncidence) →
  Z3.NonZeroMode (Physical.k tau) →
  Z3.NonZeroMode (Physical.p tau) →
  Z3.NonZeroMode (Physical.q tau) →
  (gapK gapP : Nat) →
  Shell.shellIndex (Physical.q tau)
    ≡ Shell.shellIndex (Physical.k tau) + gapK →
  Shell.shellIndex (Physical.q tau)
    ≡ Shell.shellIndex (Physical.p tau) + gapP →
  R748.pairedProductionTwoDifferenceCell system tau
  ≡
  - (
      R748.selectedDyadicWeight (Physical.k tau)
        * (R753.shellWeight gapK - 1ℚ)
        * R38.orderedPairPower E I tau (Audit.velocity system)
    )
  +
  - (
      R748.selectedDyadicWeight (Physical.p tau)
        * (R753.shellWeight gapP - 1ℚ)
        * R38.orderedPairPower E I
            (Orbit.pEnergyLeg tau) (Audit.velocity system)
    )
qHighFactoredCell {E} {I}
    system tau kNonzero pNonzero qNonzero
    gapK gapP qFromK qFromP =
  let
    wk = R748.selectedDyadicWeight (Physical.k tau)
    wp = R748.selectedDyadicWeight (Physical.p tau)
    wq = R748.selectedDyadicWeight (Physical.q tau)
    pk = R38.orderedPairPower E I tau (Audit.velocity system)
    pp =
      R38.orderedPairPower E I
        (Orbit.pEnergyLeg tau) (Audit.velocity system)
    fk = R753.shellWeight gapK - 1ℚ
    fp = R753.shellWeight gapP - 1ℚ

    qMinusK : wq - wk ≡ wk * fk
    qMinusK =
      R753.selectedDyadicWeightDifferenceGapFactor
        (Physical.k tau) (Physical.q tau)
        kNonzero qNonzero gapK qFromK

    qMinusP : wq - wp ≡ wp * fp
    qMinusP =
      R753.selectedDyadicWeightDifferenceGapFactor
        (Physical.p tau) (Physical.q tau)
        pNonzero qNonzero gapP qFromP

    kMinusQ : wk - wq ≡ - (wk * fk)
    kMinusQ =
      trans
        (solve (wk ∷ wq ∷ []))
        (cong₂ _-_ refl qMinusK
          |> λ _ → solve (wk ∷ wq ∷ fk ∷ []))

  in
  rewrite qMinusK | qMinusP =
    solve (wk ∷ wp ∷ wq ∷ pk ∷ pp ∷ fk ∷ fp ∷ [])

qLowFactoredCell :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  (system : Audit.FiniteComplex3GalerkinSystem F E I) →
  (tau : Physical.PhysicalTriadIncidence) →
  Z3.NonZeroMode (Physical.k tau) →
  Z3.NonZeroMode (Physical.p tau) →
  Z3.NonZeroMode (Physical.q tau) →
  (gapK gapP : Nat) →
  Shell.shellIndex (Physical.k tau)
    ≡ Shell.shellIndex (Physical.q tau) + gapK →
  Shell.shellIndex (Physical.p tau)
    ≡ Shell.shellIndex (Physical.q tau) + gapP →
  R748.pairedProductionTwoDifferenceCell system tau
  ≡
  R748.selectedDyadicWeight (Physical.q tau)
      * (R753.shellWeight gapK - 1ℚ)
      * R38.orderedPairPower E I tau (Audit.velocity system)
  +
  R748.selectedDyadicWeight (Physical.q tau)
      * (R753.shellWeight gapP - 1ℚ)
      * R38.orderedPairPower E I
          (Orbit.pEnergyLeg tau) (Audit.velocity system)
qLowFactoredCell {E} {I}
    system tau kNonzero pNonzero qNonzero
    gapK gapP kFromQ pFromQ =
  let
    wk = R748.selectedDyadicWeight (Physical.k tau)
    wp = R748.selectedDyadicWeight (Physical.p tau)
    wq = R748.selectedDyadicWeight (Physical.q tau)
    pk = R38.orderedPairPower E I tau (Audit.velocity system)
    pp =
      R38.orderedPairPower E I
        (Orbit.pEnergyLeg tau) (Audit.velocity system)
    fk = R753.shellWeight gapK - 1ℚ
    fp = R753.shellWeight gapP - 1ℚ

    kMinusQ : wk - wq ≡ wq * fk
    kMinusQ =
      R753.selectedDyadicWeightDifferenceGapFactor
        (Physical.q tau) (Physical.k tau)
        qNonzero kNonzero gapK kFromQ

    pMinusQ : wp - wq ≡ wq * fp
    pMinusQ =
      R753.selectedDyadicWeightDifferenceGapFactor
        (Physical.q tau) (Physical.p tau)
        qNonzero pNonzero gapP pFromQ
  in
  rewrite kMinusQ | pMinusQ =
    refl

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round754QHighMakesBothDyadicDifferenceCoefficientsNegative : Bool
round754QHighMakesBothDyadicDifferenceCoefficientsNegative = true

round754QLowMakesBothDyadicDifferenceCoefficientsPositiveFactorForm : Bool
round754QLowMakesBothDyadicDifferenceCoefficientsPositiveFactorForm = true

round754AssertsPairPowerSign : Bool
round754AssertsPairPowerSign = false

round754IntroducesEstimate : Bool
round754IntroducesEstimate = false

round754ClayPromotion : Bool
round754ClayPromotion = false

round754QHighMakesBothDyadicDifferenceCoefficientsNegativeIsTrue :
  round754QHighMakesBothDyadicDifferenceCoefficientsNegative ≡ true
round754QHighMakesBothDyadicDifferenceCoefficientsNegativeIsTrue = refl

round754QLowMakesBothDyadicDifferenceCoefficientsPositiveFactorFormIsTrue :
  round754QLowMakesBothDyadicDifferenceCoefficientsPositiveFactorForm ≡ true
round754QLowMakesBothDyadicDifferenceCoefficientsPositiveFactorFormIsTrue =
  refl

round754AssertsPairPowerSignIsFalse :
  round754AssertsPairPowerSign ≡ false
round754AssertsPairPowerSignIsFalse = refl

round754IntroducesEstimateIsFalse :
  round754IntroducesEstimate ≡ false
round754IntroducesEstimateIsFalse = refl

round754ClayPromotionIsFalse :
  round754ClayPromotion ≡ false
round754ClayPromotionIsFalse = refl
