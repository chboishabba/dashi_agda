{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNCyclicResolvedTransferRateDefectRound598Exact where

------------------------------------------------------------------------
-- ROUND598 / CONSERVED CYCLIC TRANSFER -> RESOLVENT x RATE-DEFECT NORMAL FORM
--
-- Let T0+T1+T2=0 and let
--
--   wi = 1 / lambda_i
--
-- for the three cyclic pair rates.  Subtract the common reference weight w0:
--
--   w0 T0 + w1 T1 + w2 T2
--     = (w1-w0) T1 + (w2-w0) T2.
--
-- The existing exact reciprocal-difference theorem then gives
--
--   = w1 w0 (lambda0-lambda1) T1
--     + w2 w0 (lambda0-lambda2) T2.
--
-- Thus, once an actual R230/R503 scalar consumer is identified with a
-- conserved three-leg transfer, the Cauchy-weight failure to descend is
-- already EXACTLY a signed radial/rate-difference carrier.  No absolute value,
-- norm, shell count, reciprocal majorant, spacetime estimate, or PDE estimate
-- is introduced here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; Positive; _+_; _*_; _-_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong₂; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalCyclicCellRateDefectBidiExact as Cycle
import DASHI.Physics.Closure.NSTriadKNCyclicResolventDefectFactorizationBidiExact as Resolvent
import DASHI.Physics.Closure.NSTriadKNCyclicConservationWeightedDefectBidiExact as Conservation

------------------------------------------------------------------------
-- Generic reference-w0 conservation identity.
------------------------------------------------------------------------

weightedCyclicSumFromReference0 :
  (w0 w1 w2 : ℚ) →
  (T : Conservation.CyclicTransferTriple) →
  Conservation.weightedCyclicSum w0 w1 w2 T
  ≡
  (w1 - w0) * Conservation.T1 T
    + (w2 - w0) * Conservation.T2 T
weightedCyclicSumFromReference0 w0 w1 w2 T =
  let
    t0 = Conservation.T0 T
    t1 = Conservation.T1 T
    t2 = Conservation.T2 T

    replaceThird :
      Conservation.weightedCyclicSum w0 w1 w2 T
      ≡ w0 * t0 + w1 * t1 + w2 * (0ℚ - (t0 + t1))
    replaceThird =
      cong
        (λ selected → w0 * t0 + w1 * t1 + w2 * selected)
        (Conservation.thirdFromConservation T)
  in
  trans replaceThird (solve (w0 ∷ w1 ∷ w2 ∷ t0 ∷ t1 ∷ []))

------------------------------------------------------------------------
-- Physical cyclic pair-rate / Cauchy-resolvent specialization.
------------------------------------------------------------------------

resolvedRateDefectForm :
  (rho : Z3.FourierMode → ℚ) →
  (alpha beta : Physical.PhysicalTriadIncidence) →
  Conservation.CyclicTransferTriple →
  ℚ
resolvedRateDefectForm rho alpha beta T =
  Resolvent.pairWeight1 rho alpha beta
    * Resolvent.pairWeight0 rho alpha beta
    * (Cycle.pairCycle0Rate rho alpha beta
      - Cycle.pairCycle1Rate rho alpha beta)
    * Conservation.T1 T
  +
  Resolvent.pairWeight2 rho alpha beta
    * Resolvent.pairWeight0 rho alpha beta
    * (Cycle.pairCycle0Rate rho alpha beta
      - Cycle.pairCycle2Rate rho alpha beta)
    * Conservation.T2 T

resolvedWeightedCyclicTransferIsRateDefects :
  (rho : Z3.FourierMode → ℚ) →
  (alpha beta : Physical.PhysicalTriadIncidence) →
  (T : Conservation.CyclicTransferTriple) →
  Positive (Cycle.pairCycle0Rate rho alpha beta) →
  Positive (Cycle.pairCycle1Rate rho alpha beta) →
  Positive (Cycle.pairCycle2Rate rho alpha beta) →
  Conservation.weightedCyclicSum
    (Resolvent.pairWeight0 rho alpha beta)
    (Resolvent.pairWeight1 rho alpha beta)
    (Resolvent.pairWeight2 rho alpha beta)
    T
  ≡ resolvedRateDefectForm rho alpha beta T
resolvedWeightedCyclicTransferIsRateDefects
    rho alpha beta T p0 p1 p2 =
  let
    w0 = Resolvent.pairWeight0 rho alpha beta
    w1 = Resolvent.pairWeight1 rho alpha beta
    w2 = Resolvent.pairWeight2 rho alpha beta
    t1 = Conservation.T1 T
    t2 = Conservation.T2 T

    conservationForm :
      Conservation.weightedCyclicSum w0 w1 w2 T
      ≡ (w1 - w0) * t1 + (w2 - w0) * t2
    conservationForm =
      weightedCyclicSumFromReference0 w0 w1 w2 T

    defect1 :
      w1 - w0
      ≡ w1 * w0
          * (Cycle.pairCycle0Rate rho alpha beta
            - Cycle.pairCycle1Rate rho alpha beta)
    defect1 =
      Resolvent.cycle1WeightDefectFactorization
        rho alpha beta p0 p1

    defect2 :
      w2 - w0
      ≡ w2 * w0
          * (Cycle.pairCycle0Rate rho alpha beta
            - Cycle.pairCycle2Rate rho alpha beta)
    defect2 =
      Resolvent.cycle2WeightDefectFactorization
        rho alpha beta p0 p2
  in
  trans conservationForm
    (trans
      (cong₂ _+_
        (cong (_* t1) defect1)
        (cong (_* t2) defect2))
      (solve
        ( w0 ∷ w1 ∷ w2
        ∷ Cycle.pairCycle0Rate rho alpha beta
        ∷ Cycle.pairCycle1Rate rho alpha beta
        ∷ Cycle.pairCycle2Rate rho alpha beta
        ∷ t1 ∷ t2 ∷ [])))

------------------------------------------------------------------------
-- Expose the numerator defects directly in modal-rate coordinates.
------------------------------------------------------------------------

cycle1ResolvedNumeratorIsRadialRateDefect :
  (rho : Z3.FourierMode → ℚ) →
  (alpha beta : Physical.PhysicalTriadIncidence) →
  Cycle.pairCycle0Rate rho alpha beta
    - Cycle.pairCycle1Rate rho alpha beta
  ≡
  (rho (Physical.p alpha) + rho (Physical.p beta))
    - (rho (Physical.k alpha) + rho (Physical.k beta))
cycle1ResolvedNumeratorIsRadialRateDefect =
  Resolvent.cycle1PairRateDefectExpanded

cycle2ResolvedNumeratorIsRadialRateDefect :
  (rho : Z3.FourierMode → ℚ) →
  (alpha beta : Physical.PhysicalTriadIncidence) →
  Cycle.pairCycle0Rate rho alpha beta
    - Cycle.pairCycle2Rate rho alpha beta
  ≡
  (rho (Physical.q alpha) + rho (Physical.q beta))
    - (rho (Physical.k alpha) + rho (Physical.k beta))
cycle2ResolvedNumeratorIsRadialRateDefect =
  Resolvent.cycle2PairRateDefectExpanded

------------------------------------------------------------------------
-- Status / exact remaining seam.
------------------------------------------------------------------------

round598Reference0CyclicDefectReductionClosed : Bool
round598Reference0CyclicDefectReductionClosed = true

round598ResolvedWeightedTransferIsRateDefectFormClosed : Bool
round598ResolvedWeightedTransferIsRateDefectFormClosed = true

round598RateDefectNumeratorsExposedInPhysicalModes : Bool
round598RateDefectNumeratorsExposedInPhysicalModes = true

round598IntroducesAbsoluteValueOrNorm : Bool
round598IntroducesAbsoluteValueOrNorm = false

round598IntroducesNewNSEstimate : Bool
round598IntroducesNewNSEstimate = false

round598R230ScalarConsumerToConservedTripleWeldClosed : Bool
round598R230ScalarConsumerToConservedTripleWeldClosed = false

round598CutoffUniformSpacetimePaymentClosed : Bool
round598CutoffUniformSpacetimePaymentClosed = false

round598ClayPromotion : Bool
round598ClayPromotion = false

round598Reference0CyclicDefectReductionClosedIsTrue :
  round598Reference0CyclicDefectReductionClosed ≡ true
round598Reference0CyclicDefectReductionClosedIsTrue = refl

round598ResolvedWeightedTransferIsRateDefectFormClosedIsTrue :
  round598ResolvedWeightedTransferIsRateDefectFormClosed ≡ true
round598ResolvedWeightedTransferIsRateDefectFormClosedIsTrue = refl

round598IntroducesNewNSEstimateIsFalse :
  round598IntroducesNewNSEstimate ≡ false
round598IntroducesNewNSEstimateIsFalse = refl

round598R230ScalarConsumerToConservedTripleWeldClosedIsFalse :
  round598R230ScalarConsumerToConservedTripleWeldClosed ≡ false
round598R230ScalarConsumerToConservedTripleWeldClosedIsFalse = refl

round598CutoffUniformSpacetimePaymentClosedIsFalse :
  round598CutoffUniformSpacetimePaymentClosed ≡ false
round598CutoffUniformSpacetimePaymentClosedIsFalse = refl

round598ClayPromotionIsFalse :
  round598ClayPromotion ≡ false
round598ClayPromotionIsFalse = refl
