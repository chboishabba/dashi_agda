{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650GlobalCommutatorIncidenceExpansionRound692Exact where

------------------------------------------------------------------------
-- ROUND692 / GLOBAL COHERENT COMMUTATOR -> LITERAL INCIDENCE PAIR SUM
--
-- For one output k,
--
--   M_k = sum_{alpha in F_k} A_alpha,
--   C_k = sum_{beta  in F_k} C_beta,
--
-- where A is the literal mixed-helicity cell and C is the literal R230
-- forcing-commutator cell.  Bilinearity of coherent work gives
--
--   W(M_k,C_k)
--     = sum_{alpha,beta in F_k} W(A_alpha,C_beta).
--
-- This file installs that equality on the actual physical fibres and then
-- sums it over an arbitrary output list, in particular the canonical nonzero
-- cutoff outputs.  No inequality, norm, absolute value, orbit cardinality, or
-- analytic estimate enters.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_)
open import Relation.Binary.PropositionalEquality using (cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNCanonicalCutoffSameObjectSystemRound34Exact as Canonical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNFixedOutputMixedCommutatorDampedTangentExact as D1a
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovarianceWorkExact as Work
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNMixedHelicityForcingSwapRound230Exact as R230
import DASHI.Physics.Closure.NSTriadKNFullSquareDiagonalOffDiagonalRound543Exact as R543
import DASHI.Physics.Closure.NSTriadKNFullSquareAsSpectatorRowsRound546Exact as R546
import DASHI.Physics.Closure.NSTriadKNA3CenteredCauchyPairNormalFormRound600Exact as R600

F : C3.RealField _
F = Rational.rationalRealField

module Expansion
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F) where

  system = Field30.finiteSystem physicalSystem
  cutoff = Audit.cutoff system
  velocity = Audit.velocityAt system
  forcing = Audit.projectedNonlinearity system

  mixedCell :
    Physical.PhysicalTriadIncidence → C3.Complex3 F
  mixedCell = D1a.mixedProductCell S velocity

  commutatorCell :
    Physical.PhysicalTriadIncidence → C3.Complex3 F
  commutatorCell = R230.forcingCommutatorCell S velocity forcing

  commutatorPair :
    Physical.PhysicalTriadIncidence →
    Physical.PhysicalTriadIncidence → ℚ
  commutatorPair = R600.workPairLR mixedCell commutatorCell

  fibre :
    Z3.FourierMode → List Physical.PhysicalTriadIncidence
  fibre output = Output.physicalOutputFiber cutoff output

  outputPairIncidenceSum :
    Z3.FourierMode → ℚ
  outputPairIncidenceSum output =
    R543.fullSquareSum commutatorPair (fibre output)

  outputCoherentCommutatorWork :
    Z3.FourierMode → ℚ
  outputCoherentCommutatorWork output =
    Work.coherentWork
      (Work.fixedOutputMixedProduct S velocity cutoff output)
      (Work.fixedOutputCommutator S velocity forcing cutoff output)

  outputCommutatorWorkIsPairIncidenceSum :
    (output : Z3.FourierMode) →
    outputCoherentCommutatorWork output
    ≡ outputPairIncidenceSum output
  outputCommutatorWorkIsPairIncidenceSum output =
    sym
      (R600.fullWorkLRFactors
        mixedCell commutatorCell (fibre output))

  outputPairIncidenceSumIsSpectatorRows :
    (output : Z3.FourierMode) →
    outputPairIncidenceSum output
    ≡
    R546.allSpectatorRows
      commutatorPair (fibre output) (fibre output)
  outputPairIncidenceSumIsSpectatorRows output =
    R546.fullSquareIsAllSpectatorRows
      commutatorPair (fibre output)

  sumOutputCommutatorWork :
    List Z3.FourierMode → ℚ
  sumOutputCommutatorWork [] = 0ℚ
  sumOutputCommutatorWork (output ∷ rest) =
    outputCoherentCommutatorWork output
      + sumOutputCommutatorWork rest

  sumOutputPairIncidences :
    List Z3.FourierMode → ℚ
  sumOutputPairIncidences [] = 0ℚ
  sumOutputPairIncidences (output ∷ rest) =
    outputPairIncidenceSum output
      + sumOutputPairIncidences rest

  globalCommutatorIsLiteralPairIncidenceSum :
    (outputs : List Z3.FourierMode) →
    sumOutputCommutatorWork outputs
    ≡ sumOutputPairIncidences outputs
  globalCommutatorIsLiteralPairIncidenceSum [] = refl
  globalCommutatorIsLiteralPairIncidenceSum (output ∷ rest) =
    cong₂ _+_
      (outputCommutatorWorkIsPairIncidenceSum output)
      (globalCommutatorIsLiteralPairIncidenceSum rest)

  nonzeroGlobalCommutatorWork : ℚ
  nonzeroGlobalCommutatorWork =
    sumOutputCommutatorWork
      (Canonical.nonzeroCutoffModes cutoff)

  nonzeroGlobalPairIncidenceSum : ℚ
  nonzeroGlobalPairIncidenceSum =
    sumOutputPairIncidences
      (Canonical.nonzeroCutoffModes cutoff)

  nonzeroGlobalCommutatorIsLiteralPairIncidenceSum :
    nonzeroGlobalCommutatorWork
    ≡ nonzeroGlobalPairIncidenceSum
  nonzeroGlobalCommutatorIsLiteralPairIncidenceSum =
    globalCommutatorIsLiteralPairIncidenceSum
      (Canonical.nonzeroCutoffModes cutoff)

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round692FixedOutputCommutatorExpandedToLiteralOrderedPairCarrier : Bool
round692FixedOutputCommutatorExpandedToLiteralOrderedPairCarrier = true

round692GlobalNonzeroCommutatorExpandedBeforeEstimate : Bool
round692GlobalNonzeroCommutatorExpandedBeforeEstimate = true

round692SpectatorRowOrientationExposed : Bool
round692SpectatorRowOrientationExposed = true

round692NestedProjectedForcingExpansionClosedHere : Bool
round692NestedProjectedForcingExpansionClosedHere = false

round692IntroducesEstimate : Bool
round692IntroducesEstimate = false

round692IntroducesAbsoluteValueOrNorm : Bool
round692IntroducesAbsoluteValueOrNorm = false

round692GlobalTriadOrbitCancellationClosed : Bool
round692GlobalTriadOrbitCancellationClosed = false

round692ClayPromotion : Bool
round692ClayPromotion = false

round692FixedOutputCommutatorExpandedToLiteralOrderedPairCarrierIsTrue :
  round692FixedOutputCommutatorExpandedToLiteralOrderedPairCarrier ≡ true
round692FixedOutputCommutatorExpandedToLiteralOrderedPairCarrierIsTrue = refl

round692GlobalNonzeroCommutatorExpandedBeforeEstimateIsTrue :
  round692GlobalNonzeroCommutatorExpandedBeforeEstimate ≡ true
round692GlobalNonzeroCommutatorExpandedBeforeEstimateIsTrue = refl

round692SpectatorRowOrientationExposedIsTrue :
  round692SpectatorRowOrientationExposed ≡ true
round692SpectatorRowOrientationExposedIsTrue = refl

round692NestedProjectedForcingExpansionClosedHereIsFalse :
  round692NestedProjectedForcingExpansionClosedHere ≡ false
round692NestedProjectedForcingExpansionClosedHereIsFalse = refl

round692IntroducesEstimateIsFalse :
  round692IntroducesEstimate ≡ false
round692IntroducesEstimateIsFalse = refl

round692IntroducesAbsoluteValueOrNormIsFalse :
  round692IntroducesAbsoluteValueOrNorm ≡ false
round692IntroducesAbsoluteValueOrNormIsFalse = refl

round692GlobalTriadOrbitCancellationClosedIsFalse :
  round692GlobalTriadOrbitCancellationClosed ≡ false
round692GlobalTriadOrbitCancellationClosedIsFalse = refl

round692ClayPromotionIsFalse :
  round692ClayPromotion ≡ false
round692ClayPromotionIsFalse = refl
