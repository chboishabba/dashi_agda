module DASHI.Physics.Closure.NSTriadKNWeightedCompanionHermitianCrossRound439Exact where

------------------------------------------------------------------------
-- ROUND439 / R438 TRANSPORTS THROUGH THE EXACT SIGNED HERMITIAN CROSS
--
-- R438 proves on the complete physical output fibre that the doubled R294
-- weighted projected-forcing fold is exactly the slot-or-zero quadratic-
-- companion fold.  R415/R423 consume a scalar signed aggregate cross rather
-- than the forcing vector alone.
--
-- This file closes that remaining forcing-side scalar transport without
-- inventing an amplitude proxy.  For ANY supplied same-object amplitude
-- aggregate A_k,
--
--   Re < A_k , fold (2 w F) >
--     = Re < A_k , fold (weighted quadratic companion) >.
--
-- The theorem is just congruence through R179's literal rational Hermitian
-- cross.  Thus a future R299/R415 producer only has to identify its amplitude
-- aggregate and prove the quantitative spacetime bound; there is no second
-- forcing-side same-object weld after R438.
--
-- CLAIM BOUNDARY
-- --------------
-- This does NOT identify R299's abstract `aggregateAmplitudeForcingCross` with
-- a physical scalar by itself, because R299 deliberately stores only a scalar
-- compiler.  It proves the exact transport theorem needed once the physical
-- amplitude aggregate is supplied.  No estimate, sign claim, norm, absolute
-- value, integration rule, or Package-A promotion is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNResolventWeightedMixedCommutatorRound294Exact as R294
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramRound179Exact as R179
import DASHI.Physics.Closure.NSTriadKNWeightedProjectedForcingOuterFoldRound438Exact as R438

F : C3.RealField _
F = Rational.rationalRealField

fixedOutputDoubleWeightedForcingCross :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (S : Helical.HelicalModeScalars F) →
  (W : R294.SwapInvariantCellWeight F) →
  (system : Audit.FiniteComplex3GalerkinSystem F E I) →
  (output : Z3.FourierMode) →
  C3.Complex3 F →
  Rational.ℚ
fixedOutputDoubleWeightedForcingCross E I S W system output amplitude =
  R179.realHermitianCross amplitude
    (R438.foldDoubleWeightedProjectedForcing W S system
      (DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber.physicalOutputFiber
        (Audit.cutoff system) output))

fixedOutputWeightedCompanionCross :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (S : Helical.HelicalModeScalars F) →
  (W : R294.SwapInvariantCellWeight F) →
  (system : Audit.FiniteComplex3GalerkinSystem F E I) →
  (output : Z3.FourierMode) →
  C3.Complex3 F →
  Rational.ℚ
fixedOutputWeightedCompanionCross E I S W system output amplitude =
  R179.realHermitianCross amplitude
    (R438.foldExhaustiveWeightedCompanion W S system
      (DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber.physicalOutputFiber
        (Audit.cutoff system) output))

fixedOutputWeightedForcingCrossIsCompanionCross :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (S : Helical.HelicalModeScalars F) →
  (L : Helical.PeriodicHelicalProjectorLaws F E I S) →
  (H : R142.HelicalHalfCalibration S) →
  (W : R294.SwapInvariantCellWeight F) →
  (system : Audit.FiniteComplex3GalerkinSystem F E I) →
  ((mode : Z3.FourierMode) →
    Helical.Transverse E mode (Audit.velocity system mode)) →
  (output : Z3.FourierMode) →
  (amplitude : C3.Complex3 F) →
  fixedOutputDoubleWeightedForcingCross E I S W system output amplitude
  ≡ fixedOutputWeightedCompanionCross E I S W system output amplitude
fixedOutputWeightedForcingCrossIsCompanionCross
    E I S L H W system velocityTransverse output amplitude =
  cong (R179.realHermitianCross amplitude)
    (R438.fixedOutputDoubleWeightedR294FoldIsQuadraticCompanion
      {L = L} {H = H} W system velocityTransverse output)

record PhysicalAmplitudeAggregateCross
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (S : Helical.HelicalModeScalars F)
    (W : R294.SwapInvariantCellWeight F)
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (output : Z3.FourierMode) : Set where
  constructor physical-amplitude-aggregate-cross
  field
    amplitudeAggregate : C3.Complex3 F

open PhysicalAmplitudeAggregateCross public

physicalAmplitudeForcingCross :
  ∀ {E I S W system output} →
  PhysicalAmplitudeAggregateCross E I S W system output →
  Rational.ℚ
physicalAmplitudeForcingCross {E} {I} {S} {W} {system} {output} A =
  fixedOutputDoubleWeightedForcingCross E I S W system output
    (amplitudeAggregate A)

physicalAmplitudeCompanionCross :
  ∀ {E I S W system output} →
  PhysicalAmplitudeAggregateCross E I S W system output →
  Rational.ℚ
physicalAmplitudeCompanionCross {E} {I} {S} {W} {system} {output} A =
  fixedOutputWeightedCompanionCross E I S W system output
    (amplitudeAggregate A)

physicalAmplitudeForcingCrossIsCompanionCross :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (S : Helical.HelicalModeScalars F) →
  (L : Helical.PeriodicHelicalProjectorLaws F E I S) →
  (H : R142.HelicalHalfCalibration S) →
  (W : R294.SwapInvariantCellWeight F) →
  (system : Audit.FiniteComplex3GalerkinSystem F E I) →
  (velocityTransverse :
    (mode : Z3.FourierMode) →
    Helical.Transverse E mode (Audit.velocity system mode)) →
  (output : Z3.FourierMode) →
  (A : PhysicalAmplitudeAggregateCross E I S W system output) →
  physicalAmplitudeForcingCross A ≡ physicalAmplitudeCompanionCross A
physicalAmplitudeForcingCrossIsCompanionCross
    E I S L H W system velocityTransverse output A =
  fixedOutputWeightedForcingCrossIsCompanionCross
    E I S L H W system velocityTransverse output (amplitudeAggregate A)

round439R438TransportedThroughLiteralHermitianCross : Bool
round439R438TransportedThroughLiteralHermitianCross = true

round439ForcingSideSameObjectScalarWeldClosed : Bool
round439ForcingSideSameObjectScalarWeldClosed = true

round439R299PhysicalAmplitudeAggregateIdentified : Bool
round439R299PhysicalAmplitudeAggregateIdentified = false

round439SignedCrossSpacetimeEstimateClosed : Bool
round439SignedCrossSpacetimeEstimateClosed = false

round439R423SignedCompanionBudgetClosed : Bool
round439R423SignedCompanionBudgetClosed = false

round439PackageAClosed : Bool
round439PackageAClosed = false

round439ClayPromotion : Bool
round439ClayPromotion = false

round439ForcingSideSameObjectScalarWeldClosedIsTrue :
  round439ForcingSideSameObjectScalarWeldClosed ≡ true
round439ForcingSideSameObjectScalarWeldClosedIsTrue = refl

round439R299PhysicalAmplitudeAggregateIdentifiedIsFalse :
  round439R299PhysicalAmplitudeAggregateIdentified ≡ false
round439R299PhysicalAmplitudeAggregateIdentifiedIsFalse = refl

round439SignedCrossSpacetimeEstimateClosedIsFalse :
  round439SignedCrossSpacetimeEstimateClosed ≡ false
round439SignedCrossSpacetimeEstimateClosedIsFalse = refl
