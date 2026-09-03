module DASHI.Physics.Closure.NSTriadKNHeatNestedForcesQuadraticCompanionRound420Exact where

------------------------------------------------------------------------
-- ROUND420 / BIDI CORRECTION: R329 IS A FORCING INSERTION INTO THE R167 KERNEL
--
-- Repository archaeology past Round157 matters: Round200 rejects the degree-6
-- double-commutator energy ledger as the A-facing companion.  The surviving
-- homogeneity-correct companion is the QUADRATIC R167/R145 slot kernel.
--
-- The heat/nested route is already on that corrected object.  R329's outer slot
-- is literally
--
--   slotKernel n_p n_q (innerPairedForcing) u_q,
--
-- with n_p,n_q the SAME R167 normalized directions.  In other words it is the
-- first-input forcing insertion into the homogeneity-correct quadratic kernel,
-- not a new high-degree dynamic observable.
--
-- This round freezes that same-object fact definitionally.  It redirects the
-- R415 signed heat-cross search away from the obsolete R193 energy-owner route
-- and back to the R167/R178/R326 quadratic-companion route mandated by R200.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNRationalComplex3LerayPythagoras as Leray
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNAntiParallelHelicitySlotKernelRound145Exact as R145
import DASHI.Physics.Closure.NSTriadKNCriticalSlotQuadraticKernelRound167Exact as R167
import DASHI.Physics.Closure.NSTriadKNResolventWeightedMixedCommutatorRound294Exact as R294
import DASHI.Physics.Closure.NSTriadKNStrongLowLiteralNestedKernelRound329Exact as R329

F : C3.RealField _
F = Rational.rationalRealField

quadraticCompanionCell :
  (E : C3.IntegerEmbedding F) →
  (S : Helical.HelicalModeScalars F) →
  (tau : Physical.PhysicalTriadIncidence) →
  (uP uQ : C3.Complex3 F) →
  C3.Complex3 F
quadraticCompanionCell E S tau uP uQ =
  R145.slotKernel
    (R167.normalizedDirection E S (Physical.p tau))
    (R167.normalizedDirection E S (Physical.q tau))
    uP uQ

firstInputForcingInsertion :
  (E : C3.IntegerEmbedding F) →
  (S : Helical.HelicalModeScalars F) →
  (tau : Physical.PhysicalTriadIncidence) →
  (forcingP uQ : C3.Complex3 F) →
  C3.Complex3 F
firstInputForcingInsertion = quadraticCompanionCell

nestedOuterSlotIsQuadraticCompanionForcingInsertion :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (O : Leray.RationalInverseNormOrder E I) →
  (system : Audit.FiniteComplex3GalerkinSystem F E I) →
  (S : Helical.HelicalModeScalars F) →
  (L : Helical.PeriodicHelicalProjectorLaws F E I S) →
  (H : R142.HelicalHalfCalibration S) →
  (W : R294.SwapInvariantCellWeight F) →
  (C : R329.StrongLowLiteralNestedCell E I O system S L H W) →
  R329.literalNestedOuterSlot E I O system S L H W C
  ≡ firstInputForcingInsertion E S (R329.outer C)
      (R329.innerPairedForcing E I O system S L H W C)
      (Audit.velocity system (Physical.q (R329.outer C)))
nestedOuterSlotIsQuadraticCompanionForcingInsertion
  E I O system S L H W C = refl

weightedNestedCellIsWeightedQuadraticCompanionForcingInsertion :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (O : Leray.RationalInverseNormOrder E I) →
  (system : Audit.FiniteComplex3GalerkinSystem F E I) →
  (S : Helical.HelicalModeScalars F) →
  (L : Helical.PeriodicHelicalProjectorLaws F E I S) →
  (H : R142.HelicalHalfCalibration S) →
  (W : R294.SwapInvariantCellWeight F) →
  (C : R329.StrongLowLiteralNestedCell E I O system S L H W) →
  R329.literalWeightedNestedCell E I O system S L H W C
  ≡ C3.complex3Scale
      (R294.weight W (R329.outer C))
      (firstInputForcingInsertion E S (R329.outer C)
        (R329.innerPairedForcing E I O system S L H W C)
        (Audit.velocity system (Physical.q (R329.outer C))))
weightedNestedCellIsWeightedQuadraticCompanionForcingInsertion
  E I O system S L H W C = refl

round420ACompanionIsR167QuadraticKernel : Bool
round420ACompanionIsR167QuadraticKernel = true

round420R329NestedCellForcesSameQuadraticKernel : Bool
round420R329NestedCellForcesSameQuadraticKernel = true

round420R193HighDegreeEnergyLedgerUsedAsACompanion : Bool
round420R193HighDegreeEnergyLedgerUsedAsACompanion = false

round420SignedHeatCrossSearchStaysOnHomogeneityCorrectCarrier : Bool
round420SignedHeatCrossSearchStaysOnHomogeneityCorrectCarrier = true

round420R329NestedCellForcesSameQuadraticKernelIsTrue :
  round420R329NestedCellForcesSameQuadraticKernel ≡ true
round420R329NestedCellForcesSameQuadraticKernelIsTrue = refl

round420R193HighDegreeEnergyLedgerUsedAsACompanionIsFalse :
  round420R193HighDegreeEnergyLedgerUsedAsACompanion ≡ false
round420R193HighDegreeEnergyLedgerUsedAsACompanionIsFalse = refl
