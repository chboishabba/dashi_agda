module DASHI.Physics.Closure.NSTriadKNStrongLowLiteralNestedKernelRound329Exact where

------------------------------------------------------------------------
-- ROUND329 / LITERAL STRONGLY-LOW NESTED KERNEL ENTRY
--
-- R328 leaves row/column aggregation open.  Before any finite Cauchy or Schur
-- estimate, pin the exact nested physical carrier:
--
--   inner : a+b=p,
--   outer : p+q=k,
--
-- with the inner output literally identified with the outer forcing leg.
-- The inner paired forcing is R310/R120's pure commutator, whose radical-free
-- physical cell bound is R326.  The outer vector is the SAME R307/R145 slot
-- kernel, and the scalar cell weight is the SAME swap-invariant R294 weight.
--
-- BIDI tightening: R325 identifies the inner pure commutator with (-i) times
-- a Leray projection at the inner output.  R30 therefore proves it transverse
-- to that output, and `innerOutputIsOuterForcing` transports the theorem to the
-- literal outer p-leg.  The physical outer q velocity is retained explicitly.
-- After transporting both transversality facts through the normalized-direction
-- scalings, R145's anti-parallel factorization applies to the ACTUAL R329 outer
-- slot.  No abstract replacement forcing or generic kernel proxy is used.
--
-- This file still contains no row sum, column sum, fibre cardinality, or heat
-- integrability claim.  Those are downstream aggregation questions.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; _≤_)
open import Relation.Binary.PropositionalEquality using (cong; subst; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field
import DASHI.Physics.Closure.NSTriadKNComplex3AlgebraLaws as Algebra
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianScalingLaws as Scaling
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNCriticalSlotQuadraticKernelRound167Exact as R167
import DASHI.Physics.Closure.NSTriadKNAntiParallelHelicitySlotKernelRound145Exact as R145
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNRationalComplex3LerayPythagoras as Leray
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNLerayOutputTransversalityRound30Exact as LerayOut
import DASHI.Physics.Closure.NSTriadKNProjectedHelicalSelfForcingVectorRound106Exact as R106
import DASHI.Physics.Closure.NSTriadKNExternalPureCommutatorPartnerRound120Exact as R120
import DASHI.Physics.Closure.NSTriadKNInnerStrongLowOutputSubconeRound321Exact as R321
import DASHI.Physics.Closure.NSTriadKNHHDualDefectRawCurlKernelRound172Exact as R172
import DASHI.Physics.Closure.NSTriadKNPureCommutatorRawDualDefectWeldRound325Exact as R325
import DASHI.Physics.Closure.NSTriadKNRawCurlLowOutputKernelMassRound178Exact as R178
import DASHI.Physics.Closure.NSTriadKNPhysicalInnerCommutatorLowOutputBoundRound326Exact as R326
import DASHI.Physics.Closure.NSTriadKNResolventWeightedMixedCommutatorRound294Exact as R294

F : C3.RealField _
F = Rational.rationalRealField

record StrongLowLiteralNestedCell
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (O : Leray.RationalInverseNormOrder E I)
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F E I S)
    (H : R142.HelicalHalfCalibration S)
    (W : R294.SwapInvariantCellWeight F) : Set where
  constructor strong-low-literal-nested-cell
  field
    inner outer : Physical.PhysicalTriadIncidence
    innerOutputIsOuterForcing : Physical.k inner ≡ Physical.p outer
    innerHelical : R120.PhysicalHelicalOutputPair system inner
    innerPTransverse : Helical.Transverse E (Physical.p inner)
      (Audit.velocity system (Physical.p inner))
    innerQTransverse : Helical.Transverse E (Physical.q inner)
      (Audit.velocity system (Physical.q inner))
    outerQTransverse : Helical.Transverse E (Physical.q outer)
      (Audit.velocity system (Physical.q outer))
    strongLow : R321.StronglyLowInnerOutput

open StrongLowLiteralNestedCell public

innerPairedForcing :
  (E : C3.IntegerEmbedding F)
  (I : C3.ModeInverseSquare F E)
  (O : Leray.RationalInverseNormOrder E I)
  (system : Audit.FiniteComplex3GalerkinSystem F E I)
  (S : Helical.HelicalModeScalars F)
  (L : Helical.PeriodicHelicalProjectorLaws F E I S)
  (H : R142.HelicalHalfCalibration S)
  (W : R294.SwapInvariantCellWeight F) →
  StrongLowLiteralNestedCell E I O system S L H W → C3.Complex3 F
innerPairedForcing E I O system S L H W C =
  R120.pureCommutatorVector system (inner C) (innerHelical C)

innerPairedForcingTransverseAtInnerOutput :
  (E : C3.IntegerEmbedding F)
  (I : C3.ModeInverseSquare F E)
  (O : Leray.RationalInverseNormOrder E I)
  (system : Audit.FiniteComplex3GalerkinSystem F E I)
  (S : Helical.HelicalModeScalars F)
  (L : Helical.PeriodicHelicalProjectorLaws F E I S)
  (H : R142.HelicalHalfCalibration S)
  (W : R294.SwapInvariantCellWeight F)
  (C : StrongLowLiteralNestedCell E I O system S L H W) →
  Helical.Transverse E (Physical.k (inner C))
    (innerPairedForcing E I O system S L H W C)
innerPairedForcingTransverseAtInnerOutput E I O system S L H W C =
  let
    tau = inner C
    k = Physical.k tau
    raw =
      R172.rawDirectionalSlotKernel
        (C3.modeVector E (Physical.p tau))
        (C3.modeVector E (Physical.q tau))
        (Audit.velocity system (Physical.p tau))
        (Audit.velocity system (Physical.q tau))
    projected = C3.lerayProject3 E I k raw
    scale = R106.minusI F
    sameObject = R325.pureCommutatorIsMinusIProjectedRawKernel
      system tau (innerHelical C)
  in
  trans
    (cong (C3.bilinearDot3 (C3.modeVector E k)) sameObject)
    (trans
      (Scaling.bilinearDot3ScaleRight scale (C3.modeVector E k) projected)
      (trans
        (cong (C3.complexMultiply scale)
          (LerayOut.lerayOutputTransverseExact
            E I k (R120.outputNonzero (innerHelical C)) raw))
        (Field.complexMultiplyZeroRight scale)))

innerPairedForcingTransverseAtOuterForcing :
  (E : C3.IntegerEmbedding F)
  (I : C3.ModeInverseSquare F E)
  (O : Leray.RationalInverseNormOrder E I)
  (system : Audit.FiniteComplex3GalerkinSystem F E I)
  (S : Helical.HelicalModeScalars F)
  (L : Helical.PeriodicHelicalProjectorLaws F E I S)
  (H : R142.HelicalHalfCalibration S)
  (W : R294.SwapInvariantCellWeight F)
  (C : StrongLowLiteralNestedCell E I O system S L H W) →
  Helical.Transverse E (Physical.p (outer C))
    (innerPairedForcing E I O system S L H W C)
innerPairedForcingTransverseAtOuterForcing E I O system S L H W C =
  subst
    (λ mode → Helical.Transverse E mode
      (innerPairedForcing E I O system S L H W C))
    (innerOutputIsOuterForcing C)
    (innerPairedForcingTransverseAtInnerOutput E I O system S L H W C)

transverseToNormalizedDirection :
  (E : C3.IntegerEmbedding F)
  (S : Helical.HelicalModeScalars F)
  (mode : Z3.FourierMode)
  (value : C3.Complex3 F) →
  Helical.Transverse E mode value →
  C3.bilinearDot3 value (R167.normalizedDirection E S mode)
  ≡ C3.complexZero F
transverseToNormalizedDirection E S mode value transverse =
  let
    scalar = C3.realEmbed F (Helical.inverseModeNorm S mode)
    wave = C3.modeVector E mode
  in
  trans
    (Scaling.bilinearDot3ScaleRight scalar value wave)
    (trans
      (cong (C3.complexMultiply scalar)
        (trans
          (Algebra.bilinearDot3Commutative value wave)
          transverse))
      (Field.complexMultiplyZeroRight scalar))

outerTransverseHighPair :
  (E : C3.IntegerEmbedding F)
  (I : C3.ModeInverseSquare F E)
  (O : Leray.RationalInverseNormOrder E I)
  (system : Audit.FiniteComplex3GalerkinSystem F E I)
  (S : Helical.HelicalModeScalars F)
  (L : Helical.PeriodicHelicalProjectorLaws F E I S)
  (H : R142.HelicalHalfCalibration S)
  (W : R294.SwapInvariantCellWeight F)
  (C : StrongLowLiteralNestedCell E I O system S L H W) →
  R145.TransverseHighPair
    (R167.normalizedDirection E S (Physical.p (outer C)))
    (R167.normalizedDirection E S (Physical.q (outer C)))
    (innerPairedForcing E I O system S L H W C)
    (Audit.velocity system (Physical.q (outer C)))
outerTransverseHighPair E I O system S L H W C = record
  { R145.aTransverseP =
      transverseToNormalizedDirection E S (Physical.p (outer C))
        (innerPairedForcing E I O system S L H W C)
        (innerPairedForcingTransverseAtOuterForcing E I O system S L H W C)
  ; R145.bTransverseQ =
      transverseToNormalizedDirection E S (Physical.q (outer C))
        (Audit.velocity system (Physical.q (outer C)))
        (outerQTransverse C)
  }

literalNestedOuterSlot :
  (E : C3.IntegerEmbedding F)
  (I : C3.ModeInverseSquare F E)
  (O : Leray.RationalInverseNormOrder E I)
  (system : Audit.FiniteComplex3GalerkinSystem F E I)
  (S : Helical.HelicalModeScalars F)
  (L : Helical.PeriodicHelicalProjectorLaws F E I S)
  (H : R142.HelicalHalfCalibration S)
  (W : R294.SwapInvariantCellWeight F) →
  StrongLowLiteralNestedCell E I O system S L H W → C3.Complex3 F
literalNestedOuterSlot E I O system S L H W C =
  R145.slotKernel
    (R167.normalizedDirection E S (Physical.p (outer C)))
    (R167.normalizedDirection E S (Physical.q (outer C)))
    (innerPairedForcing E I O system S L H W C)
    (Audit.velocity system (Physical.q (outer C)))

outerAntiParallelDefect :
  (E : C3.IntegerEmbedding F)
  (I : C3.ModeInverseSquare F E)
  (O : Leray.RationalInverseNormOrder E I)
  (system : Audit.FiniteComplex3GalerkinSystem F E I)
  (S : Helical.HelicalModeScalars F)
  (L : Helical.PeriodicHelicalProjectorLaws F E I S)
  (H : R142.HelicalHalfCalibration S)
  (W : R294.SwapInvariantCellWeight F) →
  StrongLowLiteralNestedCell E I O system S L H W → C3.Complex3 F
outerAntiParallelDefect E I O system S L H W C =
  R145.antiParallelDefect
    (R167.normalizedDirection E S (Physical.p (outer C)))
    (R167.normalizedDirection E S (Physical.q (outer C)))

literalNestedOuterSlotFactorsThroughAntiParallelDefect :
  (E : C3.IntegerEmbedding F)
  (I : C3.ModeInverseSquare F E)
  (O : Leray.RationalInverseNormOrder E I)
  (system : Audit.FiniteComplex3GalerkinSystem F E I)
  (S : Helical.HelicalModeScalars F)
  (L : Helical.PeriodicHelicalProjectorLaws F E I S)
  (H : R142.HelicalHalfCalibration S)
  (W : R294.SwapInvariantCellWeight F)
  (C : StrongLowLiteralNestedCell E I O system S L H W) →
  literalNestedOuterSlot E I O system S L H W C
  ≡
  C3.complex3Subtract
    (C3.complex3Add
      (C3.complex3Scale
        (C3.bilinearDot3
          (outerAntiParallelDefect E I O system S L H W C)
          (Audit.velocity system (Physical.q (outer C))))
        (innerPairedForcing E I O system S L H W C))
      (C3.complex3Scale
        (C3.bilinearDot3
          (innerPairedForcing E I O system S L H W C)
          (outerAntiParallelDefect E I O system S L H W C))
        (Audit.velocity system (Physical.q (outer C)))))
    (C3.complex3Scale
      (C3.bilinearDot3
        (innerPairedForcing E I O system S L H W C)
        (Audit.velocity system (Physical.q (outer C))))
      (outerAntiParallelDefect E I O system S L H W C))
literalNestedOuterSlotFactorsThroughAntiParallelDefect
    E I O system S L H W C =
  R145.slotKernelFactorsThroughAntiParallelDefect
    (R167.normalizedDirection E S (Physical.p (outer C)))
    (R167.normalizedDirection E S (Physical.q (outer C)))
    (innerPairedForcing E I O system S L H W C)
    (Audit.velocity system (Physical.q (outer C)))
    (outerTransverseHighPair E I O system S L H W C)

literalWeightedNestedCell :
  (E : C3.IntegerEmbedding F)
  (I : C3.ModeInverseSquare F E)
  (O : Leray.RationalInverseNormOrder E I)
  (system : Audit.FiniteComplex3GalerkinSystem F E I)
  (S : Helical.HelicalModeScalars F)
  (L : Helical.PeriodicHelicalProjectorLaws F E I S)
  (H : R142.HelicalHalfCalibration S)
  (W : R294.SwapInvariantCellWeight F) →
  StrongLowLiteralNestedCell E I O system S L H W → C3.Complex3 F
literalWeightedNestedCell E I O system S L H W C =
  C3.complex3Scale
    (R294.weight W (outer C))
    (literalNestedOuterSlot E I O system S L H W C)

innerPhysicalMajorant :
  (E : C3.IntegerEmbedding F)
  (I : C3.ModeInverseSquare F E)
  (O : Leray.RationalInverseNormOrder E I)
  (system : Audit.FiniteComplex3GalerkinSystem F E I)
  (S : Helical.HelicalModeScalars F)
  (L : Helical.PeriodicHelicalProjectorLaws F E I S)
  (H : R142.HelicalHalfCalibration S)
  (W : R294.SwapInvariantCellWeight F)
  (C : StrongLowLiteralNestedCell E I O system S L H W) →
  L2.complex3NormSquared (innerPairedForcing E I O system S L H W C)
  ≤ R178.nine * C3.normSquared I (Physical.k (inner C))
      * L2.complex3NormSquared (Audit.velocity system (Physical.p (inner C)))
      * L2.complex3NormSquared (Audit.velocity system (Physical.q (inner C)))
innerPhysicalMajorant E I O system S L H W C =
  R326.physicalInnerPureCommutatorLowOutputBound
    E I O system (inner C) (innerHelical C)
    (innerPTransverse C) (innerQTransverse C)

round329LiteralNestedPhysicalCarrierClosed : Bool
round329LiteralNestedPhysicalCarrierClosed = true

round329R294SwapInvariantWeightPreserved : Bool
round329R294SwapInvariantWeightPreserved = true

round329R326CellMajorantAttachedBeforeAggregation : Bool
round329R326CellMajorantAttachedBeforeAggregation = true

round329InnerPairedForcingTransverseAtOuterForcing : Bool
round329InnerPairedForcingTransverseAtOuterForcing = true

round329OuterQTransversalityRetained : Bool
round329OuterQTransversalityRetained = true

round329OuterAntiParallelFactorizationPhysicallyApplicable : Bool
round329OuterAntiParallelFactorizationPhysicallyApplicable = true

round329LiteralOuterSlotAntiParallelFactorized : Bool
round329LiteralOuterSlotAntiParallelFactorized = true

round329RowBudgetClosed : Bool
round329RowBudgetClosed = false

round329ColumnBudgetClosed : Bool
round329ColumnBudgetClosed = false

round329PackageAClosed : Bool
round329PackageAClosed = false

round329ClayPromotion : Bool
round329ClayPromotion = false

round329InnerPairedForcingTransverseAtOuterForcingIsTrue :
  round329InnerPairedForcingTransverseAtOuterForcing ≡ true
round329InnerPairedForcingTransverseAtOuterForcingIsTrue = refl

round329OuterAntiParallelFactorizationPhysicallyApplicableIsTrue :
  round329OuterAntiParallelFactorizationPhysicallyApplicable ≡ true
round329OuterAntiParallelFactorizationPhysicallyApplicableIsTrue = refl

round329LiteralOuterSlotAntiParallelFactorizedIsTrue :
  round329LiteralOuterSlotAntiParallelFactorized ≡ true
round329LiteralOuterSlotAntiParallelFactorizedIsTrue = refl
