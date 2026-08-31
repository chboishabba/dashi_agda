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
-- This file contains no row sum, column sum, fibre cardinality, or heat
-- integrability claim.  It only prevents later Schur code from replacing the
-- physical nested object by a generic kernel proxy.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; _≤_)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNCriticalSlotQuadraticKernelRound167Exact as R167
import DASHI.Physics.Closure.NSTriadKNAntiParallelHelicitySlotKernelRound145Exact as R145
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNRationalComplex3LerayPythagoras as Leray
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNExternalPureCommutatorPartnerRound120Exact as R120
import DASHI.Physics.Closure.NSTriadKNNestedInnerSwapCommutatorRound310Exact as R310
import DASHI.Physics.Closure.NSTriadKNInnerStrongLowOutputSubconeRound321Exact as R321
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

    -- a+b=p at `inner`, then p+q=k at `outer`.
    innerOutputIsOuterForcing :
      Physical.k inner ≡ Physical.p outer

    innerHelical : R120.PhysicalHelicalOutputPair system inner
    innerPTransverse : Helical.Transverse E (Physical.p inner)
      (Audit.velocity system (Physical.p inner))
    innerQTransverse : Helical.Transverse E (Physical.q inner)
      (Audit.velocity system (Physical.q inner))

    -- Dyadic cross-layer receipt.  It is deliberately independent of the
    -- physical norm carrier; R321 already proved the exponent consequences.
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
  ≤ R326.R178.nine * C3.normSquared I (Physical.k (inner C))
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

round329RowBudgetClosed : Bool
round329RowBudgetClosed = false

round329ColumnBudgetClosed : Bool
round329ColumnBudgetClosed = false

round329PackageAClosed : Bool
round329PackageAClosed = false

round329ClayPromotion : Bool
round329ClayPromotion = false
