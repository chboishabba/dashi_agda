module DASHI.Physics.YangMills.BalabanClayGate4CMP109DyadicGroupAveragePhysicalExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayGate4CMP109DyadicPrintedPhysicalInstantiationExact as DyadicPrinted
import DASHI.Physics.YangMills.BalabanClayGate4CMP109Equation012GroupAverageAdapterExact as GroupAdapter
import DASHI.Physics.YangMills.BalabanClayGate4CMP109PrintedPathFormulaExact as Printed
import DASHI.Physics.YangMills.BalabanClayGate4CMP109LiteralIdentificationAssemblyExact as Literal
import DASHI.Physics.YangMills.BalabanClayGate4SU2PrincipalLogBallExact as PrincipalLog

------------------------------------------------------------------------
-- Dyadic physical instance with equation-(0.11) contour averages fixed.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (2) (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- This adapter removes the last freedom to choose arbitrary source and target
-- values in equation (0.12).  They are definitionally the equation-(0.11)
-- group averages of the selected finite path-holonomy families.  The remaining
-- physical inputs are local dependence, chart admission and the differentiated
-- chain rule, not the definition of the map itself.
------------------------------------------------------------------------

record DyadicGroupAveragePhysicalInputs
    (coarseN : Nat)
    (Field Path Group Lie Scalar Radius Entry : Set) : Set₁ where
  field
    equation012 : GroupAdapter.Equation012GroupAverageInputs
      Field (DyadicPrinted.CoarseBond coarseN)
      (DyadicPrinted.FineSite coarseN)
      Path Group Lie Scalar

    inputValue :
      Field → DyadicPrinted.FineBond coarseN → Group

    printedMapLocalDependence :
      ∀ (left right : Field)
        (coarse : DyadicPrinted.CoarseBond coarseN) →
      (∀ fine → DyadicPrinted.DyadicEndpointSupport coarseN coarse fine →
        inputValue left fine ≡ inputValue right fine) →
      Printed.printedEquation012Map
        (GroupAdapter.asPrintedEquation012Data equation012) left coarse
      ≡ Printed.printedEquation012Map
          (GroupAdapter.asPrintedEquation012Data equation012) right coarse

    principalLogMeaning : PrincipalLog.PhysicalSU2PrincipalLogMeaning
      Field (DyadicPrinted.CoarseBond coarseN)
      (DyadicPrinted.FineBond coarseN)
      Lie Group Radius

    crossingFineBond :
      DyadicPrinted.CoarseBond coarseN →
      DyadicPrinted.FineSite coarseN →
      DyadicPrinted.FineBond coarseN

    printedRelativeProductUsesPhysicalPrincipalLog :
      ∀ field coarse fineSite →
      PrincipalLog.physicalLog principalLogMeaning
        field coarse (crossingFineBond coarse fineSite)
      ≡ Printed.antiHermitianLogCoordinate
          (GroupAdapter.asPrintedEquation012Data equation012)
          (Printed.printedEquation012RelativeProduct
            (GroupAdapter.asPrintedEquation012Data equation012)
            field coarse fineSite)

    derivativeEntry :
      DyadicPrinted.CoarseBond coarseN →
      DyadicPrinted.FineBond coarseN → Entry

    zeroDerivativeEntry : Entry

    derivativeVanishesOutsideDyadicSupport : ∀ coarse fine →
      Literal.Not
        (DyadicPrinted.DyadicEndpointSupport coarseN coarse fine) →
      derivativeEntry coarse fine ≡ zeroDerivativeEntry

open DyadicGroupAveragePhysicalInputs public

asDyadicPrintedPhysicalInputs :
  ∀ {coarseN Field Path Group Lie Scalar Radius Entry} →
  DyadicGroupAveragePhysicalInputs
    coarseN Field Path Group Lie Scalar Radius Entry →
  DyadicPrinted.DyadicCMP109PrintedPhysicalInputs
    coarseN Field Group Lie Scalar Radius Entry
asDyadicPrintedPhysicalInputs inputs = record
  { DyadicPrinted.DyadicCMP109PrintedPhysicalInputs.printedData =
      GroupAdapter.asPrintedEquation012Data (equation012 inputs)
  ; DyadicPrinted.DyadicCMP109PrintedPhysicalInputs.inputValue =
      inputValue inputs
  ; DyadicPrinted.DyadicCMP109PrintedPhysicalInputs.printedMapLocalDependence =
      printedMapLocalDependence inputs
  ; DyadicPrinted.DyadicCMP109PrintedPhysicalInputs.principalLogMeaning =
      principalLogMeaning inputs
  ; DyadicPrinted.DyadicCMP109PrintedPhysicalInputs.crossingFineBond =
      crossingFineBond inputs
  ; DyadicPrinted.DyadicCMP109PrintedPhysicalInputs.printedRelativeProductUsesPhysicalPrincipalLog =
      printedRelativeProductUsesPhysicalPrincipalLog inputs
  ; DyadicPrinted.DyadicCMP109PrintedPhysicalInputs.derivativeEntry =
      derivativeEntry inputs
  ; DyadicPrinted.DyadicCMP109PrintedPhysicalInputs.zeroDerivativeEntry =
      zeroDerivativeEntry inputs
  ; DyadicPrinted.DyadicCMP109PrintedPhysicalInputs.derivativeVanishesOutsideDyadicSupport =
      derivativeVanishesOutsideDyadicSupport inputs
  }

dyadicGroupAverageLiteralIdentification :
  ∀ {coarseN Field Path Group Lie Scalar Radius Entry}
    (inputs : DyadicGroupAveragePhysicalInputs
      coarseN Field Path Group Lie Scalar Radius Entry) →
  Literal.CMP109LiteralIdentification
    Field (DyadicPrinted.CoarseBond coarseN → Group)
    (DyadicPrinted.FineBond coarseN)
    (DyadicPrinted.CoarseBond coarseN)
    Group Lie Group Radius Entry
    DASHI.Physics.YangMills.BalabanClayGate4CMP109DyadicProjectionNormalizationExact.CMP109Dyadic4Normalization
dyadicGroupAverageLiteralIdentification inputs =
  DyadicPrinted.dyadicCMP109LiteralIdentification
    (asDyadicPrintedPhysicalInputs inputs)

cmp109DyadicEquation011ContourFixingLevel : ProofLevel
cmp109DyadicEquation011ContourFixingLevel = machineChecked

cmp109DyadicEquation012GroupAverageIdentificationLevel : ProofLevel
cmp109DyadicEquation012GroupAverageIdentificationLevel = machineChecked

physicalCMP109DyadicLocalDependenceInputsLevel : ProofLevel
physicalCMP109DyadicLocalDependenceInputsLevel = conditional

physicalCMP109DyadicChartAndDerivativeInputsLevel : ProofLevel
physicalCMP109DyadicChartAndDerivativeInputsLevel = conditional
