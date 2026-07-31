module DASHI.Physics.YangMills.BalabanClayGate4CMP109DyadicPrintedPhysicalInstantiationExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; suc)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
  using (PositiveBond)

import DASHI.Physics.YangMills.BalabanClayT2PeriodicBlockPolymerCarrierExact as Periodic
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicEndpointBlockPredicateExact as Endpoint
import DASHI.Physics.YangMills.BalabanClayGate4CMP109DyadicProjectionNormalizationExact as Dyadic
import DASHI.Physics.YangMills.BalabanClayGate4CMP109DyadicSupportBudgetsExact as Support
import DASHI.Physics.YangMills.BalabanClayGate4CMP109PrintedPathFormulaExact as Printed
import DASHI.Physics.YangMills.BalabanClayGate4CMP109PrintedMapInstantiationExact as Instantiation
import DASHI.Physics.YangMills.BalabanClayGate4CMP109LiteralIdentificationAssemblyExact as Literal
import DASHI.Physics.YangMills.BalabanClayGate4SU2PrincipalLogBallExact as PrincipalLog

------------------------------------------------------------------------
-- Canonical CMP109 equation-(0.12) instance on the exact dyadic four-torus.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (2) (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- The generic printed-map adapter previously left support and normalization as
-- arbitrary fields.  This module fixes them to the exact one-step dyadic
-- projection, endpoint-union support and 1/16 four-dimensional block
-- normalization.  The primary formula's transported logarithm is now the
-- literal physical principal logarithm, and a termwise field identifies it with
-- the logarithm of the equation-(0.12) relative product.  Thus map, chart,
-- support and normalization cannot be inhabited by mutually inconsistent
-- conventions.
------------------------------------------------------------------------

FineBond : Nat → Set
FineBond coarseN = PositiveBond (suc (Dyadic.dyadicFineN coarseN))

CoarseBond : Nat → Set
CoarseBond coarseN = PositiveBond (suc coarseN)

FineSite : Nat → Set
FineSite coarseN = Periodic.PeriodicBlock (Dyadic.dyadicFineN coarseN)

DyadicEndpointSupport :
  ∀ coarseN → CoarseBond coarseN → FineBond coarseN → Set
DyadicEndpointSupport coarseN =
  Endpoint.EndpointBlockUnionSupport
    (Support.dyadicEndpointGeometry coarseN)

record DyadicCMP109PrintedPhysicalInputs
    (coarseN : Nat)
    (Field Group Lie Scalar Radius Entry : Set) : Set₁ where
  field
    printedData : Printed.PrintedCMP109Equation012Data
      Field (CoarseBond coarseN) (FineSite coarseN) Group Lie Scalar

    inputValue : Field → FineBond coarseN → Group

    printedMapLocalDependence :
      ∀ (left right : Field) (coarse : CoarseBond coarseN) →
      (∀ fine → DyadicEndpointSupport coarseN coarse fine →
        inputValue left fine ≡ inputValue right fine) →
      Printed.printedEquation012Map printedData left coarse
      ≡ Printed.printedEquation012Map printedData right coarse

    principalLogMeaning : PrincipalLog.PhysicalSU2PrincipalLogMeaning
      Field (CoarseBond coarseN) (FineBond coarseN)
      Lie Group Radius

    crossingFineBond :
      CoarseBond coarseN → FineSite coarseN → FineBond coarseN

    printedRelativeProductUsesPhysicalPrincipalLog :
      ∀ field coarse fineSite →
      PrincipalLog.physicalLog principalLogMeaning
        field coarse (crossingFineBond coarse fineSite)
      ≡ Printed.antiHermitianLogCoordinate printedData
          (Printed.printedEquation012RelativeProduct
            printedData field coarse fineSite)

    derivativeEntry : CoarseBond coarseN → FineBond coarseN → Entry
    zeroDerivativeEntry : Entry

    derivativeVanishesOutsideDyadicSupport : ∀ coarse fine →
      Literal.Not (DyadicEndpointSupport coarseN coarse fine) →
      derivativeEntry coarse fine ≡ zeroDerivativeEntry

open DyadicCMP109PrintedPhysicalInputs public

dyadicCanonicalStageInputs :
  ∀ {coarseN Field Group Lie Scalar Radius Entry} →
  DyadicCMP109PrintedPhysicalInputs
    coarseN Field Group Lie Scalar Radius Entry →
  Instantiation.CanonicalEquation012StageInputs
    Field (FineBond coarseN) (CoarseBond coarseN) (FineSite coarseN)
    Group Lie Scalar
dyadicCanonicalStageInputs inputs = record
  { Instantiation.CanonicalEquation012StageInputs.printedData =
      printedData inputs
  ; Instantiation.CanonicalEquation012StageInputs.inputValue =
      inputValue inputs
  ; Instantiation.CanonicalEquation012StageInputs.ProjectedEndpointSupport =
      DyadicEndpointSupport _
  ; Instantiation.CanonicalEquation012StageInputs.printedMapLocalDependence =
      printedMapLocalDependence inputs
  ; Instantiation.CanonicalEquation012StageInputs.transportedLog =
      PrincipalLog.physicalLog (principalLogMeaning inputs)
  }

dyadicCanonicalPrintedIdentificationInputs :
  ∀ {coarseN Field Group Lie Scalar Radius Entry}
    (inputs : DyadicCMP109PrintedPhysicalInputs
      coarseN Field Group Lie Scalar Radius Entry) →
  Instantiation.CanonicalCMP109PrintedIdentificationInputs
    Field (FineBond coarseN) (CoarseBond coarseN) (FineSite coarseN)
    Group Lie Scalar Radius Entry Dyadic.CMP109Dyadic4Normalization
dyadicCanonicalPrintedIdentificationInputs inputs = record
  { Instantiation.CanonicalCMP109PrintedIdentificationInputs.stageInputs =
      dyadicCanonicalStageInputs inputs
  ; Instantiation.CanonicalCMP109PrintedIdentificationInputs.principalLogMeaning =
      principalLogMeaning inputs
  ; Instantiation.CanonicalCMP109PrintedIdentificationInputs.derivativeEntry =
      derivativeEntry inputs
  ; Instantiation.CanonicalCMP109PrintedIdentificationInputs.zeroDerivativeEntry =
      zeroDerivativeEntry inputs
  ; Instantiation.CanonicalCMP109PrintedIdentificationInputs.derivativeVanishesOutsideProjectedSupport =
      derivativeVanishesOutsideDyadicSupport inputs
  ; Instantiation.CanonicalCMP109PrintedIdentificationInputs.physicalNormalization =
      Dyadic.canonicalCMP109Dyadic4Normalization
  }

dyadicCMP109LiteralIdentification :
  ∀ {coarseN Field Group Lie Scalar Radius Entry}
    (inputs : DyadicCMP109PrintedPhysicalInputs
      coarseN Field Group Lie Scalar Radius Entry) →
  Literal.CMP109LiteralIdentification
    Field (CoarseBond coarseN → Group)
    (FineBond coarseN) (CoarseBond coarseN)
    Group Lie Group Radius Entry Dyadic.CMP109Dyadic4Normalization
dyadicCMP109LiteralIdentification inputs =
  Instantiation.canonicalCMP109LiteralIdentification
    (dyadicCanonicalPrintedIdentificationInputs inputs)

cmp109DyadicPrintedMapInstantiationLevel : ProofLevel
cmp109DyadicPrintedMapInstantiationLevel = machineChecked

cmp109DyadicSupportIdentificationLevel : ProofLevel
cmp109DyadicSupportIdentificationLevel = machineChecked

cmp109DyadicNormalizationIdentificationLevel : ProofLevel
cmp109DyadicNormalizationIdentificationLevel = machineChecked

cmp109DyadicPrincipalLogTermIdentificationLevel : ProofLevel
cmp109DyadicPrincipalLogTermIdentificationLevel = machineChecked

physicalCMP109ContourValueInputsLevel : ProofLevel
physicalCMP109ContourValueInputsLevel = conditional

physicalCMP109PrincipalChartInputsLevel : ProofLevel
physicalCMP109PrincipalChartInputsLevel = conditional

physicalCMP109FrechetKernelInputsLevel : ProofLevel
physicalCMP109FrechetKernelInputsLevel = conditional
