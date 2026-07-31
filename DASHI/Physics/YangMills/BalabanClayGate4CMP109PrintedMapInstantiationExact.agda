module DASHI.Physics.YangMills.BalabanClayGate4CMP109PrintedMapInstantiationExact where

open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayGate4PrimaryAveragingDimensionAuditExact as Dimension
import DASHI.Physics.YangMills.BalabanClayGate4PrimaryAveragingLocalityExact as Locality
import DASHI.Physics.YangMills.BalabanClayGate4SU2PrincipalLogBallExact as PrincipalLog
import DASHI.Physics.YangMills.BalabanClayGate4CMP109LiteralIdentificationAssemblyExact as Literal
import DASHI.Physics.YangMills.BalabanClayGate4CMP109PrintedPathFormulaExact as Printed

------------------------------------------------------------------------
-- Canonical instantiation of the repository one-step formula by CMP 109
-- equation (0.12).
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (2) (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- The previous frontier allowed an arbitrary proposition named
-- `LiteralMapMatchesCMP109`.  Here the proposition is fixed to propositional
-- equality with the executable equation-(0.12) fold.  The local averaging stage
-- and the primary formula are constructed with that fold as their definition,
-- so their printed-map equality is `refl`; only the physical field, support,
-- principal-log, derivative and normalization inhabitants remain to be chosen.
------------------------------------------------------------------------

record CanonicalEquation012StageInputs
    (Field FineBond CoarseBond FineSite Group Lie Scalar : Set) : Set₁ where
  field
    printedData : Printed.PrintedCMP109Equation012Data
      Field CoarseBond FineSite Group Lie Scalar

    inputValue : Field → FineBond → Group

    ProjectedEndpointSupport : CoarseBond → FineBond → Set

    printedMapLocalDependence :
      ∀ (left right : Field) (coarse : CoarseBond) →
      (∀ fine → ProjectedEndpointSupport coarse fine →
        inputValue left fine ≡ inputValue right fine) →
      Printed.printedEquation012Map printedData left coarse
      ≡ Printed.printedEquation012Map printedData right coarse

    transportedLog : Field → CoarseBond → FineBond → Lie

open CanonicalEquation012StageInputs public

canonicalEquation012LocalStage :
  ∀ {Field FineBond CoarseBond FineSite Group Lie Scalar} →
  CanonicalEquation012StageInputs
    Field FineBond CoarseBond FineSite Group Lie Scalar →
  Locality.LocalAveragingStage
    Field (CoarseBond → Group) FineBond CoarseBond Group
canonicalEquation012LocalStage inputs = record
  { Locality.LocalAveragingStage.inputValue = inputValue inputs
  ; Locality.LocalAveragingStage.outputValue = λ output coarse → output coarse
  ; Locality.LocalAveragingStage.average =
      Printed.printedEquation012Map (printedData inputs)
  ; Locality.LocalAveragingStage.Support = ProjectedEndpointSupport inputs
  ; Locality.LocalAveragingStage.localDependence =
      printedMapLocalDependence inputs
  }

canonicalEquation012OneStepFormula :
  ∀ {Field FineBond CoarseBond FineSite Group Lie Scalar}
    (inputs : CanonicalEquation012StageInputs
      Field FineBond CoarseBond FineSite Group Lie Scalar) →
  Locality.BalabanPrimaryOneStepFormula
    Field (CoarseBond → Group) FineBond CoarseBond Group Lie
canonicalEquation012OneStepFormula inputs = record
  { Locality.BalabanPrimaryOneStepFormula.localStage =
      canonicalEquation012LocalStage inputs
  ; Locality.BalabanPrimaryOneStepFormula.transportedLog =
      transportedLog inputs
  ; Locality.BalabanPrimaryOneStepFormula.weightedLocalLogSum =
      Printed.printedEquation012LieAverage (printedData inputs)
  ; Locality.BalabanPrimaryOneStepFormula.exponential =
      Printed.outerExponential (printedData inputs)
  ; Locality.BalabanPrimaryOneStepFormula.multiply =
      Printed.multiplyGroup (printedData inputs)
  ; Locality.BalabanPrimaryOneStepFormula.endpointValue =
      Printed.coarseBondValue (printedData inputs)
  ; Locality.BalabanPrimaryOneStepFormula.primaryFormula =
      λ field coarse → refl
  ; Locality.BalabanPrimaryOneStepFormula.coefficientConvention =
      Dimension.volumeDimensionExponent
  ; Locality.BalabanPrimaryOneStepFormula.coefficientConventionExact = refl
  }

canonicalProjectedEndpointLocality :
  ∀ {Field FineBond CoarseBond FineSite Group Lie Scalar}
    (inputs : CanonicalEquation012StageInputs
      Field FineBond CoarseBond FineSite Group Lie Scalar) →
  Literal.ProjectedEndpointLocality
    Field (CoarseBond → Group) FineBond CoarseBond Group
canonicalProjectedEndpointLocality inputs = record
  { Literal.ProjectedEndpointLocality.stage =
      canonicalEquation012LocalStage inputs
  ; Literal.ProjectedEndpointLocality.ProjectedEndpointSupport =
      ProjectedEndpointSupport inputs
  ; Literal.ProjectedEndpointLocality.supportMatchesProjectedEndpoints =
      λ coarse fine → refl
  }

record CanonicalCMP109PrintedIdentificationInputs
    (Field FineBond CoarseBond FineSite Group Lie Scalar Radius Entry
      Normalization : Set) : Set₁ where
  field
    stageInputs : CanonicalEquation012StageInputs
      Field FineBond CoarseBond FineSite Group Lie Scalar

    principalLogMeaning : PrincipalLog.PhysicalSU2PrincipalLogMeaning
      Field CoarseBond FineBond Lie Group Radius

    derivativeEntry : CoarseBond → FineBond → Entry
    zeroDerivativeEntry : Entry

    derivativeVanishesOutsideProjectedSupport : ∀ coarse fine →
      Literal.Not
        (ProjectedEndpointSupport stageInputs coarse fine) →
      derivativeEntry coarse fine ≡ zeroDerivativeEntry

    physicalNormalization : Normalization

open CanonicalCMP109PrintedIdentificationInputs public

canonicalCMP109LiteralIdentification :
  ∀ {Field FineBond CoarseBond FineSite Group Lie Scalar Radius Entry
      Normalization}
    (inputs : CanonicalCMP109PrintedIdentificationInputs
      Field FineBond CoarseBond FineSite Group Lie Scalar Radius Entry
      Normalization) →
  Literal.CMP109LiteralIdentification
    Field (CoarseBond → Group) FineBond CoarseBond Group Lie Group Radius Entry
    Normalization
canonicalCMP109LiteralIdentification inputs = record
  { Literal.CMP109LiteralIdentification.oneStepFormula =
      canonicalEquation012OneStepFormula (stageInputs inputs)
  ; Literal.CMP109LiteralIdentification.projectedLocality =
      canonicalProjectedEndpointLocality (stageInputs inputs)
  ; Literal.CMP109LiteralIdentification.formulaStageMatchesLocality = refl
  ; Literal.CMP109LiteralIdentification.principalLogMeaning =
      principalLogMeaning inputs
  ; Literal.CMP109LiteralIdentification.derivativeEntry =
      derivativeEntry inputs
  ; Literal.CMP109LiteralIdentification.zeroDerivativeEntry =
      zeroDerivativeEntry inputs
  ; Literal.CMP109LiteralIdentification.derivativeVanishesOutsideProjectedSupport =
      derivativeVanishesOutsideProjectedSupport inputs
  ; Literal.CMP109LiteralIdentification.physicalNormalization =
      physicalNormalization inputs
  ; Literal.CMP109LiteralIdentification.LiteralMapMatchesCMP109 =
      λ candidate →
        candidate
        ≡ Printed.printedEquation012Map
            (printedData (stageInputs inputs))
  ; Literal.CMP109LiteralIdentification.DerivativeMatchesCMP109 =
      λ candidate → candidate ≡ derivativeEntry inputs
  ; Literal.CMP109LiteralIdentification.SupportMatchesCMP109 =
      λ candidate →
        candidate ≡ ProjectedEndpointSupport (stageInputs inputs)
  ; Literal.CMP109LiteralIdentification.NormalizationMatchesCMP109 =
      λ candidate → candidate ≡ physicalNormalization inputs
  ; Literal.CMP109LiteralIdentification.literalMapMatchesCMP109 = refl
  ; Literal.CMP109LiteralIdentification.derivativeMatchesCMP109 = refl
  ; Literal.CMP109LiteralIdentification.supportMatchesCMP109 = refl
  ; Literal.CMP109LiteralIdentification.normalizationMatchesCMP109 = refl
  }

cmp109Equation012CanonicalStageLevel : ProofLevel
cmp109Equation012CanonicalStageLevel = machineChecked

cmp109Equation012PrimaryFormulaLevel : ProofLevel
cmp109Equation012PrimaryFormulaLevel = machineChecked

cmp109PrintedMapEqualityByConstructionLevel : ProofLevel
cmp109PrintedMapEqualityByConstructionLevel = machineChecked

cmp109UnifiedEqualityPredicateLevel : ProofLevel
cmp109UnifiedEqualityPredicateLevel = machineChecked

physicalCMP109Equation012LocalDependenceInputsLevel : ProofLevel
physicalCMP109Equation012LocalDependenceInputsLevel = conditional

physicalCMP109DerivativeAndNormalizationInputsLevel : ProofLevel
physicalCMP109DerivativeAndNormalizationInputsLevel = conditional
