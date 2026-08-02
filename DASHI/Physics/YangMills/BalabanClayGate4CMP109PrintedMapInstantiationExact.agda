module DASHI.Physics.YangMills.BalabanClayGate4CMP109PrintedMapInstantiationExact where

open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayGate4PrimaryAveragingDimensionAuditExact as Dimension
import DASHI.Physics.YangMills.BalabanClayGate4PrimaryAveragingLocalityExact as Locality
import DASHI.Physics.YangMills.BalabanClayGate4SU2PrincipalLogBallExact as PrincipalLog
import DASHI.Physics.YangMills.BalabanClayGate4CMP109LiteralIdentificationAssemblyExact as Literal
import DASHI.Physics.YangMills.BalabanClayGate4CMP109PrintedPathFormulaExact as Printed

record SupportAgreement (left right : Set) : Set where
  constructor supportAgreement
  field
    forward : left → right
    backward : right → left

open SupportAgreement public

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
--
-- The support matching uses pointwise logical equivalence instead of
-- propositional equality: the support is `Set`-valued (`CoarseBond → FineBond →
-- Set`), so an equality predicate over it would live in `Set₁` while the
-- `CMP109LiteralIdentification.SupportMatchesCMP109` field is `Set`-valued.
-- Pointwise bi-implication stays `Set`-level, and at the witness site the
-- candidate is definitionally the reference, so both directions are identity.
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
  { inputValue = inputValue inputs
  ; outputValue = λ output coarse → output coarse
  ; average = Printed.printedEquation012Map (printedData inputs)
  ; Support = ProjectedEndpointSupport inputs
  ; localDependence = printedMapLocalDependence inputs
  }

canonicalEquation012OneStepFormula :
  ∀ {Field FineBond CoarseBond FineSite Group Lie Scalar}
    (inputs : CanonicalEquation012StageInputs
      Field FineBond CoarseBond FineSite Group Lie Scalar) →
  Locality.BalabanPrimaryOneStepFormula
    Field (CoarseBond → Group) FineBond CoarseBond Group Lie
canonicalEquation012OneStepFormula inputs = record
  { localStage = canonicalEquation012LocalStage inputs
  ; transportedLog = transportedLog inputs
  ; weightedLocalLogSum =
      Printed.printedEquation012LieAverage (printedData inputs)
  ; exponential = Printed.outerExponential (printedData inputs)
  ; multiply = Printed.multiplyGroup (printedData inputs)
  ; endpointValue = Printed.coarseBondValue (printedData inputs)
  ; primaryFormula = λ coarseField coarse → refl
  ; coefficientConvention = Dimension.volumeDimensionExponent
  ; coefficientConventionExact = refl
  }

canonicalProjectedEndpointLocality :
  ∀ {Field FineBond CoarseBond FineSite Group Lie Scalar}
    (inputs : CanonicalEquation012StageInputs
      Field FineBond CoarseBond FineSite Group Lie Scalar) →
  Literal.ProjectedEndpointLocality
    Field (CoarseBond → Group) FineBond CoarseBond Group
canonicalProjectedEndpointLocality inputs = record
  { stage = canonicalEquation012LocalStage inputs
  ; ProjectedEndpointSupport = ProjectedEndpointSupport inputs
  ; supportMatchesProjectedEndpoints = λ coarse fine → refl
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
  { oneStepFormula = canonicalEquation012OneStepFormula (stageInputs inputs)
  ; projectedLocality = canonicalProjectedEndpointLocality (stageInputs inputs)
  ; formulaStageMatchesLocality = refl
  ; principalLogMeaning = principalLogMeaning inputs
  ; derivativeEntry = derivativeEntry inputs
  ; zeroDerivativeEntry = zeroDerivativeEntry inputs
  ; derivativeVanishesOutsideProjectedSupport =
      derivativeVanishesOutsideProjectedSupport inputs
  ; physicalNormalization = physicalNormalization inputs
  ; LiteralMapMatchesCMP109 =
      λ candidate →
        candidate
        ≡ Printed.printedEquation012Map
            (printedData (stageInputs inputs))
  ; DerivativeMatchesCMP109 = λ candidate → candidate ≡ derivativeEntry inputs
  ; SupportMatchesCMP109 =
      λ candidate →
        ∀ coarse fine →
          SupportAgreement
            (candidate coarse fine)
            (ProjectedEndpointSupport (stageInputs inputs) coarse fine)
  ; NormalizationMatchesCMP109 =
      λ candidate → candidate ≡ physicalNormalization inputs
  ; literalMapMatchesCMP109 = refl
  ; derivativeMatchesCMP109 = refl
  ; supportMatchesCMP109 = λ coarse fine → supportAgreement (λ p → p) (λ p → p)
  ; normalizationMatchesCMP109 = refl
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
