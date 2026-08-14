module DASHI.Physics.YangMills.BalabanSelectedCorrelatedJointSingletonClosureExact where

-- Tadeusz Bałaban, "The Variational Problem and Background Fields in
-- Renormalization Group Method for Lattice Gauge Theories", CMP 102 (1985),
-- 277--309. DOI: 10.1007/BF01229381.
-- Tadeusz Bałaban, "Propagators for Lattice Gauge Theories in a Background
-- Field", CMP 99 (1985), 389--434. DOI: 10.1007/BF01240355.
-- Roger Penrose, "A Generalized Inverse for Matrices", Proc. Cambridge
-- Philos. Soc. 51 (1955), 406--413. DOI: 10.1017/S0305004100030401.

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _*_; _≤_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Coordinates
import DASHI.Physics.YangMills.BalabanP33PhysicalWilsonLinearNonlinearPartitionExact as Partition
import DASHI.Physics.YangMills.BalabanP33PhysicalWilsonSignedGlobalExact as Wilson
import DASHI.Physics.YangMills.BalabanP33FiniteKKTAdmissibleProjectorExact as KKT
import DASHI.Physics.YangMills.BalabanP33FiniteKKTPseudoinverseProjectorExact as Pseudo
import DASHI.Physics.YangMills.BalabanP33PlaquetteBoundaryProjectorExact as Boundary
import DASHI.Physics.YangMills.BalabanSelectedBackgroundVariationSelectorExact as Selector
import DASHI.Physics.YangMills.BalabanSelectedVariationSignConventionExact as Sign
import DASHI.Physics.YangMills.BalabanSelectedCorrelatedResidualOwnershipExact as Ownership
import DASHI.Physics.YangMills.BalabanSelectedCorrelatedResidualAuthorityExact as Authority
import DASHI.Physics.YangMills.BalabanP33JointCorrelatedResidualExact as Joint

literalRawExtractor : Coordinates.PhysicalSU2BondField4 → Physical.Plaquette4 → KKT.StateVector
literalRawExtractor = Boundary.rawPlaquetteSingletonExtractor

record JointCorrelatedSingletonExtractionData
    (background : Physical.RationalSU2Background4)
    (bondField : Coordinates.PhysicalSU2BondField4)
    (plaquette : Physical.Plaquette4) : Set₂ where
  field
    Multiplier : Set
    pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier
    firstVariationCovector : KKT.StateVector
    residualAuthority : Authority.CorrelatedResidualAuthority pseudoData firstVariationCovector (literalRawExtractor bondField plaquette)
    FineVariation : Set
    variation : FineVariation
    GaugeAdmissible ConstraintTangent SupportedNearPlaquette : FineVariation → Set
    gaugeAdmissible : GaugeAdmissible variation
    constraintTangent : ConstraintTangent variation
    localSupport : SupportedNearPlaquette variation
    variationNormSq : FineVariation → ℚ
    selectorConstant : ℚ
    selectorConstantNonnegative : 0ℚ ≤ selectorConstant
    variationChargeBound : variationNormSq variation ≤ selectorConstant * Wilson.plaquetteCrossCharge bondField plaquette
    firstVariation : FineVariation → ℚ
    selectedEulerLagrangeStationary : firstVariation variation ≡ 0ℚ
    projectedVariationExact :
      firstVariation variation ≡ Partition.physicalPlaquetteWilsonLinearPart background bondField plaquette
        + Sign.canonicalProjectedSpillover
            (Authority.rawLocalization residualAuthority)
            (Authority.canonicalMultiplierGreenPairing pseudoData firstVariationCovector (literalRawExtractor bondField plaquette))
    exactCancellation : Ownership.ExactCorrelatedCancellation (Authority.canonicalCorrelatedResidualFamily residualAuthority)
    jointResidualUpper :
      Joint.jointResidual (Authority.canonicalCorrelatedResidualFamily residualAuthority)
      ≤ Selector.remainingSingletonCoefficient * Wilson.plaquetteCrossCharge bondField plaquette
open JointCorrelatedSingletonExtractionData public

jointTotalResidualUpper :
  ∀ {background bondField plaquette} →
  (d : JointCorrelatedSingletonExtractionData background bondField plaquette) →
  Ownership.correlatedResidualTotal (Authority.canonicalCorrelatedResidualFamily (residualAuthority d))
  ≤ Selector.remainingSingletonCoefficient * Wilson.plaquetteCrossCharge bondField plaquette
jointTotalResidualUpper {bondField = bondField} {plaquette = plaquette} d =
  subst
    (λ lower → lower ≤ Selector.remainingSingletonCoefficient * Wilson.plaquetteCrossCharge bondField plaquette)
    (sym (Joint.jointResidualIsPhysicalTotal (exactCancellation d)))
    (jointResidualUpper d)

selectedSingletonResidualBudgetJointExact :
  ∀ {background bondField plaquette} →
  (d : JointCorrelatedSingletonExtractionData background bondField plaquette) →
  Sign.canonicalProjectedSpillover
    (Authority.rawLocalization (residualAuthority d))
    (Authority.canonicalMultiplierGreenPairing (pseudoData d) (firstVariationCovector d) (literalRawExtractor bondField plaquette))
  ≤ Selector.remainingSingletonCoefficient * Wilson.plaquetteCrossCharge bondField plaquette
selectedSingletonResidualBudgetJointExact {bondField = bondField} {plaquette = plaquette} d =
  subst
    (λ lower → lower ≤ Selector.remainingSingletonCoefficient * Wilson.plaquetteCrossCharge bondField plaquette)
    (Authority.canonicalCorrelatedResidualIsProjectedSpillover (residualAuthority d))
    (jointTotalResidualUpper d)

jointCorrelatedSingletonExtractionWitness :
  ∀ {background bondField plaquette} →
  JointCorrelatedSingletonExtractionData background bondField plaquette →
  Selector.SingletonExtractionWitness background bondField plaquette
jointCorrelatedSingletonExtractionWitness {bondField = bondField} {plaquette = plaquette} d = record
  { Selector.SingletonExtractionWitness.FineVariation = FineVariation d
  ; Selector.SingletonExtractionWitness.variation = variation d
  ; Selector.SingletonExtractionWitness.GaugeAdmissible = GaugeAdmissible d
  ; Selector.SingletonExtractionWitness.ConstraintTangent = ConstraintTangent d
  ; Selector.SingletonExtractionWitness.SupportedNearPlaquette = SupportedNearPlaquette d
  ; Selector.SingletonExtractionWitness.gaugeAdmissible = gaugeAdmissible d
  ; Selector.SingletonExtractionWitness.constraintTangent = constraintTangent d
  ; Selector.SingletonExtractionWitness.localSupport = localSupport d
  ; Selector.SingletonExtractionWitness.variationNormSq = variationNormSq d
  ; Selector.SingletonExtractionWitness.selectorConstant = selectorConstant d
  ; Selector.SingletonExtractionWitness.selectorConstantNonnegative = selectorConstantNonnegative d
  ; Selector.SingletonExtractionWitness.variationChargeBound = variationChargeBound d
  ; Selector.SingletonExtractionWitness.firstVariation = firstVariation d
  ; Selector.SingletonExtractionWitness.extractionSpillover =
      Sign.canonicalProjectedSpillover (Authority.rawLocalization (residualAuthority d))
        (Authority.canonicalMultiplierGreenPairing (pseudoData d) (firstVariationCovector d) (literalRawExtractor bondField plaquette))
  ; Selector.SingletonExtractionWitness.selectedEulerLagrangeStationary = selectedEulerLagrangeStationary d
  ; Selector.SingletonExtractionWitness.extractsLiteralSingleton = projectedVariationExact d
  ; Selector.SingletonExtractionWitness.spilloverUpper = selectedSingletonResidualBudgetJointExact d }

selectedJointCorrelatedSingletonClosureLevel : ProofLevel
selectedJointCorrelatedSingletonClosureLevel = machineChecked
selectedPhysicalJointCorrelatedSingletonProducerLevel : ProofLevel
selectedPhysicalJointCorrelatedSingletonProducerLevel = conditional
