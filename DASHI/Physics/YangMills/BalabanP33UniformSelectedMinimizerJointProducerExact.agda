module DASHI.Physics.YangMills.BalabanP33UniformSelectedMinimizerJointProducerExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "The Variational Problem and Background Fields in Renormalization Group
-- Method for Lattice Gauge Theories", Communications in Mathematical Physics
-- 102 (1985), 277--309. DOI: 10.1007/BF01229381.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- Ramon E. Moore, R. Baker Kearfott and Michael J. Cloud,
-- "Introduction to Interval Analysis", SIAM, 2009.
-- DOI: 10.1137/1.9780898717716.
--
-- DASHI CONTRIBUTION
--
-- Make the uniform selected-minimizer interval theorem PRODUCE the remaining
-- joint correlated-singleton bound instead of assuming it inside the physical
-- extraction object.  `JointExtractionCore` contains every literal physical
-- field except the numerical joint-residual inequality.  The uniform pair
-- enclosure is required to refer to the canonical residual family of this same
-- core at every configuration.  At the selected minimizer the certified region
-- theorem supplies the missing inequality, and only then is the full
-- `JointCorrelatedSingletonExtractionData` constructed.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _*_; _≤_)
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
import DASHI.Physics.YangMills.BalabanSelectedCorrelatedResidualAuthorityExact as Authority
import DASHI.Physics.YangMills.BalabanSelectedCorrelatedResidualOwnershipExact as Ownership
import DASHI.Physics.YangMills.BalabanP33UniformSelectedMinimizerPairEnclosureExact as Uniform
import DASHI.Physics.YangMills.BalabanSelectedCorrelatedJointSingletonClosureExact as JointClosure
import DASHI.Physics.YangMills.BalabanP33JointCorrelatedResidualExact as Joint

literalRawExtractor :
  Coordinates.PhysicalSU2BondField4 → Physical.Plaquette4 → KKT.StateVector
literalRawExtractor = Boundary.rawPlaquetteSingletonExtractor

record JointExtractionCore
    (background : Physical.RationalSU2Background4)
    (bondField : Coordinates.PhysicalSU2BondField4)
    (plaquette : Physical.Plaquette4) : Set₂ where
  field
    Multiplier : Set
    pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier
    firstVariationCovector : KKT.StateVector
    residualAuthority : Authority.CorrelatedResidualAuthority
      pseudoData firstVariationCovector (literalRawExtractor bondField plaquette)

    FineVariation : Set
    variation : FineVariation
    GaugeAdmissible ConstraintTangent SupportedNearPlaquette : FineVariation → Set
    gaugeAdmissible : GaugeAdmissible variation
    constraintTangent : ConstraintTangent variation
    localSupport : SupportedNearPlaquette variation

    variationNormSq : FineVariation → ℚ
    selectorConstant : ℚ
    selectorConstantNonnegative : 0ℚ ≤ selectorConstant
    variationChargeBound :
      variationNormSq variation
      ≤ selectorConstant * Wilson.plaquetteCrossCharge bondField plaquette

    firstVariation : FineVariation → ℚ
    selectedEulerLagrangeStationary : firstVariation variation ≡ 0ℚ
    projectedVariationExact :
      firstVariation variation
      ≡ Partition.physicalPlaquetteWilsonLinearPart background bondField plaquette
        + Sign.canonicalProjectedSpillover
            (Authority.rawLocalization residualAuthority)
            (Authority.canonicalMultiplierGreenPairing
              pseudoData firstVariationCovector
              (literalRawExtractor bondField plaquette))

    exactCancellation : Ownership.ExactCorrelatedCancellation
      (Authority.canonicalCorrelatedResidualFamily residualAuthority)

open JointExtractionCore public

record UniformLiteralJointProducer
    (Configuration : Set)
    (backgroundAt : Configuration → Physical.RationalSU2Background4)
    (bondFieldAt : Configuration → Coordinates.PhysicalSU2BondField4)
    (plaquette : Physical.Plaquette4) : Set₂ where
  field
    coreAt : ∀ configuration →
      JointExtractionCore
        (backgroundAt configuration) (bondFieldAt configuration) plaquette

    uniform : Uniform.UniformSelectedRegionPairEnclosure Configuration

    familyAtIsLiteral : ∀ configuration →
      Uniform.familyAt uniform configuration
      ≡ Authority.canonicalCorrelatedResidualFamily
          (residualAuthority (coreAt configuration))

    chargeAtIsLiteral : ∀ configuration →
      Uniform.chargeAt uniform configuration
      ≡ Wilson.plaquetteCrossCharge (bondFieldAt configuration) plaquette

open UniformLiteralJointProducer public

selectedLiteralJointResidualUpper :
  ∀ {Configuration backgroundAt bondFieldAt plaquette}
    (dataSet : UniformLiteralJointProducer
      Configuration backgroundAt bondFieldAt plaquette) →
  let selected = Uniform.selectedMinimizer (uniform dataSet)
      core = coreAt dataSet selected
  in
  Joint.jointResidual
      (Authority.canonicalCorrelatedResidualFamily (residualAuthority core))
  ≤ Selector.remainingSingletonCoefficient
      * Wilson.plaquetteCrossCharge (bondFieldAt selected) plaquette
selectedLiteralJointResidualUpper dataSet =
  let
    selected = Uniform.selectedMinimizer (uniform dataSet)
    core = coreAt dataSet selected
    sourceUpper =
      Uniform.selectedMinimizerResidualClosesFromUniformRegion (uniform dataSet)

    physicalUpper :
      Ownership.correlatedResidualTotal
        (Authority.canonicalCorrelatedResidualFamily (residualAuthority core))
      ≤ Selector.remainingSingletonCoefficient
          * Wilson.plaquetteCrossCharge (bondFieldAt selected) _
    physicalUpper =
      subst
        (λ charge →
          Ownership.correlatedResidualTotal
            (Authority.canonicalCorrelatedResidualFamily (residualAuthority core))
          ≤ Selector.remainingSingletonCoefficient * charge)
        (chargeAtIsLiteral dataSet selected)
        (subst
          (λ family →
            Ownership.correlatedResidualTotal family
            ≤ Selector.remainingSingletonCoefficient
                * Uniform.chargeAt (uniform dataSet) selected)
          (familyAtIsLiteral dataSet selected)
          sourceUpper)
  in
  subst
    (λ lower →
      lower ≤ Selector.remainingSingletonCoefficient
        * Wilson.plaquetteCrossCharge (bondFieldAt selected) _)
    (sym (Joint.jointResidualIsPhysicalTotal (exactCancellation core)))
    physicalUpper

selectedJointExtraction :
  ∀ {Configuration backgroundAt bondFieldAt plaquette}
    (dataSet : UniformLiteralJointProducer
      Configuration backgroundAt bondFieldAt plaquette) →
  let selected = Uniform.selectedMinimizer (uniform dataSet)
  in
  JointClosure.JointCorrelatedSingletonExtractionData
    (backgroundAt selected) (bondFieldAt selected) plaquette
selectedJointExtraction dataSet =
  let
    selected = Uniform.selectedMinimizer (uniform dataSet)
    core = coreAt dataSet selected
  in record
    { JointClosure.JointCorrelatedSingletonExtractionData.Multiplier = Multiplier core
    ; JointClosure.JointCorrelatedSingletonExtractionData.pseudoData = pseudoData core
    ; JointClosure.JointCorrelatedSingletonExtractionData.firstVariationCovector =
        firstVariationCovector core
    ; JointClosure.JointCorrelatedSingletonExtractionData.residualAuthority =
        residualAuthority core
    ; JointClosure.JointCorrelatedSingletonExtractionData.FineVariation = FineVariation core
    ; JointClosure.JointCorrelatedSingletonExtractionData.variation = variation core
    ; JointClosure.JointCorrelatedSingletonExtractionData.GaugeAdmissible = GaugeAdmissible core
    ; JointClosure.JointCorrelatedSingletonExtractionData.ConstraintTangent = ConstraintTangent core
    ; JointClosure.JointCorrelatedSingletonExtractionData.SupportedNearPlaquette =
        SupportedNearPlaquette core
    ; JointClosure.JointCorrelatedSingletonExtractionData.gaugeAdmissible = gaugeAdmissible core
    ; JointClosure.JointCorrelatedSingletonExtractionData.constraintTangent = constraintTangent core
    ; JointClosure.JointCorrelatedSingletonExtractionData.localSupport = localSupport core
    ; JointClosure.JointCorrelatedSingletonExtractionData.variationNormSq = variationNormSq core
    ; JointClosure.JointCorrelatedSingletonExtractionData.selectorConstant = selectorConstant core
    ; JointClosure.JointCorrelatedSingletonExtractionData.selectorConstantNonnegative =
        selectorConstantNonnegative core
    ; JointClosure.JointCorrelatedSingletonExtractionData.variationChargeBound =
        variationChargeBound core
    ; JointClosure.JointCorrelatedSingletonExtractionData.firstVariation = firstVariation core
    ; JointClosure.JointCorrelatedSingletonExtractionData.selectedEulerLagrangeStationary =
        selectedEulerLagrangeStationary core
    ; JointClosure.JointCorrelatedSingletonExtractionData.projectedVariationExact =
        projectedVariationExact core
    ; JointClosure.JointCorrelatedSingletonExtractionData.exactCancellation = exactCancellation core
    ; JointClosure.JointCorrelatedSingletonExtractionData.jointResidualUpper =
        selectedLiteralJointResidualUpper dataSet
    }

selectedSingletonWitnessFromUniformRegion :
  ∀ {Configuration backgroundAt bondFieldAt plaquette}
    (dataSet : UniformLiteralJointProducer
      Configuration backgroundAt bondFieldAt plaquette) →
  let selected = Uniform.selectedMinimizer (uniform dataSet)
  in
  Selector.SingletonExtractionWitness
    (backgroundAt selected) (bondFieldAt selected) plaquette
selectedSingletonWitnessFromUniformRegion dataSet =
  JointClosure.jointCorrelatedSingletonExtractionWitness
    (selectedJointExtraction dataSet)

p33UniformSelectedMinimizerJointProducerLevel : ProofLevel
p33UniformSelectedMinimizerJointProducerLevel = machineChecked
