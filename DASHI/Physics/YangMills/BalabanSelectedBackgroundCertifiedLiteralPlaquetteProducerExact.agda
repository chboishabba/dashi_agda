module DASHI.Physics.YangMills.BalabanSelectedBackgroundCertifiedLiteralPlaquetteProducerExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "The Variational Problem and Background Fields in Renormalization Group
-- Method for Lattice Gauge Theories",
-- Communications in Mathematical Physics 102 (1985), 277--309.
-- DOI: 10.1007/BF01229381.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- Ramon E. Moore, R. Baker Kearfott, Michael J. Cloud,
-- "Introduction to Interval Analysis", SIAM, 2009.
-- DOI: 10.1137/1.9780898717716.
--
-- DASHI CONTRIBUTION
--
-- Replace the four independently supplied owner inequalities in the literal
-- selected plaquette producer by one certified rational enclosure object.
-- Sound interval upper bounds are converted by the already-proved enclosure
-- theorem to the exact slack-preserving owner budget, then inserted into the
-- vertical LiteralSelectedPlaquetteWitness.  This is the intended concrete
-- producer route for the finite K_A^+ / Green-kernel calculation: computation
-- supplies rational enclosures, while Agda owns the conversion to the Wilson
-- singleton budget.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _*_; _≤_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Coordinates
import DASHI.Physics.YangMills.BalabanP33PhysicalWilsonLinearNonlinearPartitionExact as Partition
import DASHI.Physics.YangMills.BalabanP33PhysicalWilsonSignedGlobalExact as Wilson
import DASHI.Physics.YangMills.BalabanP33FiniteKKTAdmissibleProjectorExact as KKT
import DASHI.Physics.YangMills.BalabanP33FiniteKKTPseudoinverseProjectorExact as Pseudo
import DASHI.Physics.YangMills.BalabanSelectedVariationSignConventionExact as Sign
import DASHI.Physics.YangMills.BalabanSelectedCorrelatedResidualAuthorityExact as Authority
import DASHI.Physics.YangMills.BalabanSelectedCorrelatedResidualOwnershipExact as Ownership
import DASHI.Physics.YangMills.BalabanSelectedCorrelatedSingletonClosureExact as Closure
import DASHI.Physics.YangMills.BalabanSelectedCertifiedOwnerEnclosureExact as Certified
import DASHI.Physics.YangMills.BalabanSelectedSinglePlaquetteWitnessExact as Plaquette

record CertifiedLiteralPlaquetteData
    (background : Physical.RationalSU2Background4)
    (bondField : Coordinates.PhysicalSU2BondField4)
    (plaquette : Physical.Plaquette4) : Set₂ where
  field
    Multiplier : Set
    pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier
    firstVariationCovector : KKT.StateVector

    residualAuthority : Authority.CorrelatedResidualAuthority
      pseudoData firstVariationCovector
      (Closure.literalRawExtractor bondField plaquette)

    FineVariation : Set
    variation : FineVariation

    GaugeAdmissible : FineVariation → Set
    ConstraintTangent : FineVariation → Set
    SupportedNearPlaquette : FineVariation → Set

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
      ≡ Partition.physicalPlaquetteWilsonLinearPart
          background bondField plaquette
        + Sign.canonicalProjectedSpillover
            (Authority.rawLocalization residualAuthority)
            (Authority.canonicalMultiplierGreenPairing
              pseudoData firstVariationCovector
              (Closure.literalRawExtractor bondField plaquette))

    exactCancellation :
      Ownership.ExactCorrelatedCancellation
        (Authority.canonicalCorrelatedResidualFamily residualAuthority)

    certifiedOwnerEnclosures :
      Certified.CertifiedCorrelatedOwnerEnclosures
        (Authority.canonicalCorrelatedResidualFamily residualAuthority)
        (Wilson.plaquetteCrossCharge bondField plaquette)

open CertifiedLiteralPlaquetteData public

certifiedLiteralPlaquetteDataToWitness :
  ∀ {background bondField plaquette} →
  CertifiedLiteralPlaquetteData background bondField plaquette →
  Plaquette.LiteralSelectedPlaquetteWitness background bondField plaquette
certifiedLiteralPlaquetteDataToWitness data = record
  { Plaquette.LiteralSelectedPlaquetteWitness.Multiplier = Multiplier data
  ; Plaquette.LiteralSelectedPlaquetteWitness.pseudoData = pseudoData data
  ; Plaquette.LiteralSelectedPlaquetteWitness.firstVariationCovector =
      firstVariationCovector data
  ; Plaquette.LiteralSelectedPlaquetteWitness.residualAuthority =
      residualAuthority data
  ; Plaquette.LiteralSelectedPlaquetteWitness.FineVariation = FineVariation data
  ; Plaquette.LiteralSelectedPlaquetteWitness.variation = variation data
  ; Plaquette.LiteralSelectedPlaquetteWitness.GaugeAdmissible = GaugeAdmissible data
  ; Plaquette.LiteralSelectedPlaquetteWitness.ConstraintTangent = ConstraintTangent data
  ; Plaquette.LiteralSelectedPlaquetteWitness.SupportedNearPlaquette =
      SupportedNearPlaquette data
  ; Plaquette.LiteralSelectedPlaquetteWitness.gaugeAdmissible = gaugeAdmissible data
  ; Plaquette.LiteralSelectedPlaquetteWitness.constraintTangent = constraintTangent data
  ; Plaquette.LiteralSelectedPlaquetteWitness.localSupport = localSupport data
  ; Plaquette.LiteralSelectedPlaquetteWitness.variationNormSq = variationNormSq data
  ; Plaquette.LiteralSelectedPlaquetteWitness.selectorConstant = selectorConstant data
  ; Plaquette.LiteralSelectedPlaquetteWitness.selectorConstantNonnegative =
      selectorConstantNonnegative data
  ; Plaquette.LiteralSelectedPlaquetteWitness.variationChargeBound =
      variationChargeBound data
  ; Plaquette.LiteralSelectedPlaquetteWitness.firstVariation = firstVariation data
  ; Plaquette.LiteralSelectedPlaquetteWitness.selectedEulerLagrangeStationary =
      selectedEulerLagrangeStationary data
  ; Plaquette.LiteralSelectedPlaquetteWitness.projectedVariationExact =
      projectedVariationExact data
  ; Plaquette.LiteralSelectedPlaquetteWitness.exactCancellation =
      exactCancellation data
  ; Plaquette.LiteralSelectedPlaquetteWitness.ownerBounds =
      Certified.certifiedEnclosuresToOwnerBounds (certifiedOwnerEnclosures data) }

record CertifiedLiteralPlaquetteFamily
    (background : Physical.RationalSU2Background4)
    (bondField : Coordinates.PhysicalSU2BondField4) : Set₂ where
  field
    atPlaquette : ∀ plaquette →
      CertifiedLiteralPlaquetteData background bondField plaquette

open CertifiedLiteralPlaquetteFamily public

certifiedLiteralPlaquetteFamilyToLiteralFamily :
  ∀ {background bondField} →
  CertifiedLiteralPlaquetteFamily background bondField →
  Plaquette.LiteralSelectedPlaquetteFamily background bondField
certifiedLiteralPlaquetteFamilyToLiteralFamily family = record
  { Plaquette.LiteralSelectedPlaquetteFamily.atPlaquette =
      λ plaquette → certifiedLiteralPlaquetteDataToWitness
        (atPlaquette family plaquette) }

selectedCertifiedLiteralPlaquetteConstructorLevel : ProofLevel
selectedCertifiedLiteralPlaquetteConstructorLevel = machineChecked

selectedCertifiedLiteralPlaquetteFamilyConstructorLevel : ProofLevel
selectedCertifiedLiteralPlaquetteFamilyConstructorLevel = machineChecked
