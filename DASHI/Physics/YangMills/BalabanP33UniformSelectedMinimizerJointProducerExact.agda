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
-- Remove the last semantic gap between the uniform-region interval route and
-- the literal selected correlated-singleton object.  The interval family is
-- required to be definitionally the canonical correlated residual family of
-- the SAME extraction at each configuration.  Therefore the selected
-- minimizer's pair certificate gives the exact joint-residual bound consumed
-- by `JointCorrelatedSingletonExtractionData`; no decimal approximation to
-- A_* and no second residual family are introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ)
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Coordinates
import DASHI.Physics.YangMills.BalabanP33PhysicalWilsonSignedGlobalExact as Wilson
import DASHI.Physics.YangMills.BalabanSelectedCorrelatedResidualAuthorityExact as Authority
import DASHI.Physics.YangMills.BalabanSelectedCorrelatedResidualOwnershipExact as Ownership
import DASHI.Physics.YangMills.BalabanP33CertifiedPlaquettePairEnvelopeExact as PairEnvelope
import DASHI.Physics.YangMills.BalabanP33UniformSelectedMinimizerPairEnclosureExact as Uniform
import DASHI.Physics.YangMills.BalabanSelectedCorrelatedJointSingletonClosureExact as JointClosure
import DASHI.Physics.YangMills.BalabanP33JointCorrelatedResidualExact as Joint

record UniformLiteralJointProducer
    (Configuration : Set)
    (backgroundAt : Configuration → Physical.RationalSU2Background4)
    (bondFieldAt : Configuration → Coordinates.PhysicalSU2BondField4)
    (plaquette : Physical.Plaquette4) : Set₂ where
  field
    extractionAt : ∀ configuration →
      JointClosure.JointCorrelatedSingletonExtractionData
        (backgroundAt configuration) (bondFieldAt configuration) plaquette

    uniform : Uniform.UniformSelectedRegionPairEnclosure Configuration

    selectedBackgroundExact :
      backgroundAt (Uniform.selectedMinimizer uniform)
      ≡ backgroundAt (Uniform.selectedMinimizer uniform)

    familyAtIsLiteral : ∀ configuration →
      Uniform.familyAt uniform configuration
      ≡ Authority.canonicalCorrelatedResidualFamily
          (JointClosure.residualAuthority (extractionAt configuration))

    chargeAtIsLiteral : ∀ configuration →
      Uniform.chargeAt uniform configuration
      ≡ Wilson.plaquetteCrossCharge (bondFieldAt configuration) plaquette

open UniformLiteralJointProducer public

selectedPairEnvelope :
  ∀ {Configuration backgroundAt bondFieldAt plaquette}
    (dataSet : UniformLiteralJointProducer
      Configuration backgroundAt bondFieldAt plaquette) →
  PairEnvelope.CertifiedCorrelatedPairEnvelope
    (Uniform.familyAt (uniform dataSet)
      (Uniform.selectedMinimizer (uniform dataSet)))
    (Uniform.chargeAt (uniform dataSet)
      (Uniform.selectedMinimizer (uniform dataSet)))
selectedPairEnvelope dataSet =
  Uniform.pairEnvelopeAt
    (uniform dataSet)
    (Uniform.selectedMinimizer (uniform dataSet))
    (Uniform.selectedMinimizerInRegion (uniform dataSet))

selectedResidualUpperOnUniformObjects :
  ∀ {Configuration backgroundAt bondFieldAt plaquette}
    (dataSet : UniformLiteralJointProducer
      Configuration backgroundAt bondFieldAt plaquette) →
  Ownership.correlatedResidualTotal
    (Uniform.familyAt (uniform dataSet)
      (Uniform.selectedMinimizer (uniform dataSet)))
  ℚ.≤
  DASHI.Physics.YangMills.BalabanSelectedBackgroundVariationSelectorExact.remainingSingletonCoefficient
    ℚ.*
  Uniform.chargeAt (uniform dataSet)
    (Uniform.selectedMinimizer (uniform dataSet))
selectedResidualUpperOnUniformObjects dataSet =
  Uniform.selectedMinimizerResidualClosesFromUniformRegion (uniform dataSet)

selectedLiteralJointResidualUpper :
  ∀ {Configuration backgroundAt bondFieldAt plaquette}
    (dataSet : UniformLiteralJointProducer
      Configuration backgroundAt bondFieldAt plaquette) →
  let selected = Uniform.selectedMinimizer (uniform dataSet)
      extraction = extractionAt dataSet selected
  in
  Joint.jointResidual
      (Authority.canonicalCorrelatedResidualFamily
        (JointClosure.residualAuthority extraction))
  ℚ.≤
  DASHI.Physics.YangMills.BalabanSelectedBackgroundVariationSelectorExact.remainingSingletonCoefficient
    ℚ.* Wilson.plaquetteCrossCharge (bondFieldAt selected) plaquette
selectedLiteralJointResidualUpper dataSet =
  let
    selected = Uniform.selectedMinimizer (uniform dataSet)
    extraction = extractionAt dataSet selected
    familyEq = familyAtIsLiteral dataSet selected
    chargeEq = chargeAtIsLiteral dataSet selected
    cancellation = JointClosure.exactCancellation extraction

    totalUpper = selectedResidualUpperOnUniformObjects dataSet

    jointIsTotal :
      Joint.jointResidual
        (Authority.canonicalCorrelatedResidualFamily
          (JointClosure.residualAuthority extraction))
      ≡ Ownership.correlatedResidualTotal
        (Authority.canonicalCorrelatedResidualFamily
          (JointClosure.residualAuthority extraction))
    jointIsTotal = Joint.jointResidualIsPhysicalTotal cancellation
  in
  subst
    (λ family →
      Joint.jointResidual
        (Authority.canonicalCorrelatedResidualFamily
          (JointClosure.residualAuthority extraction))
      ℚ.≤
      DASHI.Physics.YangMills.BalabanSelectedBackgroundVariationSelectorExact.remainingSingletonCoefficient
        ℚ.* Uniform.chargeAt (uniform dataSet) selected)
    familyEq
    (subst
      (λ left → left ℚ.≤
        DASHI.Physics.YangMills.BalabanSelectedBackgroundVariationSelectorExact.remainingSingletonCoefficient
          ℚ.* Uniform.chargeAt (uniform dataSet) selected)
      (Relation.Binary.PropositionalEquality.sym jointIsTotal)
      totalUpper)
  where
    open import Relation.Binary.PropositionalEquality

-- The interval computation now targets exactly the selected physical family.
-- This theorem is the semantic transport; the remaining numerical work is the
-- sound construction of `uniform` itself from the certified minimizer region.
p33UniformSelectedMinimizerJointTransportLevel : ProofLevel
p33UniformSelectedMinimizerJointTransportLevel = machineChecked
