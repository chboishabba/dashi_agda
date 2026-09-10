{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayDirectGapConstructionSplitRound307Exact where

------------------------------------------------------------------------
-- ROUND307 / NON-CIRCULAR CLAY GATE SPLIT
--
-- The preferred R296/R304/R305/R306 route constructs a continuum physical
-- mass-gap certificate directly from arbitrary-pair continuum clustering and
-- standard OS spectral transfer.  M1/M2/M9 remain valid alternative producer
-- routes, but they are not mandatory terminal inputs for this direct route.
--
-- The full Clay construction still separately needs nontriviality, OS/QFT
-- construction semantics, UV compatibility, a genuine physical YM Hamiltonian,
-- and same-object identification of reconstructed evolution with that operator.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Interop.IntrospectiveProofLoopExact as Introspective
import DASHI.Physics.YangMills.BalabanClayMassGapGatePackageExact as Legacy
import DASHI.Physics.YangMills.BalabanClayCanonicalBFrontierRound306Exact as B306
import DASHI.Physics.YangMills.BalabanOSMassGapClosure as OSGap
import DASHI.Physics.YangMills.YMKatoClosedFormHamiltonianExact as Kato

record DirectClayConstructionGapGates
    (gates : Legacy.ClayMassGapGatePropositions)
    (DirectContinuumGap : Set) : Set₁ where
  field
    directContinuumGap : DirectContinuumGap
    m3LocalNoncollapse : Legacy.M3LocalNoncollapse gates
    m4OSPullbackOrIntertwining :
      Legacy._or_
        (Legacy.M4ExactOSPullback gates)
        (Legacy.M4TransferIntertwining gates)
    m6SpectralUVCompatibility : Legacy.M6SpectralUVCompatibility gates
    m7aPhysicalActionVariationHamiltonianSameObject :
      Legacy.M7aPhysicalActionVariationHamiltonianSameObject gates
    m7bHamiltonianDomainCommonInvariantDenseCore :
      Legacy.M7bHamiltonianDomainCommonInvariantDenseCore gates
    m7cSelfAdjointSelectedYMForm : Legacy.M7cSelfAdjointSelectedYMForm gates
    m8YMOSGeneratorEvolutionIdentification :
      Legacy.M8YMOSGeneratorEvolutionIdentification gates

open DirectClayConstructionGapGates public

DirectPhysicalMassGapCertificate : Set → Set → Set₁
DirectPhysicalMassGapCertificate = OSGap.PhysicalMassGapCertificate

data DirectClaySearchObject307 : Set where
  directContinuumGap : DirectClaySearchObject307
  localNoncollapse : DirectClaySearchObject307
  osConstructionMeaning : DirectClaySearchObject307
  spectralUVCompatibility : DirectClaySearchObject307
  physicalHamiltonianClosedForm : DirectClaySearchObject307
  physicalActionHamiltonianSameObject : DirectClaySearchObject307
  reconstructedEvolutionSameHamiltonian : DirectClaySearchObject307
  physicalScaleClusteringTransport : DirectClaySearchObject307
  denseCoreGapRoute : DirectClaySearchObject307
  vacuumRecoveryGapRoute : DirectClaySearchObject307

directRole307 : DirectClaySearchObject307 → Introspective.ProofSearchTargetRole
directRole307 directContinuumGap = Introspective.canonicalConsumerResidual
directRole307 localNoncollapse = Introspective.canonicalConsumerResidual
directRole307 osConstructionMeaning = Introspective.canonicalConsumerResidual
directRole307 spectralUVCompatibility = Introspective.canonicalConsumerResidual
directRole307 physicalHamiltonianClosedForm = Introspective.canonicalConsumerResidual
directRole307 physicalActionHamiltonianSameObject = Introspective.canonicalConsumerResidual
directRole307 reconstructedEvolutionSameHamiltonian = Introspective.canonicalConsumerResidual
directRole307 physicalScaleClusteringTransport = Introspective.optionalProducerTactic
directRole307 denseCoreGapRoute = Introspective.optionalProducerTactic
directRole307 vacuumRecoveryGapRoute = Introspective.optionalProducerTactic

record Round307Boundary : Set where
  constructor round307-boundary
  field
    m1MandatoryOnDirectContinuumGapRoute : Bool
    m1MandatoryOnDirectContinuumGapRouteIsFalse :
      m1MandatoryOnDirectContinuumGapRoute ≡ false
    m2MandatoryOnDirectContinuumGapRoute : Bool
    m2MandatoryOnDirectContinuumGapRouteIsFalse :
      m2MandatoryOnDirectContinuumGapRoute ≡ false
    m9MandatoryOnDirectContinuumGapRoute : Bool
    m9MandatoryOnDirectContinuumGapRouteIsFalse :
      m9MandatoryOnDirectContinuumGapRoute ≡ false
    directBMassGapProducerAvailableBelowItsThreePhysicalInputs : Bool
    directBMassGapProducerAvailableBelowItsThreePhysicalInputsIsTrue :
      directBMassGapProducerAvailableBelowItsThreePhysicalInputs ≡ true
    constructionAndHamiltonianIdentityStillIndependentOfGapProof : Bool
    constructionAndHamiltonianIdentityStillIndependentOfGapProofIsTrue :
      constructionAndHamiltonianIdentityStillIndependentOfGapProof ≡ true

canonicalRound307Boundary : Round307Boundary
canonicalRound307Boundary =
  round307-boundary false refl false refl false refl true refl true refl

round307DirectBGapAssemblyLevel : ProofLevel
round307DirectBGapAssemblyLevel = B306.round306MassGapAssemblyLevel

round307DirectBG1AbsoluteTwoJLevel : ProofLevel
round307DirectBG1AbsoluteTwoJLevel = B306.round306G1LiteralAbsoluteTwoJLocalizationLevel

round307DirectBG2TimeSupportMeaningLevel : ProofLevel
round307DirectBG2TimeSupportMeaningLevel = B306.round306G2PhysicalPairwiseTimeMeaningLevel

round307DirectBG3MassRateMeaningLevel : ProofLevel
round307DirectBG3MassRateMeaningLevel = B306.round306G3PhysicalMassRateNormalizationLevel

round307StandardClusteringToGapAuthorityLevel : ProofLevel
round307StandardClusteringToGapAuthorityLevel = B306.round306StandardClusteringToSpectrumLevel

round307KatoDomainSelfAdjointCompilerLevel : ProofLevel
round307KatoDomainSelfAdjointCompilerLevel = Kato.katoClosedFormHamiltonianCompilerLevel

round307LiteralPhysicalYMClosedFormLevel : ProofLevel
round307LiteralPhysicalYMClosedFormLevel = Kato.literalPhysicalYMClosedSemiboundedFormLevel

round307LiteralPhysicalYMCommonCoreLevel : ProofLevel
round307LiteralPhysicalYMCommonCoreLevel = Kato.literalPhysicalYMCommonInvariantOperatorCoreLevel

round307ConstructionHamiltonianClosureLevel : ProofLevel
round307ConstructionHamiltonianClosureLevel = conditional
