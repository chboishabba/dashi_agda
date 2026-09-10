{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayDirectGapConstructionSplitRound307Exact where

------------------------------------------------------------------------
-- ROUND307 / NON-CIRCULAR CLAY GATE SPLIT
--
-- The historical mandatory gate package was organized around a route that
-- proved a finite/spatial clustering estimate, converted it to dense-core
-- spectral exclusion, and separately transported a finite gap through a vacuum
-- recovery system.  The preferred R296/R304/R305/R306 route instead constructs
-- a continuum physical mass-gap certificate directly from arbitrary-pair
-- continuum clustering and the standard OS spectral transfer.
--
-- Therefore the following are PRODUCER/ALTERNATIVE-ROUTE coordinates rather
-- than mandatory terminal inputs on this direct route:
--
--   M1 physical-scale lattice->continuum clustering transport,
--   M2 dense-core spectral-exclusion producer,
--   M9 finite->continuum vacuum-recovery gap transport.
--
-- They remain valid alternative proof routes.  They are not deleted.
--
-- The full Clay construction still needs the orthogonal construction/identity
-- content: local noncollapse, OS/reflection-positive reconstruction semantics,
-- UV compatibility of the constructed family, a genuine selected physical YM
-- Hamiltonian, and identification of reconstructed evolution with that same
-- Hamiltonian.  A direct gap certificate cannot manufacture those facts.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Interop.IntrospectiveProofLoopExact as Introspective
import DASHI.Physics.YangMills.BalabanClayMassGapGatePackageExact as Legacy
import DASHI.Physics.YangMills.BalabanClayCanonicalBFrontierRound306Exact as B306
import DASHI.Physics.YangMills.BalabanPairwiseClusteringStandardMassGapRound305Exact as B305
import DASHI.Physics.YangMills.BalabanOSMassGapClosure as OSGap
import DASHI.Physics.YangMills.YMKatoClosedFormHamiltonianExact as Kato

record DirectClayConstructionGapGates
    (gates : Legacy.ClayMassGapGatePropositions)
    (DirectContinuumGap : Set) : Set₁ where
  field
    directContinuumGap : DirectContinuumGap

    -- Nontriviality / construction identity remain genuine requirements.
    m3LocalNoncollapse : Legacy.M3LocalNoncollapse gates
    m4OSPullbackOrIntertwining :
      Legacy.M4ExactOSPullback gates Legacy.or Legacy.M4TransferIntertwining gates
    m6SpectralUVCompatibility : Legacy.M6SpectralUVCompatibility gates

    -- Preferred M7 route: Kato compiles domain+self-adjointness from the physical
    -- closed semibounded form, but the physical form and common core/same-object
    -- Hamiltonian semantics remain source obligations.
    m7aPhysicalActionVariationHamiltonianSameObject :
      Legacy.M7aPhysicalActionVariationHamiltonianSameObject gates
    m7bHamiltonianDomainCommonInvariantDenseCore :
      Legacy.M7bHamiltonianDomainCommonInvariantDenseCore gates
    m7cSelfAdjointSelectedYMForm : Legacy.M7cSelfAdjointSelectedYMForm gates

    -- This is the decisive same-Hamiltonian weld for the direct gap certificate.
    m8YMOSGeneratorEvolutionIdentification :
      Legacy.M8YMOSGeneratorEvolutionIdentification gates

open DirectClayConstructionGapGates public

-- A concrete direct-gap carrier can be the normalized OS physical certificate
-- produced by R305.  Keeping this alias separate avoids pretending the old
-- gate proposition family already knew the new proof route.
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
round307StandardClusteringToGapAuthorityLevel =
  B306.round306StandardClusteringToSpectrumLevel

-- Kato removes separate domain/self-adjoint theorem debt once the literal
-- physical closed semibounded form is supplied.  It does not remove the
-- common-core or action/evolution same-object obligations.
round307KatoDomainSelfAdjointCompilerLevel : ProofLevel
round307KatoDomainSelfAdjointCompilerLevel = Kato.katoClosedFormHamiltonianCompilerLevel

round307LiteralPhysicalYMClosedFormLevel : ProofLevel
round307LiteralPhysicalYMClosedFormLevel = Kato.literalPhysicalYMClosedSemiboundedFormLevel

round307LiteralPhysicalYMCommonCoreLevel : ProofLevel
round307LiteralPhysicalYMCommonCoreLevel = Kato.literalPhysicalYMCommonInvariantOperatorCoreLevel

round307ConstructionHamiltonianClosureLevel : ProofLevel
round307ConstructionHamiltonianClosureLevel = conditional
