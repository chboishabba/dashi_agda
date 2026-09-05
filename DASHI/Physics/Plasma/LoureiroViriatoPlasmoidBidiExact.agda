module DASHI.Physics.Plasma.LoureiroViriatoPlasmoidBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Core.ScientificWorkAttributionExact as Attribution
import DASHI.Physics.Plasma.IdealMHDReconnectionBidiExact as Reconnection

------------------------------------------------------------------------
-- LOUREIRO SCIENTIFIC-WORK BIDI OWNER
--
-- Source 1:
-- N. F. Loureiro, W. Dorland, L. Fazendeiro, A. Kanekar, A. Mallet,
-- M. S. Vilelas, A. Zocco,
-- "Viriato: A Fourier-Hermite spectral code for strongly magnetised
-- fluid-kinetic plasma dynamics", Computer Physics Communications 206
-- (2016) 45-63. DOI: 10.1016/j.cpc.2016.05.004; arXiv:1505.02649.
--
-- Source 2:
-- N. F. Loureiro, A. A. Schekochihin, S. C. Cowley,
-- "Instability of current sheets and formation of plasmoid chains",
-- Physics of Plasmas 14, 100703 (2007). DOI: 10.1063/1.2783986;
-- arXiv:astro-ph/0703631.
--
-- This owner encodes source-shaped scientific content, not an ideological
-- claim about openness and not a claim that DASHI has rederived the papers.
------------------------------------------------------------------------

data ViriatoEquationFamily : Set where
  KREHM
  KRMHD
  reducedMHDLimit
  : ViriatoEquationFamily

data ViriatoDirection : Set where
  parallelToGuideField
  perpendicularToGuideField
  parallelVelocitySpace
  : ViriatoDirection

data ViriatoNumericalMethod : Set where
  StrangSplitting
  GodunovSplitting
  MacCormackSecondOrder
  TVDRK3
  upwindSeventhOrder
  perpendicularPseudoSpectral
  iterativePredictorCorrector
  HermiteVelocityRepresentation
  : ViriatoNumericalMethod

data ViriatoBenchmark : Set where
  linearBenchmarks
  nonlinearBenchmarks
  OrszagTang2D
  OrszagTang3D
  fluidRegime
  kineticRegime
  : ViriatoBenchmark

record ViriatoScientificKernel : Set where
  constructor viriato-scientific-kernel
  field
    firstEquationFamily : ViriatoEquationFamily
    secondEquationFamily : ViriatoEquationFamily
    KREHMReducesToRMHDInAppropriateLimit : Bool
    KREHMReducesToRMHDInAppropriateLimitIsTrue :
      KREHMReducesToRMHDInAppropriateLimit ≡ true

    parallelPerpendicularOperatorSplit : Bool
    parallelPerpendicularOperatorSplitIsTrue :
      parallelPerpendicularOperatorSplit ≡ true

    velocitySpaceUsesHermiteRepresentation : Bool
    velocitySpaceUsesHermiteRepresentationIsTrue :
      velocitySpaceUsesHermiteRepresentation ≡ true

    benchmarkedInFluidAndKineticRegimes : Bool
    benchmarkedInFluidAndKineticRegimesIsTrue :
      benchmarkedInFluidAndKineticRegimes ≡ true

    sourceReference : String

open ViriatoScientificKernel public

canonicalViriatoScientificKernel : ViriatoScientificKernel
canonicalViriatoScientificKernel =
  viriato-scientific-kernel
    KREHM
    KRMHD
    true refl
    true refl
    true refl
    true refl
    "Loureiro et al., CPC 206 (2016) 45-63, DOI 10.1016/j.cpc.2016.05.004, arXiv:1505.02649"

------------------------------------------------------------------------
-- The Hermite chart is not merely a numerical label.  The paper states that
-- the Hermite expansion converts the drift-kinetic equation into an infinite
-- coupled hierarchy of fluid-like moment equations and is formally equivalent
-- before numerical truncation.  The truncation/closure is a separate step.
------------------------------------------------------------------------

data HermiteRepresentationState : Set where
  kineticDistributionRepresentation
  infiniteHermiteMomentHierarchy
  finiteTruncatedHierarchy
  closedFiniteHierarchy
  : HermiteRepresentationState

record HermiteBidiBoundary : Set where
  constructor hermite-bidi-boundary
  field
    expansionBeforeTruncationIsInformationLosingByDefinition : Bool
    expansionBeforeTruncationIsInformationLosingByDefinitionIsFalse :
      expansionBeforeTruncationIsInformationLosingByDefinition ≡ false

    finiteNumericalHierarchyRequiresTruncationOrClosure : Bool
    finiteNumericalHierarchyRequiresTruncationOrClosureIsTrue :
      finiteNumericalHierarchyRequiresTruncationOrClosure ≡ true

    finiteTruncationIsAutomaticallyExactAtAnyMomentCount : Bool
    finiteTruncationIsAutomaticallyExactAtAnyMomentCountIsFalse :
      finiteTruncationIsAutomaticallyExactAtAnyMomentCount ≡ false

canonicalHermiteBidiBoundary : HermiteBidiBoundary
canonicalHermiteBidiBoundary =
  hermite-bidi-boundary false refl true refl false refl

------------------------------------------------------------------------
-- Free-energy bookkeeping from the Viriato/KREHM presentation.
-- The paper decomposes the collisionless quadratic invariant into a fluid
-- electromagnetic contribution W_fluid and an electron free-energy H_e.
-- We type the decomposition without pretending this file rederives the
-- continuous integrals appearing in the paper.
------------------------------------------------------------------------

data FreeEnergyCoordinate : Set where
  totalFreeEnergy
  fluidElectromagneticFreeEnergy
  electronDistributionFreeEnergy
  : FreeEnergyCoordinate

record FreeEnergyDecompositionReceipt : Set where
  constructor free-energy-decomposition-receipt
  field
    total : FreeEnergyCoordinate
    fluidPart : FreeEnergyCoordinate
    electronPart : FreeEnergyCoordinate
    collisionlessQuadraticInvariant : Bool
    collisionlessQuadraticInvariantIsTrue :
      collisionlessQuadraticInvariant ≡ true
    sourceEquationReading : String

canonicalViriatoFreeEnergyReceipt : FreeEnergyDecompositionReceipt
canonicalViriatoFreeEnergyReceipt =
  free-energy-decomposition-receipt
    totalFreeEnergy
    fluidElectromagneticFreeEnergy
    electronDistributionFreeEnergy
    true refl
    "Viriato Sec. Energy: W = W_fluid + H_e; H_e is electron free energy of reduced distribution g_e"

------------------------------------------------------------------------
-- 2007 plasmoid-instability scaling law.
--
-- Source statement:
--   gamma_max ~ S^(1/4) v_A / L
--   N_plasmoid ~ S^(3/8)
-- where S is the Lundquist number.
--
-- The exponents are exact source coordinates.  The proportionality itself is
-- an asymptotic scaling claim from the source, not a definitional equality.
------------------------------------------------------------------------

record RationalExponent : Set where
  constructor rational-exponent
  field
    numerator : Nat
    denominator : Nat

open RationalExponent public

oneQuarter : RationalExponent
oneQuarter = rational-exponent 1 4

threeEighths : RationalExponent
threeEighths = rational-exponent 3 8

data PlasmoidObservable : Set where
  fastestGrowthRate
  plasmoidChainNumber
  : PlasmoidObservable

record PlasmoidScalingClaim : Set where
  constructor plasmoid-scaling-claim
  field
    observable : PlasmoidObservable
    lundquistExponent : RationalExponent
    dimensionalPrefactor : String
    asymptoticScalingNotIdentity : Bool
    asymptoticScalingNotIdentityIsTrue : asymptoticScalingNotIdentity ≡ true
    sourceReference : String

open PlasmoidScalingClaim public

plasmoidGrowthScaling : PlasmoidScalingClaim
plasmoidGrowthScaling =
  plasmoid-scaling-claim
    fastestGrowthRate
    oneQuarter
    "v_A / L"
    true refl
    "Loureiro-Schekochihin-Cowley 2007: gamma_max scales as S^(1/4) v_A/L"

plasmoidNumberScaling : PlasmoidScalingClaim
plasmoidNumberScaling =
  plasmoid-scaling-claim
    plasmoidChainNumber
    threeEighths
    "dimensionless chain count scaling"
    true refl
    "Loureiro-Schekochihin-Cowley 2007: plasmoid number scales as S^(3/8)"

------------------------------------------------------------------------
-- BIDI proof-search direction.
-- Forward: a source-backed model/scaling receipt may populate the appropriate
-- scientific fibre.
-- Reverse: observing a plasmoid chain or a benchmark match does not by itself
-- identify the unique reduced model, closure, numerical method or microphysics.
------------------------------------------------------------------------

data LoureiroReverseTarget : Set where
  acquireEquationFamily
  acquireHermiteClosure
  acquireParallelNumerics
  acquirePerpendicularNumerics
  acquireFreeEnergyInvariant
  acquireLundquistDefinition
  acquireGrowthScaling
  acquireNumberScaling
  acquireNonIdealReconnectionProducer
  acquireBenchmarkConfiguration
  : LoureiroReverseTarget

record LoureiroReverseObligation : Set where
  constructor loureiro-reverse-obligation
  field
    target : LoureiroReverseTarget
    requiredReceipt : String
    promotes : String
    cannotPromote : String

open LoureiroReverseObligation public

record LoureiroBidiBoundary : Set where
  constructor loureiro-bidi-boundary
  field
    benchmarkAgreementUniquelyIdentifiesNumericalMethod : Bool
    benchmarkAgreementUniquelyIdentifiesNumericalMethodIsFalse :
      benchmarkAgreementUniquelyIdentifiesNumericalMethod ≡ false

    plasmoidObservationUniquelyIdentifiesMicrophysics : Bool
    plasmoidObservationUniquelyIdentifiesMicrophysicsIsFalse :
      plasmoidObservationUniquelyIdentifiesMicrophysics ≡ false

    plasmoidScalingIsUniversalExactEqualityForAllS : Bool
    plasmoidScalingIsUniversalExactEqualityForAllSIsFalse :
      plasmoidScalingIsUniversalExactEqualityForAllS ≡ false

    reducedModelIsFullSixDimensionalKineticPlasma : Bool
    reducedModelIsFullSixDimensionalKineticPlasmaIsFalse :
      reducedModelIsFullSixDimensionalKineticPlasma ≡ false

canonicalLoureiroBidiBoundary : LoureiroBidiBoundary
canonicalLoureiroBidiBoundary =
  loureiro-bidi-boundary false refl false refl false refl false refl

------------------------------------------------------------------------
-- Cross-pollination into the existing DASHI reconnection fibre.
-- The bridge is deliberately narrow: Loureiro's plasmoid work concerns a
-- reconnection instability and therefore consumes the repo's non-ideal
-- reconnection semantics.  It does not collapse plasmoid scaling into the
-- generic definition of reconnection.
------------------------------------------------------------------------

record LoureiroReconnectionCrossPollination : Set₁ where
  constructor loureiro-reconnection-cross-pollination
  field
    regime : Reconnection.PlasmaEvolutionRegime
    scaling : PlasmoidScalingClaim
    nonIdealProducerStillRequired : Bool
    nonIdealProducerStillRequiredIsTrue : nonIdealProducerStillRequired ≡ true
    sourceToRepoBridgeReference : String

open LoureiroReconnectionCrossPollination public

resistivePlasmoidBridge : LoureiroReconnectionCrossPollination
resistivePlasmoidBridge =
  loureiro-reconnection-cross-pollination
    Reconnection.resistiveMHD
    plasmoidGrowthScaling
    true refl
    "2007 high-Lundquist current-sheet instability -> DASHI IdealMHDReconnectionBidiExact non-ideal/reconnection fibre"

------------------------------------------------------------------------
-- Exact person/work attribution, preserving coauthorship.
------------------------------------------------------------------------

loureiroViriatoAttribution : Attribution.ScientificWorkAttribution
loureiroViriatoAttribution =
  Attribution.scientific-work-attribution
    "Nuno F. Loureiro"
    "Viriato: A Fourier-Hermite spectral code for strongly magnetised fluid-kinetic plasma dynamics"
    "MIT PSFC / multi-institution collaboration"
    Attribution.namedAuthor
    Attribution.primaryPublicationRecord
    "DOI 10.1016/j.cpc.2016.05.004; arXiv:1505.02649"
    "Named coauthor; source supports attribution to the paper, not sole invention of every constituent model or algorithm"
    Attribution.externalSourceOwner

loureiroPlasmoidAttribution : Attribution.ScientificWorkAttribution
loureiroPlasmoidAttribution =
  Attribution.scientific-work-attribution
    "Nuno F. Loureiro"
    "Instability of current sheets and formation of plasmoid chains"
    "Princeton / Imperial / UCLA collaboration"
    Attribution.namedAuthor
    Attribution.primaryPublicationRecord
    "Phys. Plasmas 14, 100703 (2007), DOI 10.1063/1.2783986, arXiv:astro-ph/0703631"
    "Named coauthor with A. A. Schekochihin and S. C. Cowley"
    Attribution.externalSourceOwner
