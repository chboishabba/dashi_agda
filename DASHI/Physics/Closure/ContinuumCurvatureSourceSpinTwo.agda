module DASHI.Physics.Closure.ContinuumCurvatureSourceSpinTwo where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Unified.GRQuantumProofTerms as Legacy
import DASHI.Geometry.GeneralLeviCivitaTheoremBoundary as LeviCivita
import DASHI.Geometry.DifferentialBianchiTheoremBoundary as Bianchi
import DASHI.Physics.Closure.ContinuumEinsteinMatterSolutionBoundary as EinsteinMatter

------------------------------------------------------------------------
-- Discrete-to-continuum Riemann/Ricci convergence.

record DiscreteCurvatureApproximation : Set₁ where
  field
    Resolution : Set
    DiscreteMetric : Resolution → Set
    DiscreteConnection : Resolution → Set
    DiscreteRiemann : Resolution → Set
    DiscreteRicci : Resolution → Set
    DiscreteScalarCurvature : Resolution → Set
    DiscreteEinsteinTensor : Resolution → Set

    ContinuumMetric : Set
    ContinuumConnection : Set
    ContinuumRiemann : Set
    ContinuumRicci : Set
    ContinuumScalarCurvature : Set
    ContinuumEinsteinTensor : Set

    discreteLeviCivita :
      (resolution : Resolution) →
      DiscreteMetric resolution → DiscreteConnection resolution
    discreteRiemann :
      (resolution : Resolution) →
      DiscreteConnection resolution → DiscreteRiemann resolution
    discreteRicci :
      (resolution : Resolution) →
      DiscreteRiemann resolution → DiscreteRicci resolution

    embedMetric :
      (resolution : Resolution) →
      DiscreteMetric resolution → ContinuumMetric
    embedConnection :
      (resolution : Resolution) →
      DiscreteConnection resolution → ContinuumConnection
    embedRiemann :
      (resolution : Resolution) →
      DiscreteRiemann resolution → ContinuumRiemann
    embedRicci :
      (resolution : Resolution) →
      DiscreteRicci resolution → ContinuumRicci

    ConsistencyError : Set
    StabilityBound : Set
    CompactnessWitness : Set
    ConvergenceMode : Set

    meshOrRefinementTendsToZero : Set
    meshOrRefinementTendsToZeroProof : meshOrRefinementTendsToZero
    metricConverges : Set
    metricConvergesProof : metricConverges
    discreteConnectionsConvergeToLeviCivita : Set
    discreteConnectionsConvergeToLeviCivitaProof :
      discreteConnectionsConvergeToLeviCivita
    riemannConverges : Set
    riemannConvergesProof : riemannConverges
    ricciConverges : Set
    ricciConvergesProof : ricciConverges
    scalarCurvatureConverges : Set
    scalarCurvatureConvergesProof : scalarCurvatureConverges
    einsteinTensorConverges : Set
    einsteinTensorConvergesProof : einsteinTensorConverges
    contractionsCommuteWithLimit : Set
    contractionsCommuteWithLimitProof : contractionsCommuteWithLimit
open DiscreteCurvatureApproximation public

record ContinuumCurvatureConvergenceAuthority : Set₁ where
  field
    approximation : DiscreteCurvatureApproximation
    smoothGeometry : LeviCivita.SmoothMetricGeometry
    leviCivitaReceipt :
      LeviCivita.GeneralLeviCivitaReceipt smoothGeometry

    coordinateOrGaugeControl : Set
    coordinateOrGaugeControlProof : coordinateOrGaugeControl
    convergenceIndependentOfRepresentative : Set
    convergenceIndependentOfRepresentativeProof :
      convergenceIndependentOfRepresentative

    legacySurface : Legacy.EinsteinTensorProof
    legacyClosed : Legacy.EinsteinTensorClosed legacySurface
    legacyCurvatureOperationsAgree : Set
    legacyCurvatureOperationsAgreeProof : legacyCurvatureOperationsAgree
open ContinuumCurvatureConvergenceAuthority public

------------------------------------------------------------------------
-- General Bianchi/Noether conservation with a genuinely nonzero source.

data ⊥ : Set where

_≢_ : {A : Set} → A → A → Set
left ≢ right = left ≡ right → ⊥

record NonzeroStressWitness
  (system : EinsteinMatter.ContinuumEinsteinMatterSystem)
  (solution : EinsteinMatter.ContinuumSolutionData system) : Set where
  field
    point : EinsteinMatter.Point system
    leftIndex rightIndex : EinsteinMatter.Index system
    stressIsNonzero :
      EinsteinMatter.StressTensor system
        (EinsteinMatter.matter solution)
        (EinsteinMatter.metric solution)
        point leftIndex rightIndex
      ≢ EinsteinMatter.zero system
open NonzeroStressWitness public

record BianchiNoetherNonzeroSourceAuthority : Set₁ where
  field
    curvatureCalculus : Bianchi.CurvatureCalculus
    differentialBianchi : Bianchi.DifferentialBianchiReceipt curvatureCalculus

    system : EinsteinMatter.ContinuumEinsteinMatterSystem
    solution : EinsteinMatter.ContinuumSolutionData system
    nonzeroSource : NonzeroStressWitness system solution

    MatterAction : Set
    DiffeomorphismVariation : Set
    EulerLagrangeEquation : Set
    noetherIdentity : Set
    noetherIdentityProof : noetherIdentity
    stressTensorComesFromMatterVariation : Set
    stressTensorComesFromMatterVariationProof :
      stressTensorComesFromMatterVariation
    bianchiCalculusMatchesEinsteinSystem : Set
    bianchiCalculusMatchesEinsteinSystemProof :
      bianchiCalculusMatchesEinsteinSystem
    noExternalConservationPostulate : Set
    noExternalConservationPostulateProof : noExternalConservationPostulate
open BianchiNoetherNonzeroSourceAuthority public

nonzeroSourceIsCovariantlyConserved :
  (authority : BianchiNoetherNonzeroSourceAuthority) →
  (p : EinsteinMatter.Point (system authority)) →
  (b : EinsteinMatter.Index (system authority)) →
  EinsteinMatter.DivergenceStress
    (system authority)
    (EinsteinMatter.matter (solution authority))
    (EinsteinMatter.metric (solution authority))
    p b
  ≡ EinsteinMatter.zero (system authority)
nonzeroSourceIsCovariantlyConserved authority =
  EinsteinMatter.matterConservationFromEinsteinAndBianchi
    (system authority)
    (solution authority)

------------------------------------------------------------------------
-- Massless spin-two nonlinear bootstrap.

record MasslessSpinTwoBootstrapAuthority : Set₁ where
  field
    Background : Set
    LinearSpinTwoField : Set
    GaugeParameter : Set
    ConservedSource : Set
    CouplingConstant : Set

    freeAction : Background → LinearSpinTwoField → Set
    linearGaugeTransform :
      GaugeParameter → LinearSpinTwoField → LinearSpinTwoField
    sourceCoupling :
      ConservedSource → LinearSpinTwoField → Set

    PerturbativeOrder : Set
    InteractionVertex : PerturbativeOrder → Set
    CorrectedGaugeTransform : PerturbativeOrder → Set
    CorrectedFieldEquation : PerturbativeOrder → Set

    freeTheoryIsFierzPauliOrEquivalent : Set
    freeTheoryIsFierzPauliOrEquivalentProof :
      freeTheoryIsFierzPauliOrEquivalent
    masslessHelicityTwoAndNoGhost : Set
    masslessHelicityTwoAndNoGhostProof : masslessHelicityTwoAndNoGhost
    universalCouplingToTotalStressEnergy : Set
    universalCouplingToTotalStressEnergyProof :
      universalCouplingToTotalStressEnergy
    selfStressFeedsNextOrder : Set
    selfStressFeedsNextOrderProof : selfStressFeedsNextOrder
    gaugeInvarianceRestoredAtEveryOrder :
      (order : PerturbativeOrder) → Set
    gaugeInvarianceRestoredAtEveryOrderProof :
      (order : PerturbativeOrder) →
      gaugeInvarianceRestoredAtEveryOrder order
    bootstrapSequenceConvergesOrResums : Set
    bootstrapSequenceConvergesOrResumsProof :
      bootstrapSequenceConvergesOrResums
    resummedEquationIsEinstein : Set
    resummedEquationIsEinsteinProof : resummedEquationIsEinstein
    uniquenessModuloFieldRedefinitionAndBoundaryTerms : Set
    uniquenessModuloFieldRedefinitionAndBoundaryTermsProof :
      uniquenessModuloFieldRedefinitionAndBoundaryTerms
    backgroundIndependenceRecovered : Set
    backgroundIndependenceRecoveredProof : backgroundIndependenceRecovered

    legacyEinsteinSurface : Legacy.EinsteinTensorProof
    legacyEinsteinClosed : Legacy.EinsteinTensorClosed legacyEinsteinSurface
    bootstrapAgreesWithLegacySpinTwoField : Set
    bootstrapAgreesWithLegacySpinTwoFieldProof :
      bootstrapAgreesWithLegacySpinTwoField
open MasslessSpinTwoBootstrapAuthority public
