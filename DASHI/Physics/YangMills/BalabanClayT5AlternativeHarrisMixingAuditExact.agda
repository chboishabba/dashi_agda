module DASHI.Physics.YangMills.BalabanClayT5AlternativeHarrisMixingAuditExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Alternative-strategy locator, not theorem authority.
--
-- Site/working-paper locator:
-- tsizek.github.io, "vacuum-has-steps" boundary-Langevin/Harris-mixing
-- programme. Author/title/DOI metadata were not verified from a primary
-- publication in the supplied material; no DOI is recorded here.
--
-- The mechanism is standard in form: a uniform Harris/Wasserstein contraction
-- for an induced boundary Markov process would imply exponential mixing, then
-- correlation decay, then the OS4 input used by the reconstructed transfer-gap
-- route. It replaces cluster-with-holes estimates by a different hard uniform
-- contraction theorem; it does not make the mass-gap problem easier by fiat.
------------------------------------------------------------------------

record AlternativeRouteAudit : Set where
  constructor alternativeRoute
  field
    authorsOrSite : String
    titleOrScope : String
    stableLocator : String
    doi : String
    admissibleAsAuthority : Bool
    usableAsMechanismPrompt : Bool
    replacesCurrentArchitecture : Bool
    exactUnprovedLoad : String

open AlternativeRouteAudit public

harrisBoundaryMixingAudit : AlternativeRouteAudit
harrisBoundaryMixingAudit = alternativeRoute
  "tsizek.github.io; author metadata pending primary verification"
  "Boundary Langevin dynamics and Harris-mixing route to clustering and gap"
  "tsizek.github.io/papers/vacuum-has-steps/paper.pdf"
  "no DOI verified"
  false
  true
  false
  "uniform volume/cutoff-independent contraction for the physical induced boundary process"

record HarrisBoundaryMixingRoute
    (BoundaryState Observable Bound Distance Gap : Set) : Set₁ where
  field
    transition : BoundaryState → BoundaryState
    distance : BoundaryState → BoundaryState → Distance
    covariance : Observable → Observable → Bound

    UniformContraction ExponentialMixing ExponentialClustering : Set
    PositiveTransferGap : Gap → Set

    uniformContraction : UniformContraction
    contractionImpliesMixing : UniformContraction → ExponentialMixing
    mixingImpliesClustering : ExponentialMixing → ExponentialClustering
    clusteringImpliesTransferGap : ExponentialClustering →
      (gap : Gap) → PositiveTransferGap gap

    candidateGap : Gap

open HarrisBoundaryMixingRoute public

harrisMixingProducesClustering :
  ∀ {BoundaryState Observable Bound Distance Gap} →
  (dataSet : HarrisBoundaryMixingRoute
    BoundaryState Observable Bound Distance Gap) →
  ExponentialClustering dataSet
harrisMixingProducesClustering dataSet =
  mixingImpliesClustering dataSet
    (contractionImpliesMixing dataSet (uniformContraction dataSet))

harrisMixingProducesTransferGap :
  ∀ {BoundaryState Observable Bound Distance Gap} →
  (dataSet : HarrisBoundaryMixingRoute
    BoundaryState Observable Bound Distance Gap) →
  PositiveTransferGap dataSet (candidateGap dataSet)
harrisMixingProducesTransferGap dataSet =
  clusteringImpliesTransferGap dataSet
    (harrisMixingProducesClustering dataSet)
    (candidateGap dataSet)

harrisAlternativeVocabularyLevel : ProofLevel
harrisAlternativeVocabularyLevel = machineChecked

harrisContractionToGapAssemblyLevel : ProofLevel
harrisContractionToGapAssemblyLevel = machineChecked

physicalBoundaryMarkovProcessIdentificationLevel : ProofLevel
physicalBoundaryMarkovProcessIdentificationLevel = conditional

physicalUniformHarrisContractionInputsLevel : ProofLevel
physicalUniformHarrisContractionInputsLevel = conditional

-- The route is explicitly not accepted as a completed mass-gap authority. Its
-- mathematical application remains an open/conjectural alternative.
harrisRouteAcceptedAsMassGapAuthority : ProofLevel
harrisRouteAcceptedAsMassGapAuthority = conjectural
