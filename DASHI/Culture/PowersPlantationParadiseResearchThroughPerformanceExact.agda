module DASHI.Culture.PowersPlantationParadiseResearchThroughPerformanceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Core.RobustExperimentInferenceFrontierExact as Robust
import DASHI.Culture.ColonialTheatreSensoryAccessExact as Sensory

------------------------------------------------------------------------
-- RESEARCH-THROUGH-PERFORMANCE AS A DISCRIMINATOR / AFFORDANCE PROBE
--
-- Re-enactment or spatial reconstruction may reveal candidate sightline,
-- audibility, language, service-route or information-flow constraints.  It is
-- never promoted into proof that the reconstructed event actually occurred.
------------------------------------------------------------------------

data PerformanceProbeKind : Set where
  sightlineProbe : PerformanceProbeKind
  audibilityProbe : PerformanceProbeKind
  backstageRouteProbe : PerformanceProbeKind
  languageIntelligibilityProbe : PerformanceProbeKind
  seatingInteractionProbe : PerformanceProbeKind

data ProbeOutcomeClass : Set where
  candidateAffordance : ProbeOutcomeClass
  candidateObstruction : ProbeOutcomeClass
  unresolvedUnderAssumptions : ProbeOutcomeClass

record PerformanceProbe : Set where
  constructor performance-probe
  field
    probeKind : PerformanceProbeKind
    venueReference : String
    sourceGeometryReference : String
    assumptionsReference : String
    consumerQuestion : String
    resultClass : ProbeOutcomeClass
    heldOutHistoricalOccurrenceClaim : Bool
    heldOutHistoricalOccurrenceClaimIsFalse :
      heldOutHistoricalOccurrenceClaim ≡ false

open PerformanceProbe public

portAuPrinceSightlineProbe : PerformanceProbe
portAuPrinceSightlineProbe =
  performance-probe
    sightlineProbe
    "1782 Port-au-Prince theatre plan surface"
    "located reproduction ANOM FM F3 296 E 75; archive original still separately inspectable"
    "reconstruction must declare stage, box and observer placements rather than inventing missing geometry"
    "which audience positions could plausibly obtain direct visual access?"
    candidateAffordance
    false refl

mitigatedAudibilityProbe : PerformanceProbe
mitigatedAudibilityProbe =
  performance-probe
    audibilityProbe
    "Saint-Domingue playhouse / threshold or service-position reconstruction"
    "Prest/Sabee mitigated-spectatorship methodology plus sourced venue constraints"
    "acoustic parameters not present in historical evidence must remain explicit assumptions"
    "could a position lacking direct sight plausibly retain aural access?"
    candidateAffordance
    false refl

backstageInformationFlowProbe : PerformanceProbe
backstageInformationFlowProbe =
  performance-probe
    backstageRouteProbe
    "source-bounded playhouse/service-route model"
    "only sourced entrances, backstage/service positions and documented roles may be treated as historical coordinates"
    "movement timing and unsourced connectivity remain probe assumptions"
    "what information-flow channels become possible for workers not represented in the seated audience map?"
    unresolvedUnderAssumptions
    false refl

probeScore : PerformanceProbe → Nat
probeScore portAuPrinceSightlineProbe = 8
probeScore mitigatedAudibilityProbe = 9
probeScore backstageInformationFlowProbe = 8

data PreferredPerformanceProbe : PerformanceProbe → PerformanceProbe → Set where
  audibilityOverSightlineWhenTestingMitigatedAccess :
    PreferredPerformanceProbe mitigatedAudibilityProbe portAuPrinceSightlineProbe

powersPerformanceProbeDesign : Robust.ExperimentDesign PerformanceProbe Nat
powersPerformanceProbeDesign =
  Robust.experimentDesign
    probeScore
    PreferredPerformanceProbe
    ⊤

sensoryAccessDemand : Sensory.SensoryAccessCoordinateDemand
sensoryAccessDemand = Sensory.canonicalSensoryAccessCoordinateDemand

data ReconstructionCreatesHistoricalOccurrence : Set where

data ProbeAffordanceCreatesHistoricalFact : Set where

reconstructionDoesNotCreateHistoricalOccurrence :
  ReconstructionCreatesHistoricalOccurrence → ⊥
reconstructionDoesNotCreateHistoricalOccurrence ()

probeAffordanceDoesNotCreateHistoricalFact :
  ProbeAffordanceCreatesHistoricalFact → ⊥
probeAffordanceDoesNotCreateHistoricalFact ()

record PowersResearchThroughPerformanceBoundary : Set where
  constructor powers-research-through-performance-boundary
  field
    performanceMayGenerateDiscriminator : Bool
    performanceMayGenerateDiscriminatorIsTrue :
      performanceMayGenerateDiscriminator ≡ true
    reconstructionCreatesHistoricalOccurrence : Bool
    reconstructionCreatesHistoricalOccurrenceIsFalse :
      reconstructionCreatesHistoricalOccurrence ≡ false
    unsourcedGeometryMayBeSilentlyFilled : Bool
    unsourcedGeometryMayBeSilentlyFilledIsFalse :
      unsourcedGeometryMayBeSilentlyFilled ≡ false
    probeAssumptionsRemainExplicit : Bool
    probeAssumptionsRemainExplicitIsTrue :
      probeAssumptionsRemainExplicit ≡ true
    probeOutputRequiresArchiveFollowup : Bool
    probeOutputRequiresArchiveFollowupIsTrue :
      probeOutputRequiresArchiveFollowup ≡ true

canonicalPowersResearchThroughPerformanceBoundary :
  PowersResearchThroughPerformanceBoundary
canonicalPowersResearchThroughPerformanceBoundary =
  powers-research-through-performance-boundary
    true refl
    false refl
    false refl
    true refl
    true refl
