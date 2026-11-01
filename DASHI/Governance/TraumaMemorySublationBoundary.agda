module DASHI.Governance.TraumaMemorySublationBoundary where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Biology.BodyKeepsScoreResidualBridge as BodyMemory
import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Governance.RevolutionarySourceAtlas as Source
import DASHI.Governance.TransitionResidual as Transition
import DASHI.Reasoning.MultiObserverScienceQuotient as Observer

------------------------------------------------------------------------
-- Trauma / memory / sublation boundary.
--
-- Collective injury is carried as politically causal context without becoming
-- an unlimited warrant for war, policing, occupation, punishment or civilian
-- harm.  Historical framing, power asymmetry, grief, accountability and repair
-- remain separate axes.  Contemporary monuments and spectacles enter only as
-- candidate memory-infrastructure observations requiring external sources.
------------------------------------------------------------------------

data CollectiveTraumaContext : Set where
  unitedStatesPostNineElevenContext : CollectiveTraumaContext
  israelPalestineContext : CollectiveTraumaContext
  iranUnitedStatesContext : CollectiveTraumaContext
  sudanConflictContext : CollectiveTraumaContext
  namedCollectiveTraumaContext : String → CollectiveTraumaContext

data TraumaResponseMode : Set where
  coerciveRepetitionMode : TraumaResponseMode
  reparativeSublationMode : TraumaResponseMode

data SublationInvariant : Set where
  injuryRecognisedInvariant : SublationInvariant
  griefNotMonopolisedInvariant : SublationInvariant
  historicalDepthRetainedInvariant : SublationInvariant
  powerAsymmetryVisibleInvariant : SublationInvariant
  civilianNonSubstitutabilityInvariant : SublationInvariant
  accountabilityInvariant : SublationInvariant
  materialRepairInvariant : SublationInvariant
  ecologicalContinuanceInvariant : SublationInvariant
  reviewAndRecallInvariant : SublationInvariant

canonicalSublationInvariants : List SublationInvariant
canonicalSublationInvariants =
  injuryRecognisedInvariant
  ∷ griefNotMonopolisedInvariant
  ∷ historicalDepthRetainedInvariant
  ∷ powerAsymmetryVisibleInvariant
  ∷ civilianNonSubstitutabilityInvariant
  ∷ accountabilityInvariant
  ∷ materialRepairInvariant
  ∷ ecologicalContinuanceInvariant
  ∷ reviewAndRecallInvariant
  ∷ []

record HistoricalOriginFrame : Set where
  constructor historicalOriginFrame
  field
    frameContext : CollectiveTraumaContext
    selectedOriginLabel : String
    priorHistoryRetained : Bool
    selectedOriginIsCompleteCause : Bool
    frameCreatesHistoricalAuthority : Bool

open HistoricalOriginFrame public

mkHistoricalOriginFrame :
  CollectiveTraumaContext → String → HistoricalOriginFrame
mkHistoricalOriginFrame context label =
  historicalOriginFrame
    context
    label
    true
    false
    false

unitedStatesNineElevenFrame : HistoricalOriginFrame
unitedStatesNineElevenFrame =
  mkHistoricalOriginFrame
    unitedStatesPostNineElevenContext
    "11 September 2001; prior imperial, regional, racial and security history remains open"

iranNineteenFiftyThreeFrame : HistoricalOriginFrame
iranNineteenFiftyThreeFrame =
  mkHistoricalOriginFrame
    iranUnitedStatesContext
    "1953 coup and intervention frame"

iranNineteenSeventyNineFrame : HistoricalOriginFrame
iranNineteenSeventyNineFrame =
  mkHistoricalOriginFrame
    iranUnitedStatesContext
    "1979 revolution and hostage-crisis frame"

israelPalestinePluralOriginFrame : HistoricalOriginFrame
israelPalestinePluralOriginFrame =
  mkHistoricalOriginFrame
    israelPalestineContext
    "plural frames of antisemitic persecution, settler colonialism, displacement, occupation, war and resistance"

sudanAprilTwentyTwentyThreeFrame : HistoricalOriginFrame
sudanAprilTwentyTwentyThreeFrame =
  mkHistoricalOriginFrame
    sudanConflictContext
    "April 2023 armed conflict; prior colonial, authoritarian, regional and revolutionary history remains open"

record PriorInjuryAuthorityBoundary : Set where
  constructor priorInjuryAuthorityBoundary
  field
    recognitionClaimAvailable : Bool
    safetyClaimAvailable : Bool
    repairClaimAvailable : Bool
    restitutionClaimMayRequireSeparateEvidence : Bool
    priorInjuryAuthorisesUnlimitedControl : Bool
    priorInjuryAuthorisesCivilianHarm : Bool
    priorInjuryErasesOtherGrief : Bool
    traumaExplanationCreatesViolenceAuthority : Bool
    traumaParityImpliesPowerParity : Bool

open PriorInjuryAuthorityBoundary public

canonicalPriorInjuryAuthorityBoundary : PriorInjuryAuthorityBoundary
canonicalPriorInjuryAuthorityBoundary =
  priorInjuryAuthorityBoundary
    true
    true
    true
    true
    false
    false
    false
    false
    false

record TraumaPoliticsSurface : Set where
  constructor traumaPoliticsSurface
  field
    context : CollectiveTraumaContext
    historicalFrames : List HistoricalOriginFrame
    observedInjury : String
    publicNarrative : String
    responseMode : TraumaResponseMode
    memoryResidualRetained : Bool
    causalDepthRequired : Bool
    powerAnalysisRequired : Bool
    civilianProtectionRequired : Bool
    accountabilityRequired : Bool
    repairRequired : Bool
    coerciveActionEqualsTraumaIntegration : Bool
    enemyCarrierSuppressionResolvesConditions : Bool
    formalModelDiagnosesPopulation : Bool
    politicalAuthorityPromoted : Bool

open TraumaPoliticsSurface public

mkTraumaPoliticsSurface :
  CollectiveTraumaContext →
  List HistoricalOriginFrame →
  String →
  String →
  TraumaResponseMode →
  TraumaPoliticsSurface
mkTraumaPoliticsSurface context frames injury narrative mode =
  traumaPoliticsSurface
    context
    frames
    injury
    narrative
    mode
    true
    true
    true
    true
    true
    true
    false
    false
    false
    false

canonicalUnitedStatesPostNineElevenSurface : TraumaPoliticsSurface
canonicalUnitedStatesPostNineElevenSurface =
  mkTraumaPoliticsSurface
    unitedStatesPostNineElevenContext
    (unitedStatesNineElevenFrame ∷ [])
    "civilian death, fear and symbolic national injury"
    "candidate analysis of how trauma may be narrated into war-on-terror repetition"
    coerciveRepetitionMode

canonicalIsraelPalestineSurface : TraumaPoliticsSurface
canonicalIsraelPalestineSurface =
  mkTraumaPoliticsSurface
    israelPalestineContext
    (israelPalestinePluralOriginFrame ∷ [])
    "plural histories of persecution, dispossession, occupation, attack, war and civilian loss"
    "grief remains plural while material and military power asymmetry remains an independent axis"
    reparativeSublationMode

canonicalIranUnitedStatesSurface : TraumaPoliticsSurface
canonicalIranUnitedStatesSurface =
  mkTraumaPoliticsSurface
    iranUnitedStatesContext
    (iranNineteenFiftyThreeFrame ∷ iranNineteenSeventyNineFrame ∷ [])
    "recursive intervention, siege, retaliation and threat memory"
    "causal narrative changes with selected origin and therefore retains earlier frames"
    reparativeSublationMode

canonicalSudanTraumaSurface : TraumaPoliticsSurface
canonicalSudanTraumaSurface =
  mkTraumaPoliticsSurface
    sudanConflictContext
    (sudanAprilTwentyTwentyThreeFrame ∷ [])
    "repeated authoritarian, military, displacement and civilian trauma"
    "the RCEPP popular-power lane remains a situated reconstruction proposal, not a trauma-closure theorem"
    reparativeSublationMode

data MemoryInfrastructureKind : Set where
  reflectingPoolInfrastructure : MemoryInfrastructureKind
  executiveResidenceRenovationInfrastructure : MemoryInfrastructureKind
  nationalAnniversaryCombatSpectacleInfrastructure : MemoryInfrastructureKind
  namedMemoryInfrastructure : String → MemoryInfrastructureKind

record ContemporaryMemoryObservation : Set where
  constructor contemporaryMemoryObservation
  field
    infrastructure : MemoryInfrastructureKind
    observationLabel : String
    symbolicReadingCandidate : Bool
    externalSourceRequired : Bool
    motiveInferredAsFact : Bool
    legalViolationClaimed : Bool
    historicalMeaningClosed : Bool
    personalityDiagnosisClaimed : Bool
    politicalAuthorityPromoted : Bool

open ContemporaryMemoryObservation public

mkContemporaryMemoryObservation :
  MemoryInfrastructureKind → String → ContemporaryMemoryObservation
mkContemporaryMemoryObservation kind label =
  contemporaryMemoryObservation
    kind
    label
    true
    true
    false
    false
    false
    false
    false

reflectingPoolObservation : ContemporaryMemoryObservation
reflectingPoolObservation =
  mkContemporaryMemoryObservation
    reflectingPoolInfrastructure
    "reflecting-pool repair, leakage, accusation and national self-reflection are retained as a candidate symbolic reading"

whiteHouseRenovationObservation : ContemporaryMemoryObservation
whiteHouseRenovationObservation =
  mkContemporaryMemoryObservation
    executiveResidenceRenovationInfrastructure
    "executive-building renovation is inspected through stewardship versus possessive remaking without inferring motive or legality"

freedomTwoFiftyCombatSpectacleObservation : ContemporaryMemoryObservation
freedomTwoFiftyCombatSpectacleObservation =
  mkContemporaryMemoryObservation
    nationalAnniversaryCombatSpectacleInfrastructure
    "Freedom 250 / WWE / combat-sport imagery is inspected as candidate agonistic memory spectacle without closing historical meaning"

canonicalContemporaryMemoryObservations : List ContemporaryMemoryObservation
canonicalContemporaryMemoryObservations =
  reflectingPoolObservation
  ∷ whiteHouseRenovationObservation
  ∷ freedomTwoFiftyCombatSpectacleObservation
  ∷ []

record TraumaMemoryCrossPollination : Set where
  constructor traumaMemoryCrossPollination
  field
    bodyMemoryBoundary : BodyMemory.BodyKeepsScoreGovernance
    multiObserverBoundary : Observer.MultiObserverScienceBoundary
    transitionBoundary : Transition.TransitionAuthorityBoundary
    sources : List Source.SourceReference
    priorInjuryBoundary : PriorInjuryAuthorityBoundary
    collectiveSurfaces : List TraumaPoliticsSurface
    memoryInfrastructureObservations : List ContemporaryMemoryObservation
    individualBodyMemoryEqualsCollectiveHistory : Bool
    observerFusionRecoversCompleteHistory : Bool
    formalSublationGuaranteesReconciliation : Bool
    politicalAuthorityPromoted : Bool

open TraumaMemoryCrossPollination public

canonicalTraumaMemoryCrossPollination : TraumaMemoryCrossPollination
canonicalTraumaMemoryCrossPollination =
  traumaMemoryCrossPollination
    BodyMemory.canonicalBodyKeepsScoreGovernance
    Observer.canonicalMultiObserverScienceBoundary
    Transition.canonicalTransitionAuthorityBoundary
    (Source.dominickLaCapraWritingHistoryWritingTrauma
      ∷ Source.judithButlerFramesOfWar
      ∷ Source.nineElevenCommissionReport
      ∷ Source.frantzFanonWretchedEarth
      ∷ [])
    canonicalPriorInjuryAuthorityBoundary
    (canonicalUnitedStatesPostNineElevenSurface
      ∷ canonicalIsraelPalestineSurface
      ∷ canonicalIranUnitedStatesSurface
      ∷ canonicalSudanTraumaSurface
      ∷ [])
    canonicalContemporaryMemoryObservations
    false
    false
    false
    false

record TraumaMemorySublationBoundary : Set where
  constructor traumaMemorySublationBoundary
  field
    priorInjuryDoesNotAuthoriseUnlimitedControl :
      priorInjuryAuthorisesUnlimitedControl
        canonicalPriorInjuryAuthorityBoundary
        ≡ false
    priorInjuryDoesNotAuthoriseCivilianHarm :
      priorInjuryAuthorisesCivilianHarm
        canonicalPriorInjuryAuthorityBoundary
        ≡ false
    traumaParityDoesNotImplyPowerParity :
      traumaParityImpliesPowerParity
        canonicalPriorInjuryAuthorityBoundary
        ≡ false
    symbolicObservationDoesNotInferMotive :
      motiveInferredAsFact reflectingPoolObservation ≡ false
    formalSublationDoesNotGuaranteeReconciliation :
      formalSublationGuaranteesReconciliation
        canonicalTraumaMemoryCrossPollination
        ≡ false
    politicalAuthorityBlocked :
      politicalAuthorityPromoted canonicalTraumaMemoryCrossPollination
        ≡ false

open TraumaMemorySublationBoundary public

canonicalTraumaMemorySublationBoundary : TraumaMemorySublationBoundary
canonicalTraumaMemorySublationBoundary =
  traumaMemorySublationBoundary refl refl refl refl refl refl

canonicalTraumaMemorySublationReceipt : GenericReceipt.GenericReceipt
canonicalTraumaMemorySublationReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "trauma memory sublation boundary"
    "DASHI.Governance.TraumaMemorySublationBoundary"
    "canonicalTraumaMemoryCrossPollination"
    "connects body-memory residuals, multi-observer partiality, constitutional transition, selected-origin framing, plural grief, power asymmetry, memory infrastructure and reparative sublation invariants"
    "trauma does not authorise war or civilian harm, symbolic observations do not establish motive or legality, and formal sublation does not guarantee reconciliation"
    "agda -i . DASHI/Governance/TraumaMemorySublationBoundary.agda"
