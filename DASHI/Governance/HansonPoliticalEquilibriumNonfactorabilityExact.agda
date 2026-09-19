module DASHI.Governance.HansonPoliticalEquilibriumNonfactorabilityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Core.RelationalHistoryFabricExact as History
import DASHI.Core.AmplificationLineageBidiCrossPollination2026Exact as Amplification
import DASHI.Governance.HansonCapacityCriticismHyperformalismExact as Capacity
import DASHI.Governance.HansonOneNationPoliticalEcologyExact as Ecology

------------------------------------------------------------------------
-- HANSON POLITICAL EQUILIBRIUM / ENVIRONMENTAL NON-FACTORABILITY
--
-- DASHI-original theorem layer over the separately attributed political
-- ecology source registry.
--
-- External claim owners reused from HansonOneNationPoliticalEcologyExact:
--
-- * ABC / Antony Green and ABC Southern Queensland:
--     Groom/Toowoomba conservative electoral history.
-- * Tony Lynch / University of New England:
--     middle-class/status interpretation of One Nation support.
-- * ABC reporting of Kos Samaras:
--     outer-suburban, debt/economic-pressure and changing voter composition.
-- * Deutchman & Ellison, Media, Culture & Society 21(1), 1999,
--     DOI 10.1177/016344399021001002:
--     Hanson news coverage / political-celebrity analysis.
-- * Graeme Turner:
--     media-governmentality / Hanson-effect analysis.
-- * ABC Radio National / The Conversation (2026):
--     historical-to-platform media-ecology discussion.
-- * ABC News (2025):
--     Barnaby Joyce's move from the Nationals to One Nation.
-- * Pauline Hanson's One Nation:
--     current declared policy surfaces only, not outcome authority.
--
-- Those sources motivate and populate axes.  They do NOT state the generic
-- non-factorability theorems below.  DASHI owns:
--
--   same public-performance register
--   + different political environment/history
--   -> different political-reach consumer
--   -> reach does not factor through the public-performance register alone.
--
-- This is deliberately NOT:
--   * a psychological diagnosis of Pauline Hanson;
--   * a causal estimate of any media effect;
--   * a claim that one voter class or one region explains One Nation;
--   * an election prediction;
--   * a claim that controversy automatically increases support.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- SOURCE RECEIPTS ARE IMPORTED, NOT REATTRIBUTED.
------------------------------------------------------------------------

mediaSource1999 : Ecology.PoliticalEcologySource
mediaSource1999 = Ecology.deutchmanEllison1999

mediaSourceTurner : Ecology.PoliticalEcologySource
mediaSourceTurner = Ecology.turnerHansonEffect

mediaSource2026 : Ecology.PoliticalEcologySource
mediaSource2026 = Ecology.abcMasterTheMedia2026

groomSource : Ecology.PoliticalEcologySource
groomSource = Ecology.abcGroom2020

economicPressureSource : Ecology.PoliticalEcologySource
economicPressureSource = Ecology.abcOuterSuburban2026

middleClassStatusSource : Ecology.PoliticalEcologySource
middleClassStatusSource = Ecology.uneMiddleClassRoots

barnabySource : Ecology.PoliticalEcologySource
barnabySource = Ecology.abcBarnabyDefection2025

policySource : Ecology.PoliticalEcologySource
policySource = Ecology.oneNationNationalIssues2026

------------------------------------------------------------------------
-- PUBLIC INTERFACE / POLITICAL ENVIRONMENT
------------------------------------------------------------------------

data HansonInterfaceFeature : Set where
  plainSpeechRegister : HansonInterfaceFeature
  conflictPerformance : HansonInterfaceFeature
  outsiderVictimPosition : HansonInterfaceFeature
  highNameRecognition : HansonInterfaceFeature
  longPoliticalMemory : HansonInterfaceFeature
  battlerRegister : HansonInterfaceFeature

canonicalHansonInterface : List HansonInterfaceFeature
canonicalHansonInterface =
  plainSpeechRegister
  ∷ conflictPerformance
  ∷ outsiderVictimPosition
  ∷ highNameRecognition
  ∷ longPoliticalMemory
  ∷ battlerRegister
  ∷ []

data EnvironmentAxis : Set where
  regionalConservativeInheritance : EnvironmentAxis
  mediaAttentionStructure : EnvironmentAxis
  classStatusConfiguration : EnvironmentAxis
  householdEconomicPressure : EnvironmentAxis
  migrationIdentityConflict : EnvironmentAxis
  majorPartyPositioning : EnvironmentAxis
  personnelNetworkCapacity : EnvironmentAxis
  donorEliteNetwork : EnvironmentAxis
  partyOrganisation : EnvironmentAxis
  socialPlatformStructure : EnvironmentAxis
  policyIssueSalience : EnvironmentAxis
  institutionalRepresentation : EnvironmentAxis

canonicalEnvironmentAxes : List EnvironmentAxis
canonicalEnvironmentAxes =
  regionalConservativeInheritance
  ∷ mediaAttentionStructure
  ∷ classStatusConfiguration
  ∷ householdEconomicPressure
  ∷ migrationIdentityConflict
  ∷ majorPartyPositioning
  ∷ personnelNetworkCapacity
  ∷ donorEliteNetwork
  ∷ partyOrganisation
  ∷ socialPlatformStructure
  ∷ policyIssueSalience
  ∷ institutionalRepresentation
  ∷ []

------------------------------------------------------------------------
-- EXACT NON-FACTORABILITY WITNESS
--
-- This finite specimen is structural/synthetic.  It proves that a model which
-- observes only a fixed Hanson-style public interface cannot, in general,
-- determine political reach once environment is allowed to vary.
--
-- It does NOT claim that these two constructor states literally instantiate
-- historical Australia or quantify a real-world media treatment effect.
------------------------------------------------------------------------

data HansonEquilibriumState : Set where
  sameInterfaceLowReachEnvironment : HansonEquilibriumState
  sameInterfaceHighReachEnvironment : HansonEquilibriumState

data HansonInterfaceSurface : Set where
  sameHansonInterface : HansonInterfaceSurface

interfaceObserver : HansonEquilibriumState → HansonInterfaceSurface
interfaceObserver sameInterfaceLowReachEnvironment = sameHansonInterface
interfaceObserver sameInterfaceHighReachEnvironment = sameHansonInterface

data PoliticalReach : Set where
  constrainedReach : PoliticalReach
  expandedReach : PoliticalReach

politicalReachConsumer : HansonEquilibriumState → PoliticalReach
politicalReachConsumer sameInterfaceLowReachEnvironment = constrainedReach
politicalReachConsumer sameInterfaceHighReachEnvironment = expandedReach

politicalReachDiffers :
  politicalReachConsumer sameInterfaceLowReachEnvironment ≡
  politicalReachConsumer sameInterfaceHighReachEnvironment → ⊥
politicalReachDiffers ()

sameInterfaceDifferentReachWitness :
  NF.NonFactorabilityWitness interfaceObserver politicalReachConsumer
sameInterfaceDifferentReachWitness =
  NF.nonFactorabilityWitness
    sameInterfaceLowReachEnvironment
    sameInterfaceHighReachEnvironment
    refl
    politicalReachDiffers

hansonInterfaceAloneCannotDeterminePoliticalReach :
  NF.FactorsThrough interfaceObserver politicalReachConsumer → ⊥
hansonInterfaceAloneCannotDeterminePoliticalReach =
  NF.witnessRulesOutEveryFlatFactorisation
    sameInterfaceDifferentReachWitness

------------------------------------------------------------------------
-- DUAL NON-FACTORABILITY: ENVIRONMENT LABEL ALONE ALSO FAILS.
--
-- The reverse collapse is forbidden as well: a broad environmental label
-- cannot determine a person's or party's exact political performance without
-- the actor/organisation coordinates.
------------------------------------------------------------------------

data SameEnvironmentDifferentActorState : Set where
  sameEnvironmentLowReachActor : SameEnvironmentDifferentActorState
  sameEnvironmentHighReachActor : SameEnvironmentDifferentActorState

data BroadEnvironmentSurface : Set where
  sameBroadEnvironment : BroadEnvironmentSurface

broadEnvironmentObserver :
  SameEnvironmentDifferentActorState → BroadEnvironmentSurface
broadEnvironmentObserver sameEnvironmentLowReachActor = sameBroadEnvironment
broadEnvironmentObserver sameEnvironmentHighReachActor = sameBroadEnvironment

actorReachConsumer : SameEnvironmentDifferentActorState → PoliticalReach
actorReachConsumer sameEnvironmentLowReachActor = constrainedReach
actorReachConsumer sameEnvironmentHighReachActor = expandedReach

actorReachDiffers :
  actorReachConsumer sameEnvironmentLowReachActor ≡
  actorReachConsumer sameEnvironmentHighReachActor → ⊥
actorReachDiffers ()

environmentAloneCannotDeterminePoliticalReach :
  NF.FactorsThrough broadEnvironmentObserver actorReachConsumer → ⊥
environmentAloneCannotDeterminePoliticalReach =
  NF.witnessRulesOutEveryFlatFactorisation
    (NF.nonFactorabilityWitness
      sameEnvironmentLowReachActor
      sameEnvironmentHighReachActor
      refl
      actorReachDiffers)

------------------------------------------------------------------------
-- RELATIONAL HISTORY FABRIC
--
-- Same present public register; different accumulated media/institutional/
-- organisational history; different gate/reach/future-cone code.
--
-- This uses repo-native generic history machinery rather than inventing a
-- parallel temporal ontology.
------------------------------------------------------------------------

data EquilibriumObservation : Set where
  samePresentRegister : EquilibriumObservation

data EquilibriumHistoryCode : Set where
  weakAmplificationHistory : EquilibriumHistoryCode
  accumulatedAmplificationHistory : EquilibriumHistoryCode

data EquilibriumRelationCode : Set where
  weakInstitutionalNetwork : EquilibriumRelationCode
  denseInstitutionalNetwork : EquilibriumRelationCode

data EquilibriumGateCode : Set where
  lowAttentionGate : EquilibriumGateCode
  highAttentionGate : EquilibriumGateCode

data EquilibriumReachableCode : Set where
  narrowReachableAudience : EquilibriumReachableCode
  broadReachableAudience : EquilibriumReachableCode

data EquilibriumAffordanceCode : Set where
  protestOnlyAffordance : EquilibriumAffordanceCode
  institutionalExpansionAffordance : EquilibriumAffordanceCode

data EquilibriumFutureCone : Set where
  constrainedContinuation : EquilibriumFutureCone
  expandedContinuation : EquilibriumFutureCone

politicalEquilibriumFabric : History.RelationalHistoryFabric
politicalEquilibriumFabric =
  record
    { SituatedState = HansonEquilibriumState
    ; Observation = EquilibriumObservation
    ; HistoryCode = EquilibriumHistoryCode
    ; RelationCode = EquilibriumRelationCode
    ; GateCode = EquilibriumGateCode
    ; ReachableCode = EquilibriumReachableCode
    ; AffordanceCode = EquilibriumAffordanceCode
    ; FutureConeCode = EquilibriumFutureCone
    ; observe = λ _ → samePresentRegister
    ; historyOf = λ
        { sameInterfaceLowReachEnvironment → weakAmplificationHistory
        ; sameInterfaceHighReachEnvironment → accumulatedAmplificationHistory
        }
    ; relationOf = λ
        { sameInterfaceLowReachEnvironment → weakInstitutionalNetwork
        ; sameInterfaceHighReachEnvironment → denseInstitutionalNetwork
        }
    ; gateOf = λ
        { sameInterfaceLowReachEnvironment → lowAttentionGate
        ; sameInterfaceHighReachEnvironment → highAttentionGate
        }
    ; reachableOf = λ
        { sameInterfaceLowReachEnvironment → narrowReachableAudience
        ; sameInterfaceHighReachEnvironment → broadReachableAudience
        }
    ; affordanceOf = λ
        { sameInterfaceLowReachEnvironment → protestOnlyAffordance
        ; sameInterfaceHighReachEnvironment → institutionalExpansionAffordance
        }
    ; futureConeOf = λ
        { sameInterfaceLowReachEnvironment → constrainedContinuation
        ; sameInterfaceHighReachEnvironment → expandedContinuation
        }
    ; fabricReading =
        "A comparatively stable public-performance register can coexist with different accumulated media, network and institutional histories, yielding different reachable political affordances; this finite fabric is a structural witness, not an empirical effect-size model."
    }

samePresentDifferentFuture :
  History.SameObservationDifferentFuture politicalEquilibriumFabric
samePresentDifferentFuture =
  record
    { leftState = sameInterfaceLowReachEnvironment
    ; rightState = sameInterfaceHighReachEnvironment
    ; sameObservation = refl
    ; differentFutureCone = λ ()
    }

presentRegisterCannotDetermineFutureCone :
  NF.FactorsThrough
    (History.observe politicalEquilibriumFabric)
    (History.futureConeOf politicalEquilibriumFabric) →
  ⊥
presentRegisterCannotDetermineFutureCone =
  History.coarsePresentCannotDetermineFutureCone
    samePresentDifferentFuture

------------------------------------------------------------------------
-- AMPLIFICATION LINEAGE: AMPLIFIED != GENERATED
--
-- We reuse the generic amplification constitution.  The fact that a political
-- object is amplified, circulated or reported does not imply that the
-- amplifier generated the underlying political proposition or independently
-- verified it.
------------------------------------------------------------------------

amplificationBoundary : Amplification.AmplificationLineageBoundary
amplificationBoundary =
  Amplification.canonicalAmplificationLineageBoundary

data MediaAmplificationGeneratedHanson : Set where
data HansonGeneratedMediaStructure : Set where
data VisibilityCountEqualsIndependentSupport : Set where

mediaAmplificationDoesNotGeneratePerson :
  MediaAmplificationGeneratedHanson → ⊥
mediaAmplificationDoesNotGeneratePerson ()

personDoesNotGenerateWholeMediaStructure :
  HansonGeneratedMediaStructure → ⊥
personDoesNotGenerateWholeMediaStructure ()

visibilityDoesNotEqualIndependentSupport :
  VisibilityCountEqualsIndependentSupport → ⊥
visibilityDoesNotEqualIndependentSupport ()

------------------------------------------------------------------------
-- ACCESS / INTERFACE-COST HYPOTHESIS
--
-- The proposition that plain speech, recognisable conflict and familiar
-- cultural register lower the interpretive cost of entering a political
-- coalition is useful, but the cited source set does not presently establish
-- it as a quantified causal theorem.  It therefore remains an explicitly open
-- candidate interpretation.
------------------------------------------------------------------------

data InterfaceCostStatus : Set where
  candidateInterpretation : InterfaceCostStatus
  empiricallyPaid : InterfaceCostStatus

hansonInterfaceCostStatus : InterfaceCostStatus
hansonInterfaceCostStatus = candidateInterpretation

data RecognisableRegisterAutomaticallyLowersInterfaceCost : Set where

recognisableRegisterDoesNotAutoPayInterfaceCost :
  RecognisableRegisterAutomaticallyLowersInterfaceCost → ⊥
recognisableRegisterDoesNotAutoPayInterfaceCost ()

------------------------------------------------------------------------
-- MAJOR-PARTY / ONE-NATION RELATION
--
-- Barnaby Joyce's 2025 move is an observed institutional bridge.  It witnesses
-- permeability between established agrarian-conservative institutions and One
-- Nation.  It does not prove that the Nationals, Coalition and One Nation are
-- identical, nor that all voters transfer with personnel.
------------------------------------------------------------------------

data PersonnelDefectionImpliesPartyIdentity : Set where
data SeniorDefectionImpliesVoterTransfer : Set where
data SharedPolicyIssueImpliesWholePlatformIdentity : Set where

defectionDoesNotCollapseParties :
  PersonnelDefectionImpliesPartyIdentity → ⊥
defectionDoesNotCollapseParties ()

defectionDoesNotAutoTransferVoters :
  SeniorDefectionImpliesVoterTransfer → ⊥
defectionDoesNotAutoTransferVoters ()

sharedIssueDoesNotCollapsePlatforms :
  SharedPolicyIssueImpliesWholePlatformIdentity → ⊥
sharedIssueDoesNotCollapsePlatforms ()

------------------------------------------------------------------------
-- EQUILIBRIUM EXPLANATION SURFACE
--
-- This is an explanatory coordinate bundle, not a score or ranking.
------------------------------------------------------------------------

record HansonEquilibriumExplanation : Set where
  constructor hanson-equilibrium-explanation
  field
    interfaceFeatures : List HansonInterfaceFeature
    environmentAxes : List EnvironmentAxis

    interfaceAloneInsufficient : Bool
    interfaceAloneInsufficientIsTrue :
      interfaceAloneInsufficient ≡ true

    environmentAloneInsufficient : Bool
    environmentAloneInsufficientIsTrue :
      environmentAloneInsufficient ≡ true

    regionalInheritanceTracked : Bool
    mediaStructureTracked : Bool
    classStatusTracked : Bool
    economicPressureTracked : Bool
    identityConflictTracked : Bool
    majorPartyRelationTracked : Bool
    personnelNetworkTracked : Bool
    partyOrganisationTracked : Bool
    platformStructureTracked : Bool
    institutionalRepresentationTracked : Bool

    psychologicalDiagnosisRequired : Bool
    psychologicalDiagnosisRequiredIsFalse :
      psychologicalDiagnosisRequired ≡ false

    oneAxisCausallySufficient : Bool
    oneAxisCausallySufficientIsFalse :
      oneAxisCausallySufficient ≡ false

    politicalReachIsElectionForecast : Bool
    politicalReachIsElectionForecastIsFalse :
      politicalReachIsElectionForecast ≡ false

open HansonEquilibriumExplanation public

canonicalHansonEquilibriumExplanation : HansonEquilibriumExplanation
canonicalHansonEquilibriumExplanation =
  hanson-equilibrium-explanation
    canonicalHansonInterface
    canonicalEnvironmentAxes
    true refl
    true refl
    true
    true
    true
    true
    true
    true
    true
    true
    true
    true
    false refl
    false refl
    false refl

------------------------------------------------------------------------
-- FINAL NON-COLLAPSE THEOREMS
------------------------------------------------------------------------

data HansonPersonalityIsHansonPhenomenon : Set where
data HansonPhenomenonIsMediaEffect : Set where
data HansonPhenomenonIsEconomicGrievance : Set where
data HansonPhenomenonIsRegionalConservatism : Set where
data HansonPhenomenonIsImmigrationIssue : Set where
data HansonPhenomenonIsBillionaireNetwork : Set where

personalityDoesNotEqualPhenomenon :
  HansonPersonalityIsHansonPhenomenon → ⊥
personalityDoesNotEqualPhenomenon ()

mediaDoesNotEqualPhenomenon :
  HansonPhenomenonIsMediaEffect → ⊥
mediaDoesNotEqualPhenomenon ()

economicsDoesNotEqualPhenomenon :
  HansonPhenomenonIsEconomicGrievance → ⊥
economicsDoesNotEqualPhenomenon ()

regionDoesNotEqualPhenomenon :
  HansonPhenomenonIsRegionalConservatism → ⊥
regionDoesNotEqualPhenomenon ()

immigrationDoesNotEqualPhenomenon :
  HansonPhenomenonIsImmigrationIssue → ⊥
immigrationDoesNotEqualPhenomenon ()

eliteNetworkDoesNotEqualPhenomenon :
  HansonPhenomenonIsBillionaireNetwork → ⊥
eliteNetworkDoesNotEqualPhenomenon ()
