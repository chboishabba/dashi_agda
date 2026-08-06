module DASHI.Biology.TarotInterpretationPNFExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Biology.AssociativeDivinationPNFExact as Associative
import DASHI.Biology.TarotCarrierExact as Tarot
import DASHI.Biology.TarotSpreadHyperfabricExact as Spread
import DASHI.Cognition.PNF.EventAlgebra as EventPNF
import DASHI.Interop.SensibLawResidualLattice as Residual

------------------------------------------------------------------------
-- Tarot reading PNF reuses the existing associative-divination compiler.
-- Structural, autobiographical, therapeutic, and external claims remain in
-- distinct constructors rather than being silently promoted.
------------------------------------------------------------------------

record TarotReadingTrace : Set where
  constructor tarotReadingTrace
  field
    readingContextId : Nat
    readingLayout : Spread.TarotLayout
    associationTrace : Associative.AssociationTrace
    readingQuestion : String
    readingReceipt : String

open TarotReadingTrace public

compileTarotPNF : TarotReadingTrace → List Associative.PNFAtom
compileTarotPNF trace =
  Associative.compileAssociationPNF (associationTrace trace)

canonicalReflectiveTrace : TarotReadingTrace
canonicalReflectiveTrace =
  tarotReadingTrace
    78
    Spread.canonicalThreeCardLayout
    (Associative.associationTrace
      78
      Associative.elaboratedAssociation
      Associative.autobiographicalHypothesis
      true
      false)
    Spread.canonicalQuestion
    "random layout used as an associative probe"

canonicalReflectiveTraceCompilesWithoutExternalPrediction :
  compileTarotPNF canonicalReflectiveTrace
  ≡ Associative.castProduced 78
    ∷ Associative.participantSelected 78
    ∷ Associative.autobiographicalThemeHypothesized 78
    ∷ []
canonicalReflectiveTraceCompilesWithoutExternalPrediction = refl

------------------------------------------------------------------------
-- Bounded finite narrative selection with an explicit five-term cost.
------------------------------------------------------------------------

record NarrativeCost : Set where
  constructor narrativeCost
  field
    descriptionLength : Nat
    fitPenalty : Nat
    contradictionPenalty : Nat
    overreachPenalty : Nat
    omissionPenalty : Nat

open NarrativeCost public

totalCost : NarrativeCost → Nat
totalCost cost =
  descriptionLength cost
  + fitPenalty cost
  + contradictionPenalty cost
  + overreachPenalty cost
  + omissionPenalty cost

record NarrativeCandidate : Set where
  constructor narrativeCandidate
  field
    narrativeText : String
    narrativeCostValue : NarrativeCost
    candidateValidity : EventPNF.CandidateValidity
    narrativeProvenance : List String

open NarrativeCandidate public

record CandidateComparison : Set where
  constructor candidateComparison
  field
    selectedCandidate : NarrativeCandidate
    alternativeCandidate : NarrativeCandidate
    selectedCostBound :
      totalCost (narrativeCostValue selectedCandidate)
      ≤
      totalCost (narrativeCostValue alternativeCandidate)

open CandidateComparison public

record BoundedMDLSelection : Set where
  constructor boundedMDLSelection
  field
    selectedNarrative : NarrativeCandidate
    retainedAlternativeNarratives : List NarrativeCandidate
    pairwiseCostWitnesses : List CandidateComparison
    selectionReceipt : String

open BoundedMDLSelection public

canonicalSelectedNarrative canonicalDramaticAlternative : NarrativeCandidate
canonicalSelectedNarrative =
  narrativeCandidate
    "An inherited openness meets a present need for reflection; possible structural change remains unresolved."
    (narrativeCost 1 1 0 0 0)
    EventPNF.admissible
    ("Fool" ∷ "Hermit" ∷ "reversed Tower" ∷ "spread roles" ∷ [])
canonicalDramaticAlternative =
  narrativeCandidate
    "A catastrophic external event is certainly imminent."
    (narrativeCost 1 2 1 1 1)
    EventPNF.invalid
    ("selective Tower overreading" ∷ "external certainty unsupported" ∷ [])

canonicalSelectedCostIsTwo :
  totalCost (narrativeCostValue canonicalSelectedNarrative) ≡ 2
canonicalSelectedCostIsTwo = refl

canonicalAlternativeCostIsSix :
  totalCost (narrativeCostValue canonicalDramaticAlternative) ≡ 6
canonicalAlternativeCostIsSix = refl

twoIsAtMostSix : 2 ≤ 6
twoIsAtMostSix = s≤s (s≤s z≤n)

canonicalSelection : BoundedMDLSelection
canonicalSelection =
  boundedMDLSelection
    canonicalSelectedNarrative
    (canonicalDramaticAlternative ∷ [])
    (candidateComparison
      canonicalSelectedNarrative
      canonicalDramaticAlternative
      twoIsAtMostSix
      ∷ [])
    "finite candidate comparison retains the rejected dramatic alternative"

------------------------------------------------------------------------
-- Interpretation normal form and residual-preserving output.
------------------------------------------------------------------------

record TarotAuthorityFlags : Set where
  constructor tarotAuthorityFlags
  field
    historicalGameOriginSupported : Bool
    ancientEgyptianOriginSupported : Bool
    futureCausationProved : Bool
    clinicalDiagnosisAuthorised : Bool
    reflectiveInterpretationAvailable : Bool
    actionRecommendationRequiresJudgment : Bool

open TarotAuthorityFlags public

canonicalTarotAuthorityFlags : TarotAuthorityFlags
canonicalTarotAuthorityFlags =
  tarotAuthorityFlags true false false false true true

record InterpretationNF : Set where
  constructor interpretationNF
  field
    mdlSelection : BoundedMDLSelection
    unresolvedResiduals : List Residual.ResidualLevel
    interpretationProvenance : List String
    authorityFlags : TarotAuthorityFlags
    normalisationReceipt : String

open InterpretationNF public

canonicalInterpretationNF : InterpretationNF
canonicalInterpretationNF =
  interpretationNF
    canonicalSelection
    (Residual.partial ∷ [])
    ("Rider--Waite--Smith semantic table"
      ∷ "typed spread roles"
      ∷ "associative-divination PNF"
      ∷ "SensibLaw residual lattice"
      ∷ [])
    canonicalTarotAuthorityFlags
    "extract -> normalise -> place -> transport -> residualise -> finite MDL -> project"

interpretationResidualClass :
  InterpretationNF → EventPNF.ComparisonResult
interpretationResidualClass normalForm with unresolvedResiduals normalForm
... | [] = EventPNF.equivalent
... | residual ∷ _ = EventPNF.comparisonFromResidual residual

canonicalInterpretationRetainsResidualDifference :
  interpretationResidualClass canonicalInterpretationNF
  ≡ EventPNF.residuallyDifferent
canonicalInterpretationRetainsResidualDifference = refl

------------------------------------------------------------------------
-- Prediction and intervention are different causal lanes.
------------------------------------------------------------------------

data CausalLane : Set where
  independentlyFixedOutcome reflectiveActionIntervention : CausalLane

fixedOutcomeIsNotReflectiveIntervention :
  independentlyFixedOutcome ≡ reflectiveActionIntervention → ⊥
fixedOutcomeIsNotReflectiveIntervention ()

record TarotInterpretationBoundary : Set where
  constructor tarotInterpretationBoundary
  field
    randomLayoutPromotedToIndependentWorldFact : Bool
    participantResponseMayExposeAssociation : Bool
    readingMayChangeLaterAction : Bool
    changedActionIsPrecognition : Bool
    alternativesRetained : Bool
    residualsRetained : Bool
    clinicalOrCosmicAuthorityImported : Bool

canonicalTarotInterpretationBoundary : TarotInterpretationBoundary
canonicalTarotInterpretationBoundary =
  tarotInterpretationBoundary
    false
    true
    true
    false
    true
    true
    false
