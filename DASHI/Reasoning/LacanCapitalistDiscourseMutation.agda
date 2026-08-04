module DASHI.Reasoning.LacanCapitalistDiscourseMutation where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Reasoning.LacanDiscourseMatheme as Discourse
import DASHI.Reasoning.LacanSignifierSubjectCore as Lacan
import DASHI.Reasoning.SurplusChannelCore as Surplus

------------------------------------------------------------------------
-- Source calibration: Stijn Vanheule, "Capitalist Discourse, Subjectivity
-- and Lacanian Psychoanalysis", DOI 10.3389/fpsyg.2016.01948.
--
-- Capitalist discourse as a separately governed mutation of the Master's
-- discourse, not a fifth member of the standard Z/4 orbit.
------------------------------------------------------------------------

data ArrowState : Set where
  forwardArrow reversedArrow blockedArrow absentArrow : ArrowState

record DiscourseGraph : Set where
  field
    agentTerm otherTerm truthTerm productTerm : Lacan.LacanianTerm
    agentToOther : ArrowState
    truthToAgent : ArrowState
    otherToProduct : ArrowState
    productToTruth : ArrowState
    graphReceipt : String

masterGraph : DiscourseGraph
masterGraph = record
  { agentTerm = Lacan.masterSignifier
  ; otherTerm = Lacan.knowledgeNetwork
  ; truthTerm = Lacan.barredSubjectTerm
  ; productTerm = Lacan.objetATerm
  ; agentToOther = forwardArrow
  ; truthToAgent = forwardArrow
  ; otherToProduct = forwardArrow
  ; productToTruth = blockedArrow
  ; graphReceipt = "standard master discourse graph"
  }

capitalistGraph : DiscourseGraph
capitalistGraph = record
  { agentTerm = Lacan.barredSubjectTerm
  ; otherTerm = Lacan.knowledgeNetwork
  ; truthTerm = Lacan.masterSignifier
  ; productTerm = Lacan.objetATerm
  ; agentToOther = absentArrow
  ; truthToAgent = reversedArrow
  ; otherToProduct = forwardArrow
  ; productToTruth = forwardArrow
  ; graphReceipt =
      "candidate formal transcription of the 1972 capitalist-discourse mutation: left terms exchanged, truth arrow reversed, ordinary agent-other link absent"
  }

record CapitalistMutationReceipt : Set where
  field
    source : DiscourseGraph
    target : DiscourseGraph
    sourceIsMaster : source ≡ masterGraph
    targetIsCapitalist : target ≡ capitalistGraph
    agentTruthTermsSwapped : Bool
    truthArrowReversed : Bool
    agentOtherArrowDeleted : Bool
    standardFourCyclePreservedClaimed : Bool
    noStructuralLapseProved : Bool
    historicalSourceRequired : Bool

canonicalCapitalistMutationReceipt : CapitalistMutationReceipt
canonicalCapitalistMutationReceipt = record
  { source = masterGraph
  ; target = capitalistGraph
  ; sourceIsMaster = refl
  ; targetIsCapitalist = refl
  ; agentTruthTermsSwapped = true
  ; truthArrowReversed = true
  ; agentOtherArrowDeleted = true
  ; standardFourCyclePreservedClaimed = false
  ; noStructuralLapseProved = false
  ; historicalSourceRequired = true
  }

record CapitalistSurplusProjection : Set₁ where
  field
    mutation : CapitalistMutationReceipt
    surplusVector : Surplus.PNFResidualSurplusVector
    valueChannelPrivilegedByReading : Bool
    enjoymentChannelRetained : Bool
    knowledgeChannelRetained : Bool
    powerChannelRetained : Bool
    allChannelsIdentified : Bool
    calibrationReceipt : String

record CapitalistDiscourseAuthorityBoundary : Set where
  field
    mutationSeparatedFromStandardOrbit : Bool
    graphMutationExact : Bool
    capitalismDefinitionallyStageNine : Bool
    noStructuralLapseTheoremAvailable : Bool
    allCapitalistSystemsHaveThisGraph : Bool
    surplusValueMathematicallyDerivedFromGraphAlone : Bool
    clinicalStructureInferredFromGraph : Bool
    boundaryNote : String

canonicalCapitalistDiscourseAuthorityBoundary :
  CapitalistDiscourseAuthorityBoundary
canonicalCapitalistDiscourseAuthorityBoundary = record
  { mutationSeparatedFromStandardOrbit = true
  ; graphMutationExact = true
  ; capitalismDefinitionallyStageNine = false
  ; noStructuralLapseTheoremAvailable = false
  ; allCapitalistSystemsHaveThisGraph = false
  ; surplusValueMathematicallyDerivedFromGraphAlone = false
  ; clinicalStructureInferredFromGraph = false
  ; boundaryNote =
      "The fifth discourse is represented as a sourced graph mutation and candidate surplus bridge, not as a universal theorem about economies, subjects or Stage 9."
  }
