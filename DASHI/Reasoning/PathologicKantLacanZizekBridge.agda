module DASHI.Reasoning.PathologicKantLacanZizekBridge where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Reasoning.KantCriticalCompiler as Kant
import DASHI.Reasoning.LacanDiscourseMatheme as Discourse
import DASHI.Reasoning.PNFZizekOperator as Zizek
import DASHI.Reasoning.PathologicConstraintSystem as Constraint
import DASHI.Reasoning.PathologicPerspectiveHyperfabric as Perspective

------------------------------------------------------------------------
-- Governed Kant-Lacan-Zizek lenses over the three Pathologic routes.
--
-- These constructors type-check the internal architecture of each proposed
-- reading.  They do not prove that the game text uniquely entails the reading,
-- that a character is a clinical subject, or that one discourse exhausts a
-- route.  The attached review and source atlas provide interpretive provenance.
------------------------------------------------------------------------

data RouteIdeologyForm : Set where
  utopianSublimeClosure : RouteIdeologyForm
  embodiedSinthomaticRepair : RouteIdeologyForm
  sacrificialNonAllMediation : RouteIdeologyForm

data RouteLensEvidence :
    Constraint.Doctor →
    Kant.CriticalResult →
    Discourse.StandardDiscourse →
    Zizek.TypedGap →
    Perspective.EndingProposal →
    RouteIdeologyForm →
    Set where

  bachelorLensEvidence :
    RouteLensEvidence
      Constraint.bachelor
      Kant.transcendentalIllusionResult
      Discourse.universityDiscourse
      Zizek.parallaxNoMeet
      Perspective.bachelorProposal
      utopianSublimeClosure

  haruspexLensEvidence :
    RouteLensEvidence
      Constraint.haruspex
      Kant.regulativeResult
      Discourse.analystDiscourse
      Zizek.residualGap
      Perspective.haruspexProposal
      embodiedSinthomaticRepair

  changelingLensEvidence :
    RouteLensEvidence
      Constraint.changeling
      Kant.noTypedMeetResult
      Discourse.hystericDiscourse
      Zizek.parallaxNoMeet
      Perspective.changelingProposal
      sacrificialNonAllMediation

record RouteInterpretiveLens : Set where
  field
    doctor : Constraint.Doctor
    criticalResult : Kant.CriticalResult
    discourse : Discourse.StandardDiscourse
    typedGap : Zizek.TypedGap
    ending : Perspective.EndingProposal
    ideologyForm : RouteIdeologyForm
    evidence :
      RouteLensEvidence
        doctor criticalResult discourse typedGap ending ideologyForm
    kantReading : String
    lacanReading : String
    zizekReading : String
    sourceDerivationReceipt : String
    interpretationCandidateOnly : Bool
    interpretationCandidateOnlyIsTrue :
      interpretationCandidateOnly ≡ true
    clinicalDiagnosisPromoted : Bool
    clinicalDiagnosisPromotedIsFalse :
      clinicalDiagnosisPromoted ≡ false
    uniqueReadingClaimed : Bool
    uniqueReadingClaimedIsFalse : uniqueReadingClaimed ≡ false

open RouteInterpretiveLens public

bachelorInterpretiveLens : RouteInterpretiveLens
bachelorInterpretiveLens = record
  { doctor = Constraint.bachelor
  ; criticalResult = Kant.transcendentalIllusionResult
  ; discourse = Discourse.universityDiscourse
  ; typedGap = Zizek.parallaxNoMeet
  ; ending = Perspective.bachelorProposal
  ; ideologyForm = utopianSublimeClosure
  ; evidence = bachelorLensEvidence
  ; kantReading =
      "A regulative aspiration to defeat death risks constitutive reification and scope excess."
  ; lacanReading =
      "A knowledge-led discourse candidate whose universalising programme remains split by excluded local knowledge."
  ; zizekReading =
      "The Polyhedron may function as a sublime closure object whose preservation externalises the town as obstacle."
  ; sourceDerivationReceipt =
      "Candidate synthesis of route mechanics, ending structure and the attached hbomberguy review; not a unique textual theorem."
  ; interpretationCandidateOnly = true
  ; interpretationCandidateOnlyIsTrue = refl
  ; clinicalDiagnosisPromoted = false
  ; clinicalDiagnosisPromotedIsFalse = refl
  ; uniqueReadingClaimed = false
  ; uniqueReadingClaimedIsFalse = refl
  }

haruspexInterpretiveLens : RouteInterpretiveLens
haruspexInterpretiveLens = record
  { doctor = Constraint.haruspex
  ; criticalResult = Kant.regulativeResult
  ; discourse = Discourse.analystDiscourse
  ; typedGap = Zizek.residualGap
  ; ending = Perspective.haruspexProposal
  ; ideologyForm = embodiedSinthomaticRepair
  ; evidence = haruspexLensEvidence
  ; kantReading =
      "Situated schemata and embodied access revise the outsider's attempted universalisation."
  ; lacanReading =
      "An analyst-discourse candidate organised around retained cause, bodily knowledge and transformation rather than total mastery."
  ; zizekReading =
      "The route works through the town's wound by reorganising relations while accepting a constitutive loss."
  ; sourceDerivationReceipt =
      "Candidate synthesis of route asymmetry, local medicine, Kin obligations and the town-versus-Polyhedron ending conflict."
  ; interpretationCandidateOnly = true
  ; interpretationCandidateOnlyIsTrue = refl
  ; clinicalDiagnosisPromoted = false
  ; clinicalDiagnosisPromotedIsFalse = refl
  ; uniqueReadingClaimed = false
  ; uniqueReadingClaimedIsFalse = refl
  }

changelingInterpretiveLens : RouteInterpretiveLens
changelingInterpretiveLens = record
  { doctor = Constraint.changeling
  ; criticalResult = Kant.noTypedMeetResult
  ; discourse = Discourse.hystericDiscourse
  ; typedGap = Zizek.parallaxNoMeet
  ; ending = Perspective.changelingProposal
  ; ideologyForm = sacrificialNonAllMediation
  ; evidence = changelingLensEvidence
  ; kantReading =
      "Conflicting appearances and claims resist one determining synthesis without additional evidence."
  ; lacanReading =
      "A divided, questioning position exposes the incompleteness of the other routes and leaks cross-layer knowledge."
  ; zizekReading =
      "Joint preservation is mediated by a marked sacrificial remainder rather than a cost-free reconciled whole."
  ; sourceDerivationReceipt =
      "Candidate synthesis of doubled identity, miracle ambiguity, metatheatrical knowledge and the sacrificial ending."
  ; interpretationCandidateOnly = true
  ; interpretationCandidateOnlyIsTrue = refl
  ; clinicalDiagnosisPromoted = false
  ; clinicalDiagnosisPromotedIsFalse = refl
  ; uniqueReadingClaimed = false
  ; uniqueReadingClaimedIsFalse = refl
  }

bachelorIsNotHaruspex :
  Constraint.bachelor ≡ Constraint.haruspex → ⊥
bachelorIsNotHaruspex ()

haruspexIsNotChangeling :
  Constraint.haruspex ≡ Constraint.changeling → ⊥
haruspexIsNotChangeling ()

record PathologicKLZAuthorityBoundary : Set where
  field
    routeReadingsTyped : Bool
    routeReadingsCandidateOnly : Bool
    oneDiscourseExhaustsCharacter : Bool
    endingChoiceProvesPoliticalDoctrine : Bool
    characterStructureDiagnosesPlayer : Bool
    reviewInterpretationEqualsGameSource : Bool
    boundaryNote : String

canonicalPathologicKLZAuthorityBoundary : PathologicKLZAuthorityBoundary
canonicalPathologicKLZAuthorityBoundary = record
  { routeReadingsTyped = true
  ; routeReadingsCandidateOnly = true
  ; oneDiscourseExhaustsCharacter = false
  ; endingChoiceProvesPoliticalDoctrine = false
  ; characterStructureDiagnosesPlayer = false
  ; reviewInterpretationEqualsGameSource = false
  ; boundaryNote =
      "The route lenses cross-pollinate exact repository types while keeping game text, review interpretation and philosophical projection as separate authority surfaces."
  }
