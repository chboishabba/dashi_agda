module DASHI.Reasoning.KantLacanZizekRuntime where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Cognition.PNF.EventAlgebra as PNF
import DASHI.Reasoning.KantAntinomyCore as Antinomy
import DASHI.Reasoning.KantCriticalCompiler as Kant
import DASHI.Reasoning.LacanDiscourseMatheme as Discourse
import DASHI.Reasoning.LacanFantasyDriveCore as Fantasy
import DASHI.Reasoning.LacanSignifierSubjectCore as Lacan
import DASHI.Reasoning.PNFZizekOperator as Zizek

------------------------------------------------------------------------
-- Typed composition:
--   Kant  : legitimacy and scope of synthesis
--   Lacan : subject/signifier/desire/discourse structure
--   Zizek : ideological closure, surplus, recurrence and working-through
------------------------------------------------------------------------

record KantianCriticalState : Set₁ where
  field
    event : PNF.EventPNF
    result : Kant.CriticalResult
    categoryReceipt : String
    schemaReceipt : String
    boundary : Kant.CriticalBoundary
    promotionBlockedWhenIllicit : Bool

record LacanianSubjectState : Set₁ where
  field
    criticalState : KantianCriticalState
    subject : Lacan.BarredSubject
    discourse : Discourse.StandardDiscourse
    fantasyCandidate : Fantasy.FantasyFrame
    registerProjection : Lacan.RegisterProjection
    subjectStructureCandidateOnly : Bool

record ZizekianIdeologyState : Set₁ where
  field
    subjectState : LacanianSubjectState
    typedGap : Zizek.TypedGap
    closurePresentation : Zizek.PNFIdeologicalClosure
    recurrenceLabel : String
    surplusReceipt : String
    politicalReadingCandidateOnly : Bool

record KantLacanZizekRuntime : Set₁ where
  field
    criticalAudit : PNF.EventPNF → KantianCriticalState
    subjectivise : KantianCriticalState → LacanianSubjectState
    ideologyAnalyse : LacanianSubjectState → ZizekianIdeologyState
    orderReceipt : String
    stagesMayCallRuntime : Bool
    runtimeCreatesEmpiricalTruth : Bool

record FailureRouting : Set where
  field
    pnfNoTypedMeet : PNF.ComparisonResult
    kantianNoMeet : Kant.CriticalResult
    kantianAntinomy : Kant.CriticalResult
    kantianParalogism : Kant.CriticalResult
    zizekParallaxCandidate : Zizek.TypedGap
    allFailureKindsIdentified : Bool

canonicalFailureRouting : FailureRouting
canonicalFailureRouting = record
  { pnfNoTypedMeet = PNF.noTypedMeet
  ; kantianNoMeet = Kant.noTypedMeetResult
  ; kantianAntinomy = Kant.antinomicResult
  ; kantianParalogism = Kant.formallyValidEquivocationResult
  ; zizekParallaxCandidate = Zizek.parallaxNoMeet
  ; allFailureKindsIdentified = false
  }

record KantLacanZizekAuthorityBoundary : Set where
  field
    dependencyOrderKantLacanZizek : Bool
    kantBoundaryEqualsLacanReal : Bool
    lacanResidualEqualsObjetA : Bool
    zizekIdeologyEqualsKantErrorCode : Bool
    antinomyParallaxAndContradictionDistinct : Bool
    runtimeCrossPollinatesPNF : Bool
    runtimeDiagnosesSubject : Bool
    runtimeProvesPoliticalTheory : Bool
    boundaryNote : String

canonicalKantLacanZizekAuthorityBoundary :
  KantLacanZizekAuthorityBoundary
canonicalKantLacanZizekAuthorityBoundary = record
  { dependencyOrderKantLacanZizek = true
  ; kantBoundaryEqualsLacanReal = false
  ; lacanResidualEqualsObjetA = false
  ; zizekIdeologyEqualsKantErrorCode = false
  ; antinomyParallaxAndContradictionDistinct = true
  ; runtimeCrossPollinatesPNF = true
  ; runtimeDiagnosesSubject = false
  ; runtimeProvesPoliticalTheory = false
  ; boundaryNote =
      "Kant checks synthesis, Lacan structures the subject of signification, and Zizek analyses ideological reproduction; each bridge remains typed and non-promoting."
  }
