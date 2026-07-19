module DASHI.Biology.RetinalDesignInferenceBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)

------------------------------------------------------------------------
-- Retinal design inference boundary.
--
-- This module formalises the argumentative structure rather than settling
-- theology.  In particular it separates:
--
--   * functional adequacy from global optimality;
--   * local compensatory optimisation from architectural optimality;
--   * evidence against unconstrained optimal design from evidence against
--     every possible designer hypothesis;
--   * criticism of an argument from criticism of its author.
--
-- The biological comparison is represented as a typed counterexample:
-- forward-facing photoreceptors show that an inverted architecture is not
-- logically necessary merely because vertebrate compensation works well.
------------------------------------------------------------------------

data RetinaArchitecture : Set where
  invertedVertebrate : RetinaArchitecture
  forwardCephalopod : RetinaArchitecture

data RetinalFeature : Set where
  blindSpot : RetinalFeature
  nerveLayerBeforePhotoreceptors : RetinalFeature
  mullerLightGuidance : RetinalFeature
  fovealClearing : RetinalFeature
  choroidalPerfusion : RetinalFeature
  noOpticDiscBlindSpot : RetinalFeature

data DesignPredicate : Set where
  viable : DesignPredicate
  highPerformance : DesignPredicate
  locallyOptimised : DesignPredicate
  globallyOptimal : DesignPredicate
  architecturallyNecessary : DesignPredicate
  intentionallyDesigned : DesignPredicate

data ClaimStrength : Set where
  boundedArchitectureClaim : ClaimStrength
  optimalDesignerClaim : ClaimStrength
  genericDesignerClaim : ClaimStrength
  noDesignerClaim : ClaimStrength

data EvidenceRole : Set where
  supports : EvidenceRole
  rebuts : EvidenceRole
  irrelevant : EvidenceRole
  underdetermines : EvidenceRole

data Fallacy : Set where
  adHominem : Fallacy
  poisoningTheWell : Fallacy
  appealToRidicule : Fallacy
  strawMan : Fallacy
  nonSequitur : Fallacy
  specialPleading : Fallacy
  cherryPicking : Fallacy
  movingGoalposts : Fallacy
  falseDilemma : Fallacy
  hastyGeneralisation : Fallacy
  scopeShift : Fallacy
  necessityFromUtility : Fallacy
  compensationImpliesOptimality : Fallacy
  counterexampleNeglect : Fallacy

data ArgumentMove : Set where
  compensationWorks : ArgumentMove
  thereforeArchitectureOptimal : ArgumentMove
  coolingBenefitsInversion : ArgumentMove
  thereforeInversionNecessary : ArgumentMove
  alternativeArchitectureExists : ArgumentMove
  thereforeNoDesignerExists : ArgumentMove
  insultOpponent : ArgumentMove
  thereforeOpponentFalse : ArgumentMove
  rejectPerfectDesign : ArgumentMove
  rejectEveryDesignHypothesis : ArgumentMove

architectureHas : RetinaArchitecture -> RetinalFeature -> Bool
architectureHas invertedVertebrate blindSpot = true
architectureHas invertedVertebrate nerveLayerBeforePhotoreceptors = true
architectureHas invertedVertebrate mullerLightGuidance = true
architectureHas invertedVertebrate fovealClearing = true
architectureHas invertedVertebrate choroidalPerfusion = true
architectureHas invertedVertebrate noOpticDiscBlindSpot = false
architectureHas forwardCephalopod blindSpot = false
architectureHas forwardCephalopod nerveLayerBeforePhotoreceptors = false
architectureHas forwardCephalopod mullerLightGuidance = false
architectureHas forwardCephalopod fovealClearing = false
architectureHas forwardCephalopod choroidalPerfusion = false
architectureHas forwardCephalopod noOpticDiscBlindSpot = true

------------------------------------------------------------------------
-- Local/global separation.
------------------------------------------------------------------------

record PerformanceProfile : Set where
  field
    architecture : RetinaArchitecture
    viableHeld : Bool
    highPerformanceHeld : Bool
    localOptimisationHeld : Bool
    globalOptimalityHeld : Bool

open PerformanceProfile public

vertebrateProfile : PerformanceProfile
vertebrateProfile =
  record
    { architecture = invertedVertebrate
    ; viableHeld = true
    ; highPerformanceHeld = true
    ; localOptimisationHeld = true
    ; globalOptimalityHeld = false
    }

cephalopodProfile : PerformanceProfile
cephalopodProfile =
  record
    { architecture = forwardCephalopod
    ; viableHeld = true
    ; highPerformanceHeld = true
    ; localOptimisationHeld = true
    ; globalOptimalityHeld = false
    }

vertebrate-performance-does-not-encode-global-optimality :
  highPerformanceHeld vertebrateProfile ≡ true
vertebrate-performance-does-not-encode-global-optimality = refl

vertebrate-global-optimality-not-promoted :
  globalOptimalityHeld vertebrateProfile ≡ false
vertebrate-global-optimality-not-promoted = refl

------------------------------------------------------------------------
-- Counterexample semantics.
--
-- A functioning alternative without the proposed architectural requirement
-- rebuts necessity.  It does not by itself prove atheism, evolutionary history,
-- or the non-existence of every constrained designer model.
------------------------------------------------------------------------

record ArchitecturalCounterexample : Set where
  field
    proposedNecessaryArchitecture : RetinaArchitecture
    alternativeArchitecture : RetinaArchitecture
    alternativeViable : Bool
    avoidsProposedArchitecture : Bool

open ArchitecturalCounterexample public

cephalopodCounterexample : ArchitecturalCounterexample
cephalopodCounterexample =
  record
    { proposedNecessaryArchitecture = invertedVertebrate
    ; alternativeArchitecture = forwardCephalopod
    ; alternativeViable = true
    ; avoidsProposedArchitecture = true
    }

necessityRebutted : ArchitecturalCounterexample -> Bool
necessityRebutted c with alternativeViable c | avoidsProposedArchitecture c
... | true | true = true
... | _ | _ = false

cephalopod-rebuts-inversion-necessity :
  necessityRebutted cephalopodCounterexample ≡ true
cephalopod-rebuts-inversion-necessity = refl

evidenceScope : ClaimStrength -> EvidenceRole
evidenceScope boundedArchitectureClaim = rebuts
evidenceScope optimalDesignerClaim = rebuts
evidenceScope genericDesignerClaim = underdetermines
evidenceScope noDesignerClaim = underdetermines

counterexample-rebuts-optimality-not-all-design :
  evidenceScope optimalDesignerClaim ≡ rebuts
counterexample-rebuts-optimality-not-all-design = refl

counterexample-underdetermines-generic-designer :
  evidenceScope genericDesignerClaim ≡ underdetermines
counterexample-underdetermines-generic-designer = refl

------------------------------------------------------------------------
-- Typed diagnosis of invalid inference moves.
------------------------------------------------------------------------

diagnose : ArgumentMove -> List Fallacy
diagnose compensationWorks = []
diagnose thereforeArchitectureOptimal =
  compensationImpliesOptimality ∷ nonSequitur ∷ []
diagnose coolingBenefitsInversion = []
diagnose thereforeInversionNecessary =
  necessityFromUtility ∷ counterexampleNeglect ∷ nonSequitur ∷ []
diagnose alternativeArchitectureExists = []
diagnose thereforeNoDesignerExists =
  scopeShift ∷ nonSequitur ∷ falseDilemma ∷ []
diagnose insultOpponent =
  adHominem ∷ poisoningTheWell ∷ appealToRidicule ∷ []
diagnose thereforeOpponentFalse =
  adHominem ∷ nonSequitur ∷ []
diagnose rejectPerfectDesign = []
diagnose rejectEveryDesignHypothesis =
  scopeShift ∷ movingGoalposts ∷ falseDilemma ∷ []

muller-cell-defence-fails-global-promotion :
  diagnose thereforeArchitectureOptimal ≡
    compensationImpliesOptimality ∷ nonSequitur ∷ []
muller-cell-defence-fails-global-promotion = refl

cooling-necessity-requires-counterexample-discharge :
  diagnose thereforeInversionNecessary ≡
    necessityFromUtility ∷ counterexampleNeglect ∷ nonSequitur ∷ []
cooling-necessity-requires-counterexample-discharge = refl

anti-creationist-insults-are-also-fallacious :
  diagnose insultOpponent ≡
    adHominem ∷ poisoningTheWell ∷ appealToRidicule ∷ []
anti-creationist-insults-are-also-fallacious = refl

------------------------------------------------------------------------
-- Burden and relevance gates.
------------------------------------------------------------------------

data BurdenState : Set where
  discharged : BurdenState
  outstanding : BurdenState
  shifted : BurdenState

data Question : Set where
  isArchitectureNecessary : Question
  isArchitectureOptimal : Question
  canArchitectureFunctionWell : Question
  doesAnyDesignerExist : Question

data AnswerKind : Set where
  alternativeArchitectureEvidence : AnswerKind
  compensationEvidence : AnswerKind
  performanceEvidence : AnswerKind
  theologicalAuxiliaryPremise : AnswerKind
  personalAttack : AnswerKind

relevance : Question -> AnswerKind -> EvidenceRole
relevance isArchitectureNecessary alternativeArchitectureEvidence = rebuts
relevance isArchitectureNecessary compensationEvidence = irrelevant
relevance isArchitectureNecessary performanceEvidence = irrelevant
relevance isArchitectureNecessary theologicalAuxiliaryPremise = supports
relevance isArchitectureNecessary personalAttack = irrelevant
relevance isArchitectureOptimal alternativeArchitectureEvidence = rebuts
relevance isArchitectureOptimal compensationEvidence = underdetermines
relevance isArchitectureOptimal performanceEvidence = underdetermines
relevance isArchitectureOptimal theologicalAuxiliaryPremise = supports
relevance isArchitectureOptimal personalAttack = irrelevant
relevance canArchitectureFunctionWell alternativeArchitectureEvidence = supports
relevance canArchitectureFunctionWell compensationEvidence = supports
relevance canArchitectureFunctionWell performanceEvidence = supports
relevance canArchitectureFunctionWell theologicalAuxiliaryPremise = irrelevant
relevance canArchitectureFunctionWell personalAttack = irrelevant
relevance doesAnyDesignerExist alternativeArchitectureEvidence = underdetermines
relevance doesAnyDesignerExist compensationEvidence = underdetermines
relevance doesAnyDesignerExist performanceEvidence = underdetermines
relevance doesAnyDesignerExist theologicalAuxiliaryPremise = supports
relevance doesAnyDesignerExist personalAttack = irrelevant

compensation-does-not-answer-necessity :
  relevance isArchitectureNecessary compensationEvidence ≡ irrelevant
compensation-does-not-answer-necessity = refl

performance-underdetermines-optimality :
  relevance isArchitectureOptimal performanceEvidence ≡ underdetermines
performance-underdetermines-optimality = refl

personal-attack-never-answers-design-question :
  relevance doesAnyDesignerExist personalAttack ≡ irrelevant
personal-attack-never-answers-design-question = refl

------------------------------------------------------------------------
-- Canonical bounded reading.
------------------------------------------------------------------------

record RetinalDesignInferenceSurface : Set₁ where
  field
    Architecture : Set
    Feature : Set
    Predicate : Set
    FallacyKind : Set
    hasFeature : Architecture -> Feature -> Bool
    necessityCounterexample : ArchitecturalCounterexample
    counterexampleClosesNecessity :
      necessityRebutted necessityCounterexample ≡ true
    boundedConclusion : String
    nonPromotionBoundary : List String

retinalDesignInferenceSurface : RetinalDesignInferenceSurface
retinalDesignInferenceSurface =
  record
    { Architecture = RetinaArchitecture
    ; Feature = RetinalFeature
    ; Predicate = DesignPredicate
    ; FallacyKind = Fallacy
    ; hasFeature = architectureHas
    ; necessityCounterexample = cephalopodCounterexample
    ; counterexampleClosesNecessity = refl
    ; boundedConclusion =
        "The comparison rebuts claims that inversion is necessary or globally optimal; it does not alone decide every designer hypothesis"
    ; nonPromotionBoundary =
        "Functional adequacy is not global optimality"
        ∷ "Compensatory optimisation is not evidence that the compensated architecture was optimal"
        ∷ "A viable forward-facing retina defeats necessity-from-cooling without proving that cooling has no role"
        ∷ "Suboptimal architecture is evidence against unconstrained perfect design, not a deductive disproof of every creator model"
        ∷ "Ad hominem language remains fallacious even when the speaker's biological argument is otherwise sound"
        ∷ []
    }
