module DASHI.Law.SmithInterpretationConsumerLegalFollowExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AdmissibleConsumerMDLHyperfabricExact as MDL
import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Core.RobustExperimentInferenceFrontierExact as Experiment
import DASHI.Core.ITIRInvestigationAcquisitionParetoExact as INV
import DASHI.Law.SensibLawLegalFollowProofSearchBridgeExact as LegalFollow
import DASHI.Reasoning.JusticeLeeSensibLawAdversarialProofGraphBidiExact as Lee
import DASHI.Culture.IndigenousKnowledgeStoryTwoEyedSeeingBidiExact as TwoEyed
import DASHI.Law.SensibLawWrongTypePluralAdmissibilityGridExact as Plural

------------------------------------------------------------------------
-- SMITH v CHIEF EXECUTIVE, QUEENSLAND CORRECTIVE SERVICES [2026] HCA 37
-- CONSUMER-RELATIVE INTERPRETATION / LEGAL-FOLLOW MAX-CUT
--
-- SOURCE / ATTRIBUTION DISCIPLINE
--
-- Primary legal specimen:
--   Smith v Chief Executive, Queensland Corrective Services [2026] HCA 37,
--   judgment 14 October 2026, user-supplied judgment.
--
-- Opinion-level attribution is preserved.  In particular, `literalism`,
-- `contextomy`, the s 48 Human Rights Act 2019 (Qld) analysis, and the
-- three-way distinction between conforming interpretation, severance and
-- partial disapplication below are attributed to Edelman J's reasons unless
-- a separate source receipt says otherwise.
--
-- The formal carriers, countermodels and cross-domain welds are DASHI work.
-- Existing Two-Eyed Seeing, Kimmerer, intersectionality, Lacan/Irigaray,
-- Justice Lee, experiment-design and investigative-Pareto owners retain their
-- own source authority.  Importing them here does not transfer authorship or
-- domain authority into Smith.
------------------------------------------------------------------------

record SourceAttribution : Set where
  constructor sourceAttribution
  field
    sourceReference : String
    opinionReference : String
    spanReference : String
    propositionReference : String

open SourceAttribution public

smithOrdersSource : SourceAttribution
smithOrdersSource = sourceAttribution
  "Smith v Chief Executive, Queensland Corrective Services [2026] HCA 37"
  "Orders of the Court"
  "orders 1-3; judgment 14 October 2026"
  "appeal allowed; QCS decision quashed and matter remitted according to law"

edelmanLiteralismContextomySource : SourceAttribution
edelmanLiteralismContextomySource = sourceAttribution
  "Smith v Chief Executive, Queensland Corrective Services [2026] HCA 37"
  "Edelman J"
  "[32]-[36]"
  "wide linguistic reading criticised as literalism/contextomy; purpose, context and rights bear on construction"

edelmanTechniqueSource : SourceAttribution
edelmanTechniqueSource = sourceAttribution
  "Smith v Chief Executive, Queensland Corrective Services [2026] HCA 37"
  "Edelman J"
  "[46]-[49]"
  "conforming interpretation is meaning-forming; severance and partial disapplication constrain application after meaning"

pluralityConstructionSource : SourceAttribution
pluralityConstructionSource = sourceAttribution
  "Smith v Chief Executive, Queensland Corrective Services [2026] HCA 37"
  "Gordon A-CJ and Beech-Jones J"
  "[4]"
  "assisted reproductive technology includes technology directly assisting conception or reproduction, not egg extraction/freezing that preserves fertility"

------------------------------------------------------------------------
-- 1. Query-indexed operative constellation.
------------------------------------------------------------------------

data StatutoryAtom : Set where
  participateAtom : StatutoryAtom
  assistedAtom : StatutoryAtom
  reproductiveAtom : StatutoryAtom
  technologyAtom : StatutoryAtom
  treatmentAtom : StatutoryAtom
  fertilityPreservationAtom : StatutoryAtom
  directReproductionAtom : StatutoryAtom
  purposeAtom : StatutoryAtom
  dignityAtom : StatutoryAtom
  healthAccessAtom : StatutoryAtom

data StatutoryRelation : Set where
  modifies : StatutoryRelation
  purposeOf : StatutoryRelation
  directlyAssists : StatutoryRelation
  preservesCapacityFor : StatutoryRelation
  constrainedByPurpose : StatutoryRelation
  rightsContext : StatutoryRelation

record OperativeConstellation : Set where
  constructor operativeConstellation
  field
    rootReference : String
    operativePhraseReference : String
    pnfGraphReference : String
    consumerReference : String
    jurisdictionReference : String
    temporalReference : String
    sourceTraceReference : String

open OperativeConstellation public

smithOperativeConstellation : OperativeConstellation
smithOperativeConstellation = operativeConstellation
  "smith:hca37:s22"
  "participate in assisted reproductive technology"
  "PNF graph over s 22(2), s 22(3)(a)(ii), statutory purpose/context and reviewed source links"
  "Australian statutory-construction consumer"
  "Queensland / High Court of Australia"
  "law as considered in judgment 14 October 2026"
  "exact judgment/statute spans remain source-pinned upstream"

------------------------------------------------------------------------
-- A coarse lexical label cannot recover the operative direct-assistance /
-- fertility-preservation distinction.  Reuse the canonical FactorsThrough
-- notion rather than creating a Smith-specific factorisation relation.
------------------------------------------------------------------------

data SmithSituation : Set where
  fertilityPreservationSituation : SmithSituation
  directReproductionSituation : SmithSituation

data CoarseARTLabel : Set where
  reproductiveTechnologyLabel : CoarseARTLabel

data OperativeARTDecision : Set where
  outsideDirectAssistanceConstruction : OperativeARTDecision
  insideDirectAssistanceConstruction : OperativeARTDecision

coarseARTProjection : SmithSituation → CoarseARTLabel
coarseARTProjection _ = reproductiveTechnologyLabel

operativeARTDecision : SmithSituation → OperativeARTDecision
operativeARTDecision fertilityPreservationSituation = outsideDirectAssistanceConstruction
operativeARTDecision directReproductionSituation = insideDirectAssistanceConstruction

operativeDecisionsDiffer :
  outsideDirectAssistanceConstruction ≡ insideDirectAssistanceConstruction → ⊥
operativeDecisionsDiffer ()

coarseARTNonFactorability :
  NF.NonFactorabilityWitness coarseARTProjection operativeARTDecision
coarseARTNonFactorability =
  NF.nonFactorabilityWitness
    fertilityPreservationSituation
    directReproductionSituation
    refl
    operativeDecisionsDiffer

coarseARTLabelCannotRecoverOperativeDecision :
  NF.FactorsThrough coarseARTProjection operativeARTDecision → ⊥
coarseARTLabelCannotRecoverOperativeDecision =
  NF.witnessRulesOutEveryFlatFactorisation coarseARTNonFactorability

------------------------------------------------------------------------
-- 2. Candidate interpretation space.
--
-- These constructors are candidate coordinates, not a claim that the listed
-- candidates exhaust every linguistically/logically compatible construction.
------------------------------------------------------------------------

data CandidateConstruction : Set where
  widePurposeConnectedConstruction : CandidateConstruction
  directAssistanceConstruction : CandidateConstruction
  unresolvedAlternativeConstruction : CandidateConstruction

record CandidateInterpretation : Set where
  constructor candidateInterpretation
  field
    construction : CandidateConstruction
    generatedFromConstellationReference : String
    textualCompatibilityReference : String
    logicalSalienceReference : String
    precedentTreatmentReference : String
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true
    createsLegalAuthority : Bool
    createsLegalAuthorityIsFalse : createsLegalAuthority ≡ false

smithWideCandidate : CandidateInterpretation
smithWideCandidate = candidateInterpretation
  widePurposeConnectedConstruction
  "smith operative constellation"
  "linguistically comfortable purpose-connected reading; attributed discussion: Edelman J [32]"
  "fertility-purpose relation is sufficient under this candidate"
  "lower-court/QCS path is source material for treatment, not automatic present authority"
  true refl false refl

smithDirectCandidate : CandidateInterpretation
smithDirectCandidate = candidateInterpretation
  directAssistanceConstruction
  "smith operative constellation"
  "direct-assistance/conception relation"
  "distinguishes fertility preservation from procedures that themselves directly assist reproduction"
  "Gordon A-CJ/Beech-Jones J [4]; Edelman J [36] are separate opinion-level receipts"
  true refl false refl

------------------------------------------------------------------------
-- 3. Consumer-relative informativeness.
--
-- A surface is informative only relative to the declared query.  Expressive
-- complexity is deliberately absent from the definition.
------------------------------------------------------------------------

data InterpretiveConsumer : Set where
  smithMeaningConsumer : InterpretiveConsumer
  exactQuotationConsumer : InterpretiveConsumer

data RepresentationSurface : Set where
  simpleAccessibleSurface : RepresentationSurface
  fullTechnicalSurface : RepresentationSurface
  elaborateAmbiguousSurface : RepresentationSurface
  multilingualPeerSurface : RepresentationSurface

data MeaningDistinction : Set where
  preservationVsDirectAssistance : MeaningDistinction
  purposeConnectedVsCapableByItself : MeaningDistinction
  meaningVsApplicationConstraint : MeaningDistinction

data Preserves :
    InterpretiveConsumer → RepresentationSurface → MeaningDistinction → Set where
  simplePreservesDirect :
    Preserves smithMeaningConsumer simpleAccessibleSurface preservationVsDirectAssistance
  simplePreservesPurpose :
    Preserves smithMeaningConsumer simpleAccessibleSurface purposeConnectedVsCapableByItself
  simplePreservesTechnique :
    Preserves smithMeaningConsumer simpleAccessibleSurface meaningVsApplicationConstraint

  fullPreservesDirect :
    Preserves smithMeaningConsumer fullTechnicalSurface preservationVsDirectAssistance
  fullPreservesPurpose :
    Preserves smithMeaningConsumer fullTechnicalSurface purposeConnectedVsCapableByItself
  fullPreservesTechnique :
    Preserves smithMeaningConsumer fullTechnicalSurface meaningVsApplicationConstraint

  multilingualPreservesDirect :
    Preserves smithMeaningConsumer multilingualPeerSurface preservationVsDirectAssistance
  multilingualPreservesPurpose :
    Preserves smithMeaningConsumer multilingualPeerSurface purposeConnectedVsCapableByItself
  multilingualPreservesTechnique :
    Preserves smithMeaningConsumer multilingualPeerSurface meaningVsApplicationConstraint

  elaboratePreservesPurpose :
    Preserves smithMeaningConsumer elaborateAmbiguousSurface purposeConnectedVsCapableByItself

AtLeastAsInformative :
  InterpretiveConsumer → RepresentationSurface → RepresentationSurface → Set
AtLeastAsInformative consumer left right =
  (distinction : MeaningDistinction) →
  Preserves consumer right distinction →
  Preserves consumer left distinction

simpleAtLeastAsInformativeAsFullForMeaning :
  AtLeastAsInformative smithMeaningConsumer simpleAccessibleSurface fullTechnicalSurface
simpleAtLeastAsInformativeAsFullForMeaning preservationVsDirectAssistance fullPreservesDirect = simplePreservesDirect
simpleAtLeastAsInformativeAsFullForMeaning purposeConnectedVsCapableByItself fullPreservesPurpose = simplePreservesPurpose
simpleAtLeastAsInformativeAsFullForMeaning meaningVsApplicationConstraint fullPreservesTechnique = simplePreservesTechnique

fullAtLeastAsInformativeAsSimpleForMeaning :
  AtLeastAsInformative smithMeaningConsumer fullTechnicalSurface simpleAccessibleSurface
fullAtLeastAsInformativeAsSimpleForMeaning preservationVsDirectAssistance simplePreservesDirect = fullPreservesDirect
fullAtLeastAsInformativeAsSimpleForMeaning purposeConnectedVsCapableByItself simplePreservesPurpose = fullPreservesPurpose
fullAtLeastAsInformativeAsSimpleForMeaning meaningVsApplicationConstraint simplePreservesTechnique = fullPreservesTechnique

multilingualAtLeastAsInformativeAsFullForMeaning :
  AtLeastAsInformative smithMeaningConsumer multilingualPeerSurface fullTechnicalSurface
multilingualAtLeastAsInformativeAsFullForMeaning preservationVsDirectAssistance fullPreservesDirect = multilingualPreservesDirect
multilingualAtLeastAsInformativeAsFullForMeaning purposeConnectedVsCapableByItself fullPreservesPurpose = multilingualPreservesPurpose
multilingualAtLeastAsInformativeAsFullForMeaning meaningVsApplicationConstraint fullPreservesTechnique = multilingualPreservesTechnique

record RepresentationParity
    (consumer : InterpretiveConsumer)
    (left right : RepresentationSurface) : Set where
  constructor representationParity
  field
    leftAtLeastRight : AtLeastAsInformative consumer left right
    rightAtLeastLeft : AtLeastAsInformative consumer right left

simpleFullMeaningParity :
  RepresentationParity smithMeaningConsumer simpleAccessibleSurface fullTechnicalSurface
simpleFullMeaningParity = representationParity
  simpleAtLeastAsInformativeAsFullForMeaning
  fullAtLeastAsInformativeAsSimpleForMeaning

record StrictlyMoreInformative
    (consumer : InterpretiveConsumer)
    (left right : RepresentationSurface) : Set₁ where
  constructor strictlyMoreInformative
  field
    atLeast : AtLeastAsInformative consumer left right
    separatingDistinction : MeaningDistinction
    leftPreservesSeparator : Preserves consumer left separatingDistinction
    rightCannotPreserveSeparator : Preserves consumer right separatingDistinction → ⊥

simpleAtLeastElaborateForMeaning :
  AtLeastAsInformative smithMeaningConsumer simpleAccessibleSurface elaborateAmbiguousSurface
simpleAtLeastElaborateForMeaning purposeConnectedVsCapableByItself elaboratePreservesPurpose = simplePreservesPurpose

simpleSurfaceStrictlyDominatesElaborateForMeaning :
  StrictlyMoreInformative
    smithMeaningConsumer
    simpleAccessibleSurface
    elaborateAmbiguousSurface
simpleSurfaceStrictlyDominatesElaborateForMeaning =
  strictlyMoreInformative
    simpleAtLeastElaborateForMeaning
    preservationVsDirectAssistance
    simplePreservesDirect
    (λ ())

------------------------------------------------------------------------
-- 4. Attributed counterexample / discriminator surface.
------------------------------------------------------------------------

data SmithProcedure : Set where
  eggExtractionAndFreezing : SmithProcedure
  endometriosisTreatment : SmithProcedure
  diagnosticLaparoscopy : SmithProcedure
  twistedOvaryRepair : SmithProcedure
  cycleMonitoringApp : SmithProcedure
  cancerFertilityPreservationTreatment : SmithProcedure

data ConsumerOutcome : Set where
  treatedAsART : ConsumerOutcome
  notTreatedAsART : ConsumerOutcome

record InterpretationCounterexample
    (candidate : CandidateConstruction) : Set where
  constructor interpretationCounterexample
  field
    procedure : SmithProcedure
    candidateOutcome : ConsumerOutcome
    discriminatingOutcome : ConsumerOutcome
    outcomesDiffer : candidateOutcome ≡ discriminatingOutcome → ⊥
    counterexampleSourceAttribution : SourceAttribution
    createsCorrectInterpretation : Bool
    createsCorrectInterpretationIsFalse : createsCorrectInterpretation ≡ false

smithWideConstructionCounterexample :
  InterpretationCounterexample widePurposeConnectedConstruction
smithWideConstructionCounterexample =
  interpretationCounterexample
    cycleMonitoringApp
    treatedAsART
    notTreatedAsART
    (λ ())
    edelmanLiteralismContextomySource
    false refl

------------------------------------------------------------------------
-- 5. Experimental-design handoff.
------------------------------------------------------------------------

record DiscriminatorDesignHandoff : Set where
  constructor discriminatorDesignHandoff
  field
    discriminatorResidualReference : String
    targetDistinctionReference : String
    experimentDesignReference : String
    genericExperimentBoundary : Experiment.RobustExperimentFrontierBoundary
    proposalOnly : Bool
    proposalOnlyIsTrue : proposalOnly ≡ true
    discriminatorCreatesClaimTruth : Bool
    discriminatorCreatesClaimTruthIsFalse : discriminatorCreatesClaimTruth ≡ false
    discriminatorCreatesLegalAuthority : Bool
    discriminatorCreatesLegalAuthorityIsFalse : discriminatorCreatesLegalAuthority ≡ false

smithDiscriminatorDesignHandoff : DiscriminatorDesignHandoff
smithDiscriminatorDesignHandoff = discriminatorDesignHandoff
  "smith:residual:wide-vs-direct"
  "preservation vs direct assistance; purpose-connected vs capable-by-itself"
  "DASHI.Core.RobustExperimentInferenceFrontierExact / experimental discriminator route"
  Experiment.canonicalRobustExperimentFrontierBoundary
  true refl
  false refl
  false refl

------------------------------------------------------------------------
-- 6. Investigative Pareto handoff.
------------------------------------------------------------------------

smithPrimaryAuthorityCandidate : INV.InvestigationCandidate
smithPrimaryAuthorityCandidate = INV.investigation-candidate
  "smith:acquire:primary-authority"
  "smith:residual:wide-vs-direct"
  "official judgment/statute/case-law follow"
  "lawful provider/public-court access required"
  "primary-source genealogy retained"
  "reviewed axis estimates only"
  9 8 8 9 4
  true refl false refl false refl

record AcquisitionParetoHandoff : Set where
  constructor acquisitionParetoHandoff
  field
    selectedCandidate : INV.InvestigationCandidate
    directParetoView : INV.DirectMixedParetoView
    paretoScalarScoreUsed : Bool
    paretoScalarScoreUsedIsFalse : paretoScalarScoreUsed ≡ false
    paretoCreatesSourceTruth : Bool
    paretoCreatesSourceTruthIsFalse : paretoCreatesSourceTruth ≡ false
    paretoCreatesAccessAuthority : Bool
    paretoCreatesAccessAuthorityIsFalse : paretoCreatesAccessAuthority ≡ false
    paretoCreatesLegalAuthority : Bool
    paretoCreatesLegalAuthorityIsFalse : paretoCreatesLegalAuthority ≡ false

smithParetoAcquisitionHandoff : AcquisitionParetoHandoff
smithParetoAcquisitionHandoff = acquisitionParetoHandoff
  smithPrimaryAuthorityCandidate
  INV.investigationParetoView
  false refl
  false refl
  false refl
  false refl

------------------------------------------------------------------------
-- 7. LegalFollow reuse.
------------------------------------------------------------------------

record SmithLegalFollowHandoff : Set where
  constructor smithLegalFollowHandoffRecord
  field
    legalResidualReference : String
    constellation : OperativeConstellation
    proofSearchBoundary : LegalFollow.LegalFollowProofSearchBoundary
    jurisdictionConstraintReference : String
    sourceRoleConstraintReference : String
    authorityConstraintReference : String
    samePNFReentryReference : String
    acquisitionPaysResidual : Bool
    acquisitionPaysResidualIsFalse : acquisitionPaysResidual ≡ false

canonicalSmithLegalFollowHandoff : SmithLegalFollowHandoff
canonicalSmithLegalFollowHandoff = smithLegalFollowHandoffRecord
  "smith:residual:wide-vs-direct"
  smithOperativeConstellation
  LegalFollow.canonicalLegalFollowProofSearchBoundary
  "Australian / Queensland / HCA as applicable to the declared consumer"
  "primary legislation and case law preferred for authority payment; other roles retained distinctly"
  "authority/treatment assessed after acquisition and review"
  "same parser / PNF re-entry; no parallel interpretation store"
  false refl

------------------------------------------------------------------------
-- 8. Meaning formation != application constraint (attributed to Edelman J).
------------------------------------------------------------------------

data InterpretiveTechnique : Set where
  conformingInterpretation : InterpretiveTechnique
  severance : InterpretiveTechnique
  partialDisapplication : InterpretiveTechnique

data TechniquePhase : Set where
  meaningFormation : TechniquePhase
  applicationConstraint : TechniquePhase

techniquePhase : InterpretiveTechnique → TechniquePhase
techniquePhase conformingInterpretation = meaningFormation
techniquePhase severance = applicationConstraint
techniquePhase partialDisapplication = applicationConstraint

conformingIsMeaningFormation : techniquePhase conformingInterpretation ≡ meaningFormation
conformingIsMeaningFormation = refl

severanceIsApplicationConstraint : techniquePhase severance ≡ applicationConstraint
severanceIsApplicationConstraint = refl

partialDisapplicationIsApplicationConstraint :
  techniquePhase partialDisapplication ≡ applicationConstraint
partialDisapplicationIsApplicationConstraint = refl

meaningAndApplicationPhasesDiffer : meaningFormation ≡ applicationConstraint → ⊥
meaningAndApplicationPhasesDiffer ()

------------------------------------------------------------------------
-- 9. Reused cross-domain boundaries.
------------------------------------------------------------------------

consumerMDLBoundary : MDL.AdmissibleConsumerMDLBoundary
consumerMDLBoundary = MDL.canonicalAdmissibleConsumerMDLBoundary

justiceLeeAuthorityBoundary : Lee.AuthorityBoundary
justiceLeeAuthorityBoundary = Lee.canonicalAuthorityBoundary

legalFollowBoundary : LegalFollow.LegalFollowProofSearchBoundary
legalFollowBoundary = LegalFollow.canonicalLegalFollowProofSearchBoundary

investigationBoundary : INV.InvestigationAcquisitionBoundary
investigationBoundary = INV.canonicalInvestigationAcquisitionBoundary

twoEyedReuseReference : String
twoEyedReuseReference =
  "DASHI.Culture.IndigenousKnowledgeStoryTwoEyedSeeingBidiExact: coordination without epistemic fusion; translation may preserve/add/erase/unresolve"

pluralAdmissibilityReuseReference : String
pluralAdmissibilityReuseReference =
  "DASHI.Law.SensibLawWrongTypePluralAdmissibilityGridExact: query-indexed admissibility and erased-axis non-factorability"

------------------------------------------------------------------------
-- 10. Terminal no-collapse boundary.
------------------------------------------------------------------------

record SmithInterpretationBoundary : Set where
  constructor smithInterpretationBoundary
  field
    complexityCreatesAuthority : Bool
    complexityCreatesAuthorityIsFalse : complexityCreatesAuthority ≡ false

    precedentExhaustsInterpretationUniverse : Bool
    precedentExhaustsInterpretationUniverseIsFalse :
      precedentExhaustsInterpretationUniverse ≡ false

    experimentalDiscriminatorCreatesTruth : Bool
    experimentalDiscriminatorCreatesTruthIsFalse :
      experimentalDiscriminatorCreatesTruth ≡ false

    investigativeParetoUsesScalarScore : Bool
    investigativeParetoUsesScalarScoreIsFalse :
      investigativeParetoUsesScalarScore ≡ false

    legalFollowAcquisitionPaysResidual : Bool
    legalFollowAcquisitionPaysResidualIsFalse :
      legalFollowAcquisitionPaysResidual ≡ false

    structuralDistortionProvesSophistryIntent : Bool
    structuralDistortionProvesSophistryIntentIsFalse :
      structuralDistortionProvesSophistryIntent ≡ false

    machineSynthesisDeterminesJudgment : Bool
    machineSynthesisDeterminesJudgmentIsFalse :
      machineSynthesisDeterminesJudgment ≡ false

    twoEyedCoordinationRequiresEpistemicFusion : Bool
    twoEyedCoordinationRequiresEpistemicFusionIsFalse :
      twoEyedCoordinationRequiresEpistemicFusion ≡ false

    candidateWithoutPrecedentIsLogicallyImpossible : Bool
    candidateWithoutPrecedentIsLogicallyImpossibleIsFalse :
      candidateWithoutPrecedentIsLogicallyImpossible ≡ false

open SmithInterpretationBoundary public

canonicalSmithInterpretationBoundary : SmithInterpretationBoundary
canonicalSmithInterpretationBoundary = smithInterpretationBoundary
  false refl
  false refl
  false refl
  false refl
  false refl
  false refl
  false refl
  false refl
  false refl
