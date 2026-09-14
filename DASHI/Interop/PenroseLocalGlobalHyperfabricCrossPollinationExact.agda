module DASHI.Interop.PenroseLocalGlobalHyperfabricCrossPollinationExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Reasoning.LocalFibreHyperfabricExact as LocalFibre
import DASHI.Core.NDimParetoHyperfabricExact as NDim
import DASHI.Core.AdmissibleConsumerMDLHyperfabricExact as Pareto
import DASHI.Combinatorics.GraphColouringRecolourPantsSnowballExact as Graph
import DASHI.Physics.Gravity.PenroseGlobalHorismosContradictionExact as Penrose
import DASHI.Physics.Gravity.PenroseGlobalCausalityAuthorityExact as Authority
import DASHI.ComputerScience.RSA260C3OrbitReducerHyperfabricExact as RSA
import DASHI.ComputerScience.RSA260ReducerHyperfabricSourceDiligenceExact as RSASources
import DASHI.ComputerScience.FlyStructureFunctionNDimFibreExact as Fly

------------------------------------------------------------------------
-- THIN LOCAL/GLOBAL CROSS-POLLINATION BRIDGE
--
-- This module records a shared dependency architecture across already-owned
-- theorem surfaces. It does not identify domain objects, import proofs from
-- citations, or assert historical influence among the source traditions.
------------------------------------------------------------------------

data LocalGlobalRole : Set where
  localWitness : LocalGlobalRole
  boundaryRestriction : LocalGlobalRole
  compatibilityCondition : LocalGlobalRole
  globalCompatibleObject : LocalGlobalRole
  projectionReduction : LocalGlobalRole
  globalObstruction : LocalGlobalRole
  reductioConclusion : LocalGlobalRole

------------------------------------------------------------------------
-- Penrose adapter: obstruction / reductio form.
------------------------------------------------------------------------

record PenroseLocalGlobalAdapter : Set where
  constructor penroseLocalGlobalAdapter
  field
    localWitnessReference : String
    boundaryCompatibilityReference : String
    globalObjectReference : String
    projectionReference : String
    globalObstructionReference : String
    reductioConclusionReference : String
    sameHorismosObjectPreserved : Bool
    sameHorismosObjectPreservedIsTrue : sameHorismosObjectPreserved ≡ true
    localFocusingDoesNotAlonePayGlobalObstruction : Bool
    localFocusingDoesNotAlonePayGlobalObstructionIsTrue :
      localFocusingDoesNotAlonePayGlobalObstruction ≡ true
    cauchyProjectionIsGlobalCausalityStep : Bool
    cauchyProjectionIsGlobalCausalityStepIsTrue :
      cauchyProjectionIsGlobalCausalityStep ≡ true
    sourceAuthorityRemainsOwnedByParent : Bool
    sourceAuthorityRemainsOwnedByParentIsTrue :
      sourceAuthorityRemainsOwnedByParent ≡ true

open PenroseLocalGlobalAdapter public

canonicalPenroseLocalGlobalAdapter : PenroseLocalGlobalAdapter
canonicalPenroseLocalGlobalAdapter = penroseLocalGlobalAdapter
  "trapped surface plus strictly negative future null expansions and local Raychaudhuri/Sachs focusing"
  "null generator remains on E+(T) only until focal/conjugate structure moves it into I+(T)"
  "the same future horismos E+(T) used by both compact and noncompact reductio claims"
  "Minguzzi 2019 Theorem 6.23 timelike-flow projection of E+(T) to a Cauchy hypersurface"
  "compactness and noncompactness are incompatible properties of the same E+(T) under the reductio assumptions"
  "discharge future null completeness; conclude future null geodesic incompleteness at the theorem boundary"
  (Penrose.sameHorismosObjectCarriesBothReductioClaims
    Penrose.canonicalPenroseGlobalHorismosBoundary)
  (Penrose.sameHorismosObjectCarriesBothReductioClaimsIsTrue
    Penrose.canonicalPenroseGlobalHorismosBoundary)
  true refl
  true refl
  (Authority.authorityCitationImportsNeitherProofNorAuthority
    Authority.canonicalGlobalCausalityAuthorityReceipt)
  (Authority.authorityCitationImportsNeitherProofNorAuthorityIsTrue
    Authority.canonicalGlobalCausalityAuthorityReceipt)

------------------------------------------------------------------------
-- Graph-colouring adapter: constructive gluing form.
------------------------------------------------------------------------

record GraphColouringLocalGlobalAdapter : Set where
  constructor graphColouringLocalGlobalAdapter
  field
    localMoveReference : String
    boundaryRestrictionReference : String
    seamCompatibilityReference : String
    recursiveCompatibilityReference : String
    globalColouringReference : String
    localMoveAutomaticallyPaysGlobalCompatibility : Bool
    localMoveAutomaticallyPaysGlobalCompatibilityIsFalse :
      localMoveAutomaticallyPaysGlobalCompatibility ≡ false

open GraphColouringLocalGlobalAdapter public

canonicalGraphColouringLocalGlobalAdapter : GraphColouringLocalGlobalAdapter
canonicalGraphColouringLocalGlobalAdapter = graphColouringLocalGlobalAdapter
  "GraphColouringRecolourPantsSnowballExact.localRecolourMove"
  "GraphColouringRecolourPantsSnowballExact.boundaryRestriction"
  "GraphColouringRecolourPantsSnowballExact.pantsSeamCompatibility"
  "GraphColouringRecolourPantsSnowballExact.recursiveGluingCompatibility"
  "GraphColouringRecolourPantsSnowballExact.globalColouring"
  (Graph.localRecolourImpliesGlobalGluingCompatibility
    Graph.canonicalGraphColouringPantsBoundary)
  refl

------------------------------------------------------------------------
-- LocalFibre adapter: existing restriction / compatible-section spine.
------------------------------------------------------------------------

record LocalFibreLocalGlobalAdapter : Set where
  constructor localFibreLocalGlobalAdapter
  field
    localCarrierOwnerReference : String
    restrictionOwnerReference : String
    compatibilityOwnerReference : String
    globalSectionReference : String
    penroseGlobalObjectIdentifiedWithHyperfabricGlobalSection : Bool
    penroseGlobalObjectIdentifiedWithHyperfabricGlobalSectionIsFalse :
      penroseGlobalObjectIdentifiedWithHyperfabricGlobalSection ≡ false

open LocalFibreLocalGlobalAdapter public

canonicalLocalFibreLocalGlobalAdapter : LocalFibreLocalGlobalAdapter
canonicalLocalFibreLocalGlobalAdapter = localFibreLocalGlobalAdapter
  (LocalFibre.localStalkOwner LocalFibre.canonicalLocalFibreAuthorityMap)
  (LocalFibre.restrictionTransportOwner LocalFibre.canonicalLocalFibreAuthorityMap)
  (LocalFibre.globalCompatibilityOwner LocalFibre.canonicalLocalFibreAuthorityMap)
  "DASHI.Reasoning.TypedHyperfabricCore.GlobalSection"
  false refl

------------------------------------------------------------------------
-- NDim projection adapter: projection is weaker than source sufficiency.
------------------------------------------------------------------------

record NDimProjectionAdapter : Set where
  constructor ndimProjectionAdapter
  field
    projectionOwnerReference : String
    fullInformationMayProject : Bool
    fullInformationMayProjectIsTrue : fullInformationMayProject ≡ true
    projectedResultPromotesSourceSufficiency : Bool
    projectedResultPromotesSourceSufficiencyIsFalse :
      projectedResultPromotesSourceSufficiency ≡ false
    cauchyProjectionIdentifiedWithParetoAxisProjection : Bool
    cauchyProjectionIdentifiedWithParetoAxisProjectionIsFalse :
      cauchyProjectionIdentifiedWithParetoAxisProjection ≡ false

open NDimProjectionAdapter public

canonicalNDimProjectionAdapter : NDimProjectionAdapter
canonicalNDimProjectionAdapter = ndimProjectionAdapter
  "DASHI.Core.NDimParetoHyperfabricExact.AxisProjection / fullDominanceImpliesProjected"
  true refl
  (NDim.projectedDominanceImpliesFullDominanceAutomatically
    NDim.canonicalNDimParetoHyperfabricBoundary)
  refl
  false refl

------------------------------------------------------------------------
-- RSA adapter: candidate compatibility is not terminal action validity.
--
-- The donor already requires co-requirement closure, consumer-conflict
-- selection, and final MP = PM. Its source-diligence owner separately blocks
-- transfer from graph-colouring / Monster source architecture to RSA theorem
-- authority. We reuse those states rather than re-authoring them.
------------------------------------------------------------------------

record RSACompatibilityClosureAdapter : Set where
  constructor rsaCompatibilityClosureAdapter
  field
    candidateReference : String
    closureReference : String
    conflictSelectionReference : String
    terminalConsumerReference : String
    coRequirementClosureRequired : Bool
    coRequirementClosureRequiredIsTrue : coRequirementClosureRequired ≡ true
    consumerConflictSelectionRequired : Bool
    consumerConflictSelectionRequiredIsTrue : consumerConflictSelectionRequired ≡ true
    globalCommutationRequired : Bool
    globalCommutationRequiredIsTrue : globalCommutationRequired ≡ true
    sourceArchitectureCreatesRSAAction : Bool
    sourceArchitectureCreatesRSAActionIsFalse : sourceArchitectureCreatesRSAAction ≡ false
    snowballAcquisitionOutOfOrderAllowed : Bool
    snowballAcquisitionOutOfOrderAllowedIsTrue : snowballAcquisitionOutOfOrderAllowed ≡ true
    snowballPaymentOutOfOrderAllowed : Bool
    snowballPaymentOutOfOrderAllowedIsFalse : snowballPaymentOutOfOrderAllowed ≡ false

open RSACompatibilityClosureAdapter public

canonicalRSACompatibilityClosureAdapter : RSACompatibilityClosureAdapter
canonicalRSACompatibilityClosureAdapter = rsaCompatibilityClosureAdapter
  "stable refinement class / inferred structured orbit candidate"
  "operator-derived co-requirement closure"
  "consumer-conflict-free closed-batch selection"
  "final global MP = PM commutation check"
  (RSA.coRequirementClosureStillRequired RSA.canonicalStructuredOrbitPromotionBoundary)
  refl
  (RSA.consumerConflictSelectionStillRequired RSA.canonicalStructuredOrbitPromotionBoundary)
  refl
  (RSA.globalMPEqualsPMStillRequired RSA.canonicalStructuredOrbitPromotionBoundary)
  refl
  (RSA.monster3BSourceImpliesRSAAction RSA.canonicalStructuredOrbitPromotionBoundary)
  refl
  (RSASources.acquisitionMayProceedOutOfDependencyOrder
    RSASources.canonicalSnowballAttributionBoundary)
  refl
  (RSASources.paymentMayProceedOutOfDependencyOrder
    RSASources.canonicalSnowballAttributionBoundary)
  refl

------------------------------------------------------------------------
-- Fly adapter: compatibility selection precedes and cannot replace held-out
-- consumer payment.
------------------------------------------------------------------------

record FlyHeldOutCompatibilityAdapter : Set where
  constructor flyHeldOutCompatibilityAdapter
  field
    restrictionReference : String
    compatibilityReference : String
    freezeReference : String
    terminalConsumerReference : String
    compatibilitySelectionUsesHeldOutOutcome : Bool
    compatibilitySelectionUsesHeldOutOutcomeIsFalse :
      compatibilitySelectionUsesHeldOutOutcome ≡ false
    compositionFitUsesHeldOutOutcome : Bool
    compositionFitUsesHeldOutOutcomeIsFalse :
      compositionFitUsesHeldOutOutcome ≡ false
    localCompatibilityAutomaticallyPaysGlobalImprovement : Bool
    localCompatibilityAutomaticallyPaysGlobalImprovementIsFalse :
      localCompatibilityAutomaticallyPaysGlobalImprovement ≡ false
    globalHeldOutEvaluationRequired : Bool
    globalHeldOutEvaluationRequiredIsTrue : globalHeldOutEvaluationRequired ≡ true
    unseenRegionEvaluationRequired : Bool
    unseenRegionEvaluationRequiredIsTrue : unseenRegionEvaluationRequired ≡ true

open FlyHeldOutCompatibilityAdapter public

canonicalFlyHeldOutCompatibilityAdapter : FlyHeldOutCompatibilityAdapter
canonicalFlyHeldOutCompatibilityAdapter = flyHeldOutCompatibilityAdapter
  "restrict structural fibres to training carrier"
  "build conflict graph and select a compatible fibre family without held-out outcomes"
  "fit on training pairs then freeze composition before evaluation"
  "held-out pairs, held-out regions, stability, and null-model consumers"
  (Fly.compatibilitySelectionUsesHeldOutOutcomes
    Fly.canonicalFlyNDimStructureFunctionBoundary)
  refl
  (Fly.compositionFitUsesHeldOutOutcomes
    Fly.canonicalFlyNDimStructureFunctionBoundary)
  refl
  (Fly.pairwiseCompatibilityAutomaticallyImpliesHeldOutImprovement
    Fly.canonicalFlyNDimStructureFunctionBoundary)
  refl
  (Fly.globalHeldOutEvaluationStillRequired
    Fly.canonicalFlyNDimStructureFunctionBoundary)
  refl
  (Fly.unseenRegionEvaluationStillRequired
    Fly.canonicalFlyNDimStructureFunctionBoundary)
  refl

------------------------------------------------------------------------
-- Pareto / MDL adapter: optimization occurs only inside the eligible stratum.
------------------------------------------------------------------------

record ParetoEligibilityBeforeOptimizationAdapter : Set where
  constructor paretoEligibilityBeforeOptimizationAdapter
  field
    eligibilityReference : String
    paretoReference : String
    lowerDescriptionLengthCreatesPhysicalTruth : Bool
    lowerDescriptionLengthCreatesPhysicalTruthIsFalse :
      lowerDescriptionLengthCreatesPhysicalTruth ≡ false
    inadmissibleCandidateMayWinByShortCode : Bool
    inadmissibleCandidateMayWinByShortCodeIsFalse :
      inadmissibleCandidateMayWinByShortCode ≡ false
    consumerInadequateCandidateMayWinByShortCode : Bool
    consumerInadequateCandidateMayWinByShortCodeIsFalse :
      consumerInadequateCandidateMayWinByShortCode ≡ false
    paretoAxesRemainApplicationDeclared : Bool
    paretoAxesRemainApplicationDeclaredIsTrue :
      paretoAxesRemainApplicationDeclared ≡ true

open ParetoEligibilityBeforeOptimizationAdapter public

canonicalParetoEligibilityBeforeOptimizationAdapter :
  ParetoEligibilityBeforeOptimizationAdapter
canonicalParetoEligibilityBeforeOptimizationAdapter =
  paretoEligibilityBeforeOptimizationAdapter
    "Eligible problem model = Admissible model × ConsumerAdequate model"
    "ParetoAdmissible is defined only over the eligible stratum"
    (Pareto.lowerDescriptionLengthIsPhysicalTruth
      Pareto.canonicalAdmissibleConsumerMDLBoundary)
    refl
    (Pareto.inadmissibleModelMayWinByShortCode
      Pareto.canonicalAdmissibleConsumerMDLBoundary)
    refl
    (Pareto.consumerInadequateModelMayWinByShortCode
      Pareto.canonicalAdmissibleConsumerMDLBoundary)
    refl
    (Pareto.paretoAxesAreApplicationDeclared
      Pareto.canonicalAdmissibleConsumerMDLBoundary)
    refl

------------------------------------------------------------------------
-- Shared terminal-consumer payment rule.
------------------------------------------------------------------------

terminalConsumerStillMustBePaid : Bool
terminalConsumerStillMustBePaid = true

terminalConsumerStillMustBePaidIsTrue : terminalConsumerStillMustBePaid ≡ true
terminalConsumerStillMustBePaidIsTrue = refl

compatibilityDoesNotCreateTerminalConsumerPayment : Bool
compatibilityDoesNotCreateTerminalConsumerPayment = true

compatibilityDoesNotCreateTerminalConsumerPaymentIsTrue :
  compatibilityDoesNotCreateTerminalConsumerPayment ≡ true
compatibilityDoesNotCreateTerminalConsumerPaymentIsTrue = refl

paretoSelectionCannotRescueIneligibleCandidate :
  Pareto.inadmissibleModelMayWinByShortCode
    Pareto.canonicalAdmissibleConsumerMDLBoundary ≡ false
paretoSelectionCannotRescueIneligibleCandidate = refl

transferredArchitectureDoesNotTransferTheoremAuthority :
  RSA.monster3BSourceImpliesRSAAction
    RSA.canonicalStructuredOrbitPromotionBoundary ≡ false
transferredArchitectureDoesNotTransferTheoremAuthority = refl

rsaSnowballPaymentCannotSkipDependency :
  RSASources.paymentMayProceedOutOfDependencyOrder
    RSASources.canonicalSnowballAttributionBoundary ≡ false
rsaSnowballPaymentCannotSkipDependency = refl

------------------------------------------------------------------------
-- Constructive gluing versus obstruction/reductio duality.
------------------------------------------------------------------------

record ConstructiveGluingObstructionDuality : Set where
  constructor constructiveGluingObstructionDuality
  field
    constructivePathReference : String
    obstructionPathReference : String
    constructivePathRecorded : Bool
    constructivePathRecordedIsTrue : constructivePathRecorded ≡ true
    obstructionPathRecorded : Bool
    obstructionPathRecordedIsTrue : obstructionPathRecorded ≡ true
    constructiveAndObstructionFormsIdentical : Bool
    constructiveAndObstructionFormsIdenticalIsFalse :
      constructiveAndObstructionFormsIdentical ≡ false
    sameObjectIdentityRequiredForReductio : Bool
    sameObjectIdentityRequiredForReductioIsTrue :
      sameObjectIdentityRequiredForReductio ≡ true

open ConstructiveGluingObstructionDuality public

canonicalConstructiveGluingObstructionDuality : ConstructiveGluingObstructionDuality
canonicalConstructiveGluingObstructionDuality = constructiveGluingObstructionDuality
  "local candidates -> restriction -> compatibility filter -> globally admissible family/object"
  "local dynamics -> P(X); global topology/constraint -> incompatible not-P(X) for the same X; discharge reductio assumption"
  true refl
  true refl
  false refl
  (Penrose.sameHorismosObjectCarriesBothReductioClaims
    Penrose.canonicalPenroseGlobalHorismosBoundary)
  (Penrose.sameHorismosObjectCarriesBothReductioClaimsIsTrue
    Penrose.canonicalPenroseGlobalHorismosBoundary)

------------------------------------------------------------------------
-- Mandatory WrongType and attribution firewalls.
------------------------------------------------------------------------

localValidityDoesNotImplyGlobalValidity : Bool
localValidityDoesNotImplyGlobalValidity = true

projectionValidityDoesNotImplySourceSufficiency : Bool
projectionValidityDoesNotImplySourceSufficiency = true

boundedLocalCarrierDoesNotImplyGlobalCompactnessOrClosure : Bool
boundedLocalCarrierDoesNotImplyGlobalCompactnessOrClosure = true

sharedProofArchitectureDoesNotIdentifyDomainTheorems : Bool
sharedProofArchitectureDoesNotIdentifyDomainTheorems = true

penroseProjectionIsNotParetoAxisProjection : Bool
penroseProjectionIsNotParetoAxisProjection = true

horismosIsNotHyperfabricGlobalSection : Bool
horismosIsNotHyperfabricGlobalSection = true

graphSeamCompatibilityIsNotLorentzianCompatibility : Bool
graphSeamCompatibilityIsNotLorentzianCompatibility = true

sameObjectReductioRequiresSameObjectIdentity : Bool
sameObjectReductioRequiresSameObjectIdentity =
  Penrose.sameHorismosObjectCarriesBothReductioClaims
    Penrose.canonicalPenroseGlobalHorismosBoundary

crossPollinationAddsNoNewSourceAuthority : Bool
crossPollinationAddsNoNewSourceAuthority =
  Authority.authorityCitationImportsNeitherProofNorAuthority
    Authority.canonicalGlobalCausalityAuthorityReceipt

crossPollinationIsRetrospectiveNotHistoricalInfluence : Bool
crossPollinationIsRetrospectiveNotHistoricalInfluence = true

------------------------------------------------------------------------
-- Parent-lineage / source-custody and snowball discipline.
------------------------------------------------------------------------

record CrossPollinationParentLineage : Set where
  constructor crossPollinationParentLineage
  field
    parentPenroseOwner : String
    parentSourceAuthorityOwner : String
    crossPollinationOwner : String
    crossPollinationSupersedesParentAuthority : Bool
    crossPollinationSupersedesParentAuthorityIsFalse :
      crossPollinationSupersedesParentAuthority ≡ false

canonicalCrossPollinationParentLineage : CrossPollinationParentLineage
canonicalCrossPollinationParentLineage = crossPollinationParentLineage
  "DASHI.Physics.Gravity.PenroseGlobalHorismosContradictionExact"
  "DASHI.Physics.Gravity.PenroseGlobalCausalityAuthorityExact"
  "DASHI.Interop.PenroseLocalGlobalHyperfabricCrossPollinationExact"
  false refl

snowballAcquisitionMayProceedOutOfDependencyOrder : Bool
snowballAcquisitionMayProceedOutOfDependencyOrder = true

snowballPaymentMaySkipUnpaidParentDependency : Bool
snowballPaymentMaySkipUnpaidParentDependency = false

crossDomainAnalogyCreatesSourceAuthority : Bool
crossDomainAnalogyCreatesSourceAuthority = false

------------------------------------------------------------------------
-- Downstream candidate map only. No downstream implementation occurs here.
------------------------------------------------------------------------

record DownstreamCrossPollinationCandidate : Set where
  constructor downstreamCrossPollinationCandidate
  field
    domain : String
    candidateConstructiveRole : String
    candidateObstructionRole : String
    implementedInThisTranche : Bool
    implementedInThisTrancheIsFalse : implementedInThisTranche ≡ false

rsaNDimCandidate : DownstreamCrossPollinationCandidate
rsaNDimCandidate = downstreamCrossPollinationCandidate
  "RSA/NDim reducers"
  "requirement closure -> conflict-free compatible reducer family -> global action"
  "projection/quotient validity must not erase unpaid source or lift obligations"
  false refl

flyMaleCNSCandidate : DownstreamCrossPollinationCandidate
flyMaleCNSCandidate = downstreamCrossPollinationCandidate
  "Fly/MaleCNS held-out compatible fibres"
  "training-carrier restriction -> compatible fibre selection -> freeze -> held-out evaluation"
  "held-out or unseen-region failure can obstruct promotion of a local fit to a global explanatory claim"
  false refl

navierStokesCandidate : DownstreamCrossPollinationCandidate
navierStokesCandidate = downstreamCrossPollinationCandidate
  "Navier-Stokes local/global obstruction lanes"
  "local packet/profile estimates -> seam/transport conditions -> candidate global estimate"
  "local/tail control does not automatically pay the global regularity theorem"
  false refl

sensibLawCandidate : DownstreamCrossPollinationCandidate
sensibLawCandidate = downstreamCrossPollinationCandidate
  "SensibLaw evidence/projection authority lanes"
  "source/evidence restriction -> admissibility/compatibility -> typed downstream legal consumer"
  "projection, agreement, or source count does not create legal authority or a court finding"
  false refl

downstreamCandidateMapIsImplementation : Bool
downstreamCandidateMapIsImplementation = false

------------------------------------------------------------------------
-- Exact top-level regression-ready equalities.
------------------------------------------------------------------------

localValidityDoesNotImplyGlobalValidityIsTrue :
  localValidityDoesNotImplyGlobalValidity ≡ true
localValidityDoesNotImplyGlobalValidityIsTrue = refl

projectionValidityDoesNotImplySourceSufficiencyIsTrue :
  projectionValidityDoesNotImplySourceSufficiency ≡ true
projectionValidityDoesNotImplySourceSufficiencyIsTrue = refl

boundedLocalCarrierDoesNotImplyGlobalCompactnessOrClosureIsTrue :
  boundedLocalCarrierDoesNotImplyGlobalCompactnessOrClosure ≡ true
boundedLocalCarrierDoesNotImplyGlobalCompactnessOrClosureIsTrue = refl

sharedProofArchitectureDoesNotIdentifyDomainTheoremsIsTrue :
  sharedProofArchitectureDoesNotIdentifyDomainTheorems ≡ true
sharedProofArchitectureDoesNotIdentifyDomainTheoremsIsTrue = refl

penroseProjectionIsNotParetoAxisProjectionIsTrue :
  penroseProjectionIsNotParetoAxisProjection ≡ true
penroseProjectionIsNotParetoAxisProjectionIsTrue = refl

horismosIsNotHyperfabricGlobalSectionIsTrue :
  horismosIsNotHyperfabricGlobalSection ≡ true
horismosIsNotHyperfabricGlobalSectionIsTrue = refl

graphSeamCompatibilityIsNotLorentzianCompatibilityIsTrue :
  graphSeamCompatibilityIsNotLorentzianCompatibility ≡ true
graphSeamCompatibilityIsNotLorentzianCompatibilityIsTrue = refl

sameObjectReductioRequiresSameObjectIdentityIsTrue :
  sameObjectReductioRequiresSameObjectIdentity ≡ true
sameObjectReductioRequiresSameObjectIdentityIsTrue =
  Penrose.sameHorismosObjectCarriesBothReductioClaimsIsTrue
    Penrose.canonicalPenroseGlobalHorismosBoundary

crossPollinationAddsNoNewSourceAuthorityIsTrue :
  crossPollinationAddsNoNewSourceAuthority ≡ true
crossPollinationAddsNoNewSourceAuthorityIsTrue =
  Authority.authorityCitationImportsNeitherProofNorAuthorityIsTrue
    Authority.canonicalGlobalCausalityAuthorityReceipt

crossPollinationIsRetrospectiveNotHistoricalInfluenceIsTrue :
  crossPollinationIsRetrospectiveNotHistoricalInfluence ≡ true
crossPollinationIsRetrospectiveNotHistoricalInfluenceIsTrue = refl

snowballPaymentMaySkipUnpaidParentDependencyIsFalse :
  snowballPaymentMaySkipUnpaidParentDependency ≡ false
snowballPaymentMaySkipUnpaidParentDependencyIsFalse = refl

crossDomainAnalogyCreatesSourceAuthorityIsFalse :
  crossDomainAnalogyCreatesSourceAuthority ≡ false
crossDomainAnalogyCreatesSourceAuthorityIsFalse = refl

downstreamCandidateMapIsImplementationIsFalse :
  downstreamCandidateMapIsImplementation ≡ false
downstreamCandidateMapIsImplementationIsFalse = refl
