module DASHI.Governance.TransitionResidual where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Algebra.TetralemmaBridge as Tetralemma
import DASHI.Biology.RelationalQiEducationTraumaBridge as Relational
import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Foundations.StageValuationBundleAtlas as Stage
import DASHI.Interop.ResidualBoundaryCore as Residual

------------------------------------------------------------------------
-- Constitutional chart / residual / +1 transition machine.
--
-- The existing chart -> residual -> +1 topology is reused as a structural
-- grammar only.  A constitutional transition is not validated by its stage
-- label, by formal elegance, or by this repository.
------------------------------------------------------------------------

governanceTopologySignature : List Relational.TopologyNode
governanceTopologySignature =
  Relational.canonicalTopologySignature

governanceTopologyIsChartResidualPlusOne :
  governanceTopologySignature
  ≡ Relational.canonicalTopologySignature
governanceTopologyIsChartResidualPlusOne = refl

data TransitionalPhase : Set where
  coupOrder : TransitionalPhase
  prefigurativeOrganisation : TransitionalPhase
  temporaryRevolutionaryAuthority : TransitionalPhase
  constitutedTransitionalAuthority : TransitionalPhase
  constitutionalReconstruction : TransitionalPhase
  democraticClosure : TransitionalPhase

data AdmissibleTransition :
  TransitionalPhase →
  TransitionalPhase →
  Set where

  organiseBeforeTransfer :
    AdmissibleTransition
      coupOrder
      prefigurativeOrganisation

  transferToTemporaryCivilianOrder :
    AdmissibleTransition
      prefigurativeOrganisation
      temporaryRevolutionaryAuthority

  constituteTransitionalCouncils :
    AdmissibleTransition
      temporaryRevolutionaryAuthority
      constitutedTransitionalAuthority

  beginConstitutionMaking :
    AdmissibleTransition
      constitutedTransitionalAuthority
      constitutionalReconstruction

  closeThroughElection :
    AdmissibleTransition
      constitutionalReconstruction
      democraticClosure

------------------------------------------------------------------------
-- Four-way governance validation.
--
-- This is role-sensitive validation, not a claim of equivalence with the
-- historical catuskoti.  The imported tetralemma bridge remains a formal
-- alignment carrier only.
------------------------------------------------------------------------

data GovernanceValidation : Set where
  satisfied : GovernanceValidation
  positivelyViolated : GovernanceValidation
  undeterminedAxisIncomplete : GovernanceValidation
  inapplicableToRole : GovernanceValidation

validationResidual :
  GovernanceValidation →
  Residual.BoundaryResidual
validationResidual satisfied = Residual.exact
validationResidual positivelyViolated = Residual.contradiction
validationResidual undeterminedAxisIncomplete = Residual.partial
validationResidual inapplicableToRole = Residual.noTypedMeet

validationTetralemmaPosition :
  GovernanceValidation →
  Tetralemma.TetralemmaPosition
validationTetralemmaPosition satisfied = Tetralemma.affirmation
validationTetralemmaPosition positivelyViolated = Tetralemma.negation
validationTetralemmaPosition undeterminedAxisIncomplete = Tetralemma.both
validationTetralemmaPosition inapplicableToRole = Tetralemma.neither

satisfiedMapsToExact :
  validationResidual satisfied ≡ Residual.exact
satisfiedMapsToExact = refl

positiveViolationMapsToContradiction :
  validationResidual positivelyViolated ≡ Residual.contradiction
positiveViolationMapsToContradiction = refl

incompleteAxisMapsToPartial :
  validationResidual undeterminedAxisIncomplete ≡ Residual.partial
incompleteAxisMapsToPartial = refl

inapplicableMapsToNoTypedMeet :
  validationResidual inapplicableToRole ≡ Residual.noTypedMeet
inapplicableMapsToNoTypedMeet = refl

record InstitutionalChart : Set where
  constructor institutionalChart
  field
    chartLabel : String
    actorSurface : String
    institutionSurface : String
    resourceSurface : String
    relationSurface : String
    phase : TransitionalPhase

open InstitutionalChart public

data ConstitutionalInvariant : Set where
  civilianSupremacyInvariant : ConstitutionalInvariant
  equalCitizenshipInvariant : ConstitutionalInvariant
  rightsInvariant : ConstitutionalInvariant
  publicRevenueUnityInvariant : ConstitutionalInvariant
  affectedConstituencyInclusionInvariant : ConstitutionalInvariant
  extraordinaryPowerTimeBoundInvariant : ConstitutionalInvariant
  justiceAndReviewInvariant : ConstitutionalInvariant

record ConstitutionalResidual
  (chart : InstitutionalChart) : Set where
  constructor constitutionalResidual
  field
    invariant : ConstitutionalInvariant
    validation : GovernanceValidation
    residual : Residual.BoundaryResidual
    residualIsCanonical : residual ≡ validationResidual validation
    affectedAxisSummary : String
    affectedConstituencySummary : String
    residualPromotesTruth : Bool
    residualPromotesTruthIsFalse : residualPromotesTruth ≡ false

open ConstitutionalResidual public

mkConstitutionalResidual :
  ∀ {chart} →
  ConstitutionalInvariant →
  GovernanceValidation →
  String →
  String →
  ConstitutionalResidual chart
mkConstitutionalResidual invariantValue validationValue axes constituencies =
  constitutionalResidual
    invariantValue
    validationValue
    (validationResidual validationValue)
    refl
    axes
    constituencies
    false
    refl

record ConstitutionalPlusOne
  {before after : TransitionalPhase}
  (edge : AdmissibleTransition before after)
  (chart : InstitutionalChart) : Set where
  constructor constitutionalPlusOne
  field
    nextChart : InstitutionalChart
    sourcePhaseMatches : phase chart ≡ before
    targetPhaseMatches : phase nextChart ≡ after
    repairedResidual : ConstitutionalResidual chart
    unresolvedResidualsRetained : Bool
    unresolvedResidualsRetainedIsTrue :
      unresolvedResidualsRetained ≡ true
    previouslySatisfiedInvariantsPreserved : Bool
    previouslySatisfiedInvariantsPreservedIsTrue :
      previouslySatisfiedInvariantsPreserved ≡ true
    authorityPromotedByFormalStep : Bool
    authorityPromotedByFormalStepIsFalse :
      authorityPromotedByFormalStep ≡ false

open ConstitutionalPlusOne public

canonicalCoupChart : InstitutionalChart
canonicalCoupChart =
  institutionalChart
    "coup-order institutional chart"
    "armed command and fragmented civilian constituencies"
    "military/security-dominated public institutions"
    "off-budget and contested public resources"
    "coercive command relation"
    coupOrder

canonicalPrefigurativeChart : InstitutionalChart
canonicalPrefigurativeChart =
  institutionalChart
    "prefigurative organisation chart"
    "situated constituencies and recallable delegates"
    "local and revolutionary councils"
    "public-resource claims under audit"
    "upward delegation and downward accountability"
    prefigurativeOrganisation

canonicalForceResidual : ConstitutionalResidual canonicalCoupChart
canonicalForceResidual =
  mkConstitutionalResidual
    civilianSupremacyInvariant
    positivelyViolated
    "armed-power, institution and coloniality axes"
    "all constituencies subject to coercive command"

canonicalOrganisationPlusOne :
  ConstitutionalPlusOne
    organiseBeforeTransfer
    canonicalCoupChart
canonicalOrganisationPlusOne =
  constitutionalPlusOne
    canonicalPrefigurativeChart
    refl
    refl
    canonicalForceResidual
    true
    refl
    true
    refl
    false
    refl

stageCompressionDoesNotPromoteAuthority :
  Stage.semanticAuthorityPromoted Stage.canonicalTransformativeJump3To14
  ≡ false
stageCompressionDoesNotPromoteAuthority = refl

record TransitionAuthorityBoundary : Set where
  constructor transitionAuthorityBoundary
  field
    chartResidualPlusOneGrammarPresent : Bool
    stageNumberAloneAuthorisesTransition : Bool
    unresolvedResidualsMayBeErased : Bool
    formalTransitionCreatesLegitimacy : Bool
    rightsAndCivilianInvariantsRequired : Bool
    tetralemmaHistoricalEquivalenceClaimed : Bool

canonicalTransitionAuthorityBoundary : TransitionAuthorityBoundary
canonicalTransitionAuthorityBoundary =
  transitionAuthorityBoundary
    true
    false
    false
    false
    true
    false

canonicalTransitionResidualReceipt :
  GenericReceipt.GenericReceipt
canonicalTransitionResidualReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "constitutional chart residual plus-one machine"
    "DASHI.Governance.TransitionResidual"
    "canonicalOrganisationPlusOne"
    "reuses chart/residual/+1, residual-boundary, tetralemma and guarded-stage carriers to type a rights-preserving transition with retained unresolved residuals"
    "the carrier does not establish historical necessity, practical success, constitutional validity or popular legitimacy"
    "agda -i . DASHI/Governance/TransitionResidual.agda"
