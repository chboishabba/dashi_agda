module DASHI.Culture.RastafariItalCollectiveOptionConeEfficacyExact where

open import DASHI.Core.Prelude

import DASHI.Core.IntersectionalNonFactorability as NonFactor
import DASHI.Culture.RastafariItalExitRefusalMarxUnionCrossPollinationExact as Exit
import DASHI.Governance.OptionConeCoercionExact as Cone
import DASHI.Governance.OppositionInterfaceAntiDomesticationExact as Opposition
import DASHI.Governance.TypedBranchingOptionConeBridgeExact as BranchCone

------------------------------------------------------------------------
-- COLLECTIVE ORGANISATION AS OPTION-CONE TRANSFORMATION
--
-- Union/association presence is not itself efficacy.  Efficacy in this finite
-- comparison requires a proof-bearing widening of the safe option cone:
-- every option available before remains available after, and at least one new
-- option becomes available after organisation.
--
-- This is DASHI mathematics.  It does not claim that every union, bargaining
-- regime or historical labour movement produces such a widening.
------------------------------------------------------------------------

data OrganisationState : Set where
  individualOnly formalAssociation effectiveCollective : OrganisationState

data LabourOption : Set where
  individualRefusal
  collectiveRefusal
  protectedWithdrawal
  collectiveBargainingMove
  ruleChangeProposal
  viableMaterialExit
  : LabourOption

data LabourAvailable : OrganisationState → LabourOption → Set where
  individualRefusalIndividual : LabourAvailable individualOnly individualRefusal

  individualRefusalFormal : LabourAvailable formalAssociation individualRefusal
  collectiveRefusalFormal : LabourAvailable formalAssociation collectiveRefusal

  individualRefusalEffective : LabourAvailable effectiveCollective individualRefusal
  collectiveRefusalEffective : LabourAvailable effectiveCollective collectiveRefusal
  protectedWithdrawalEffective : LabourAvailable effectiveCollective protectedWithdrawal
  bargainingEffective : LabourAvailable effectiveCollective collectiveBargainingMove
  ruleProposalEffective : LabourAvailable effectiveCollective ruleChangeProposal
  viableExitEffective : LabourAvailable effectiveCollective viableMaterialExit

labourOptionCone : Cone.SafeReachabilitySystem OrganisationState LabourOption
labourOptionCone = Cone.safeReachabilitySystem LabourAvailable

------------------------------------------------------------------------
-- Strict expansion is the dual comparison to strict contraction.
------------------------------------------------------------------------

record StrictSafeReachabilityExpansion
    (before after : OrganisationState) : Set₁ where
  constructor strict-safe-reachability-expansion
  field
    beforeIncludedInAfter :
      (option : LabourOption) →
      Cone.Available labourOptionCone before option →
      Cone.Available labourOptionCone after option
    gainedOption : LabourOption
    gainedAfter : Cone.Available labourOptionCone after gainedOption
    gainedBeforeImpossible :
      Cone.Available labourOptionCone before gainedOption → ⊥

open StrictSafeReachabilityExpansion public

formalIncludedInEffective :
  (option : LabourOption) →
  LabourAvailable formalAssociation option →
  LabourAvailable effectiveCollective option
formalIncludedInEffective individualRefusal individualRefusalFormal =
  individualRefusalEffective
formalIncludedInEffective collectiveRefusal collectiveRefusalFormal =
  collectiveRefusalEffective

canonicalEffectiveCollectiveExpansion :
  StrictSafeReachabilityExpansion formalAssociation effectiveCollective
canonicalEffectiveCollectiveExpansion =
  strict-safe-reachability-expansion
    formalIncludedInEffective
    collectiveBargainingMove
    bargainingEffective
    (λ ())

individualIncludedInFormal :
  (option : LabourOption) →
  LabourAvailable individualOnly option →
  LabourAvailable formalAssociation option
individualIncludedInFormal individualRefusal individualRefusalIndividual =
  individualRefusalFormal

canonicalFormalAssociationExpansion :
  StrictSafeReachabilityExpansion individualOnly formalAssociation
canonicalFormalAssociationExpansion =
  strict-safe-reachability-expansion
    individualIncludedInFormal
    collectiveRefusal
    collectiveRefusalFormal
    (λ ())

------------------------------------------------------------------------
-- Union presence cannot recover efficacy.
------------------------------------------------------------------------

data AssociationSurface : Set where
  associationAbsent associationPresent : AssociationSurface

data CollectiveEfficacy : Set where
  nominalCollective effectiveCollectivePower : CollectiveEfficacy

associationSurface : OrganisationState → AssociationSurface
associationSurface individualOnly = associationAbsent
associationSurface formalAssociation = associationPresent
associationSurface effectiveCollective = associationPresent

collectiveEfficacy : OrganisationState → CollectiveEfficacy
collectiveEfficacy individualOnly = nominalCollective
collectiveEfficacy formalAssociation = nominalCollective
collectiveEfficacy effectiveCollective = effectiveCollectivePower

sameAssociationSurface :
  associationSurface formalAssociation ≡ associationSurface effectiveCollective
sameAssociationSurface = refl

efficacyDiffers :
  collectiveEfficacy formalAssociation ≡ collectiveEfficacy effectiveCollective → ⊥
efficacyDiffers ()

associationPresenceCannotRecoverCollectiveEfficacy :
  NonFactor.FactorsThrough associationSurface collectiveEfficacy → ⊥
associationPresenceCannotRecoverCollectiveEfficacy =
  NonFactor.witnessRulesOutEveryFlatFactorisation
    (NonFactor.nonFactorabilityWitness
      formalAssociation effectiveCollective sameAssociationSurface efficacyDiffers)

------------------------------------------------------------------------
-- Existing exit/refusal and opposition boundaries remain in force.
------------------------------------------------------------------------

formalOrganisationStillDoesNotRecoverBargainingPower :
  NonFactor.FactorsThrough Exit.collectiveOrganisation Exit.bargainingPower → ⊥
formalOrganisationStillDoesNotRecoverBargainingPower =
  Exit.organisationCannotRecoverBargainingPower

recognisedLabourOppositionStillDoesNotOwnMetaRule :
  Opposition.CanAlterAdmissionRule Opposition.recognisedOpposition → ⊥
recognisedLabourOppositionStillDoesNotOwnMetaRule =
  Opposition.recognisedOppositionCannotAutomaticallyAlterRule

------------------------------------------------------------------------
-- Cross-pollination with the canonical option-cone comparison discipline.
-- The typed branching owner already states that cone comparison alone does not
-- prove an actual state transition or coercion.  We retain the same boundary
-- for expansion: a comparison of before/after option sets is not by itself an
-- empirical claim that organisation caused the widening.
------------------------------------------------------------------------

typedConeComparisonStillDoesNotClaimActualTransition :
  BranchCone.TypedBranchingOptionConeBoundary.comparisonContractionClaimsActualStateTransition
    BranchCone.canonicalTypedBranchingOptionConeBoundary
  ≡ false
typedConeComparisonStillDoesNotClaimActualTransition = refl

------------------------------------------------------------------------
-- No-promotions.
------------------------------------------------------------------------

data UnionPresenceMeansOptionConeExpansion : Set where

data OptionConeExpansionProvesCausalUnionEffect : Set where

data CollectiveRefusalMeansViableExit : Set where

data BargainingOptionMeansMetaRuleAuthority : Set where

data RuleProposalMeansGoverningAuthority : Set where

unionPresenceDoesNotProveOptionConeExpansion :
  UnionPresenceMeansOptionConeExpansion → ⊥
unionPresenceDoesNotProveOptionConeExpansion ()

optionConeExpansionDoesNotProveCausalUnionEffect :
  OptionConeExpansionProvesCausalUnionEffect → ⊥
optionConeExpansionDoesNotProveCausalUnionEffect ()

collectiveRefusalDoesNotProveViableExit :
  CollectiveRefusalMeansViableExit → ⊥
collectiveRefusalDoesNotProveViableExit ()

bargainingOptionDoesNotProveMetaRuleAuthority :
  BargainingOptionMeansMetaRuleAuthority → ⊥
bargainingOptionDoesNotProveMetaRuleAuthority ()

ruleProposalDoesNotProveGoverningAuthority :
  RuleProposalMeansGoverningAuthority → ⊥
ruleProposalDoesNotProveGoverningAuthority ()

record ItalCollectiveOptionConeEfficacyBoundary : Set where
  constructor ital-collective-option-cone-efficacy-boundary
  field
    associationPresenceEqualsEfficacy : Bool
    associationPresenceEqualsEfficacyIsFalse :
      associationPresenceEqualsEfficacy ≡ false
    effectiveOrganisationRequiresReachabilityEvidence : Bool
    effectiveOrganisationRequiresReachabilityEvidenceIsTrue :
      effectiveOrganisationRequiresReachabilityEvidence ≡ true
    optionExpansionAloneProvesHistoricalCause : Bool
    optionExpansionAloneProvesHistoricalCauseIsFalse :
      optionExpansionAloneProvesHistoricalCause ≡ false
    bargainingEqualsMetaRulePower : Bool
    bargainingEqualsMetaRulePowerIsFalse : bargainingEqualsMetaRulePower ≡ false

canonicalItalCollectiveOptionConeEfficacyBoundary :
  ItalCollectiveOptionConeEfficacyBoundary
canonicalItalCollectiveOptionConeEfficacyBoundary =
  ital-collective-option-cone-efficacy-boundary
    false refl true refl false refl false refl
