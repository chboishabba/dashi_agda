module DASHI.Core.GenderedApprovalObjectiveRechartExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (trans; sym)

import DASHI.Core.GenderedNormApprovalIndependenceExact as Approval
import DASHI.Core.IrigarayLabialRelationalCarrierExact as Irigaray
import DASHI.Core.LacanIrigarayTernaryGrammarBridgeExact as LI
import DASHI.Core.TernaryRoleCarrierExact as Ternary
import DASHI.Reasoning.LacanSignifierSubjectCore as Lacan
import DASHI.Reasoning.LacanFantasyDriveCore as Fantasy

------------------------------------------------------------------------
-- DYNAMIC APPROVAL-OBJECTIVE RECHART
--
-- The source phrase "stop optimizing for approval" is formalised here as a
-- change in the objective/observer used to select conduct.  This is not
-- identified with hostility, meanness, social withdrawal, elimination of
-- sanctions, elimination of desire, or escape from symbolic structure.
--
-- Lacan cross-pollination:
--   approval can occupy a symbolic/supposed-authority coordinate without
--   becoming verified authority or a final object that terminates desire.
--
-- Irigaray cross-pollination:
--   a relational chart need not be One-centred; reciprocal relation can be
--   retained without making one endpoint the master evaluation centre.
------------------------------------------------------------------------

data Conduct : Set where
  approvalConformingConduct : Conduct
  nonApprovalConformingConduct : Conduct

data Objective : Set where
  approvalIndexedObjective : Objective
  declaredCriterionObjective : Objective

data ApprovalSignal : Set where
  approvedSignal : ApprovalSignal
  disapprovedSignal : ApprovalSignal

data DeclaredCriterionSignal : Set where
  criterionMet : DeclaredCriterionSignal
  criterionMissed : DeclaredCriterionSignal

approvalSignal : Conduct → ApprovalSignal
approvalSignal approvalConformingConduct = approvedSignal
approvalSignal nonApprovalConformingConduct = disapprovedSignal

declaredCriterionSignal : Conduct → DeclaredCriterionSignal
declaredCriterionSignal approvalConformingConduct = criterionMissed
declaredCriterionSignal nonApprovalConformingConduct = criterionMet

data Choice : Set where
  chooseApprovalConforming : Choice
  chooseNonApprovalConforming : Choice

chooseByObjective : Objective → Choice
chooseByObjective approvalIndexedObjective = chooseApprovalConforming
chooseByObjective declaredCriterionObjective = chooseNonApprovalConforming

objectiveRechartChangesSelectedConduct :
  chooseByObjective approvalIndexedObjective
    ≡ chooseByObjective declaredCriterionObjective → ⊥
objectiveRechartChangesSelectedConduct ()

------------------------------------------------------------------------
-- Loss of approval dependence is distinct from disappearance of constraint.
------------------------------------------------------------------------

data ConstraintWorld : Set where
  sameObjectiveLowSanction : ConstraintWorld
  sameObjectiveHighSanction : ConstraintWorld

data ObjectiveSurface : Set where
  sameDeclaredObjective : ObjectiveSurface

data SanctionAnswer : Set where
  lowerExternalSanction : SanctionAnswer
  higherExternalSanction : SanctionAnswer

objectiveSurface : ConstraintWorld → ObjectiveSurface
objectiveSurface world = sameDeclaredObjective

sanctionAnswer : ConstraintWorld → SanctionAnswer
sanctionAnswer sameObjectiveLowSanction = lowerExternalSanction
sanctionAnswer sameObjectiveHighSanction = higherExternalSanction

objectiveDoesNotDetermineSanction :
  (coarse : ObjectiveSurface → SanctionAnswer) →
  ((world : ConstraintWorld) →
    sanctionAnswer world ≡ coarse (objectiveSurface world)) →
  ⊥
objectiveDoesNotDetermineSanction coarse factor =
  let
    left = factor sameObjectiveLowSanction
    right = factor sameObjectiveHighSanction
  in
  (λ ()) (trans left (sym right))

------------------------------------------------------------------------
-- Lacanian boundary reuse.
------------------------------------------------------------------------

supposedApprovalAuthorityIsNotVerifiedAuthority :
  Lacan.supposedAuthority ≡ Lacan.verifiedAuthority → ⊥
supposedApprovalAuthorityIsNotVerifiedAuthority =
  Lacan.supposedAuthorityIsNotVerified

desireNeedNotTerminateAtApproval :
  Fantasy.desireFinalObjectGuaranteed
    Fantasy.canonicalLacanFantasyDriveAuthorityBoundary ≡ false
desireNeedNotTerminateAtApproval = refl

bigOtherIsNotLiteralOmniscientApprover :
  Lacan.bigOtherIsOmniscientPerson
    Lacan.canonicalLacanSignifierSubjectAuthorityBoundary ≡ false
bigOtherIsNotLiteralOmniscientApprover = refl

------------------------------------------------------------------------
-- Irigarayan rechart: retaining relation without a sovereign evaluation
-- centre.  We import the already-paid theorem that no ternary relabelling
-- identifies Lacan's One-centred graph with Irigaray's reciprocal grammar.
------------------------------------------------------------------------

noRelabellingCollapsesReciprocalGrammarIntoOneCentredGrammar :
  (permutation : Ternary.TernaryPermutation) →
  LI.GrammarPreserving permutation → ⊥
noRelabellingCollapsesReciprocalGrammarIntoOneCentredGrammar =
  LI.noTernaryRelabellingPreservesGrammar

reciprocalContactDoesNotDetermineUniqueHierarchy :
  Irigaray.reciprocalContactDeterminesUniqueActivePassiveOrientation
    Irigaray.canonicalIrigarayLabialBoundary ≡ false
reciprocalContactDoesNotDetermineUniqueHierarchy = refl

------------------------------------------------------------------------
-- Non-promotion boundary.
------------------------------------------------------------------------

record ApprovalObjectiveRechartBoundary : Set where
  constructor approvalObjectiveRechartBoundary
  field
    objectiveChangeEqualsMeanness : Bool
    approvalIndependenceEliminatesExternalSanction : Bool
    approvalIndependenceEliminatesDesire : Bool
    approvalIndependenceEliminatesSymbolicStructure : Bool
    disapprovalAutomaticallyMeansCriterionFailure : Bool
    approvalAutomaticallyMeansCriterionSuccess : Bool
    reciprocalRelationRequiresSovereignEvaluator : Bool
    rechartCanChangeSelectedConduct : Bool
    relationCanPersistWithoutOneCentredApprovalObjective : Bool
    empiricalPowerEffectRequiresEvidence : Bool

open ApprovalObjectiveRechartBoundary public

canonicalApprovalObjectiveRechartBoundary : ApprovalObjectiveRechartBoundary
canonicalApprovalObjectiveRechartBoundary =
  approvalObjectiveRechartBoundary
    false
    false
    false
    false
    false
    false
    false
    true
    true
    true
