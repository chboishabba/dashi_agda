module DASHI.Governance.SituatedDissentDeceptionAssayExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.CriticalSocialEcologyObserverRegimeExact as Ecology
import DASHI.Core.HistoryQualifiedSelectionTopologyExact as Selection

------------------------------------------------------------------------
-- SITUATED DISSENT / DECEPTION ASSAYS
--
-- This module does not define a substantive moral theory and does not claim
-- that every influence is coercion or deception.  It supplies finite adversarial
-- fixtures for governance consumers that would otherwise collapse:
--
--   approval surface != decision integrity
--   formal option       != effective option cone
--   dissent recorded    != dissent causally effective
--   direct permission   != complete reachable-effect closure
--   many approvals      != independent approval fibres
--   current sincere choice != unmanipulated formation trajectory
--
-- The fixtures are synthetic DASHI theorem objects.  Dark-pattern, command,
-- whistleblowing, AI-human, institutional and consumer-interface examples are
-- application/source-calibration domains rather than theorem authority.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Approval can collide while evidence / option / pressure integrity differs.
------------------------------------------------------------------------

data ApprovalState : Set where
  informedApproval manipulatedApproval : ApprovalState

data ApprovalSurface : Set where
  approved : ApprovalSurface

data EvidenceIntegrity : Set where
  truthfulEvidence deceptiveEvidence : EvidenceIntegrity

data OptionConeIntegrity : Set where
  openOptionCone deformedOptionCone : OptionConeIntegrity

data PressureIntegrity : Set where
  noncoercivePressure manipulativePressure : PressureIntegrity

data DecisionIntegrity : Set where
  integrityAdequate integrityCompromised : DecisionIntegrity

approvalSurface : ApprovalState → ApprovalSurface
approvalSurface _ = approved

evidenceIntegrity : ApprovalState → EvidenceIntegrity
evidenceIntegrity informedApproval = truthfulEvidence
evidenceIntegrity manipulatedApproval = deceptiveEvidence

optionConeIntegrity : ApprovalState → OptionConeIntegrity
optionConeIntegrity informedApproval = openOptionCone
optionConeIntegrity manipulatedApproval = deformedOptionCone

pressureIntegrity : ApprovalState → PressureIntegrity
pressureIntegrity informedApproval = noncoercivePressure
pressureIntegrity manipulatedApproval = manipulativePressure

decisionIntegrity : ApprovalState → DecisionIntegrity
decisionIntegrity informedApproval = integrityAdequate
decisionIntegrity manipulatedApproval = integrityCompromised

sameApprovalSurface :
  approvalSurface informedApproval ≡ approvalSurface manipulatedApproval
sameApprovalSurface = refl

approvalIntegrityDiffers :
  decisionIntegrity informedApproval ≡ decisionIntegrity manipulatedApproval → ⊥
approvalIntegrityDiffers ()

approvalIntegrityWitness :
  INF.NonFactorabilityWitness approvalSurface decisionIntegrity
approvalIntegrityWitness =
  INF.nonFactorabilityWitness
    informedApproval
    manipulatedApproval
    sameApprovalSurface
    approvalIntegrityDiffers

approvalCannotRecoverDecisionIntegrity :
  INF.FactorsThrough approvalSurface decisionIntegrity → ⊥
approvalCannotRecoverDecisionIntegrity =
  INF.witnessRulesOutEveryFlatFactorisation approvalIntegrityWitness

------------------------------------------------------------------------
-- Dark-pattern-style asymmetric friction: both formal options exist, but the
-- realised refusal affordance differs.  This is the governance analogue of the
-- existing inclusive-rhetoric != realised-accessibility theorem.
------------------------------------------------------------------------

data InterfaceState : Set where
  symmetricChoice asymmetricChoice : InterfaceState

data FormalOptions : Set where
  acceptAndRefusePresent : FormalOptions

data RefusalAffordance : Set where
  refusalReachable refusalFrictional : RefusalAffordance

formalOptions : InterfaceState → FormalOptions
formalOptions _ = acceptAndRefusePresent

refusalAffordance : InterfaceState → RefusalAffordance
refusalAffordance symmetricChoice = refusalReachable
refusalAffordance asymmetricChoice = refusalFrictional

sameFormalOptions :
  formalOptions symmetricChoice ≡ formalOptions asymmetricChoice
sameFormalOptions = refl

refusalAffordanceDiffers :
  refusalAffordance symmetricChoice ≡ refusalAffordance asymmetricChoice → ⊥
refusalAffordanceDiffers ()

formalOptionsCannotRecoverRefusalAffordance :
  INF.FactorsThrough formalOptions refusalAffordance → ⊥
formalOptionsCannotRecoverRefusalAffordance =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      symmetricChoice
      asymmetricChoice
      sameFormalOptions
      refusalAffordanceDiffers)

------------------------------------------------------------------------
-- Dissent may be symbolically/procedurally visible while materially ineffective.
------------------------------------------------------------------------

data DissentState : Set where
  protectedEffectiveDissent managedDecorativeDissent : DissentState

data DissentSurface : Set where
  dissentRecorded : DissentSurface

data DissentEffect : Set where
  transitionBlocked transitionUnchanged : DissentEffect

data DissentProtection : Set where
  retaliationProtected retaliationExposed : DissentProtection

recordedDissent : DissentState → DissentSurface
recordedDissent _ = dissentRecorded

dissentEffect : DissentState → DissentEffect
dissentEffect protectedEffectiveDissent = transitionBlocked
dissentEffect managedDecorativeDissent = transitionUnchanged

dissentProtection : DissentState → DissentProtection
dissentProtection protectedEffectiveDissent = retaliationProtected
dissentProtection managedDecorativeDissent = retaliationExposed

sameDissentSurface :
  recordedDissent protectedEffectiveDissent
  ≡ recordedDissent managedDecorativeDissent
sameDissentSurface = refl

dissentEffectDiffers :
  dissentEffect protectedEffectiveDissent
  ≡ dissentEffect managedDecorativeDissent → ⊥
dissentEffectDiffers ()

recordedDissentCannotRecoverEffectiveVeto :
  INF.FactorsThrough recordedDissent dissentEffect → ⊥
recordedDissentCannotRecoverEffectiveVeto =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      protectedEffectiveDissent
      managedDecorativeDissent
      sameDissentSurface
      dissentEffectDiffers)

------------------------------------------------------------------------
-- Human mediation can be an actuation route even when direct permission is
-- identically denied.  This is a reachable-effect assay, not a universal causal
-- claim about persuasion.
------------------------------------------------------------------------

data MediationState : Set where
  directDeniedNoProxy directDeniedHumanProxy : MediationState

data DirectPermission : Set where
  directDenied : DirectPermission

data ReachableEffect : Set where
  effectUnreachable effectHumanMediated : ReachableEffect

permissionSurface : MediationState → DirectPermission
permissionSurface _ = directDenied

reachableEffect : MediationState → ReachableEffect
reachableEffect directDeniedNoProxy = effectUnreachable
reachableEffect directDeniedHumanProxy = effectHumanMediated

sameDirectPermission :
  permissionSurface directDeniedNoProxy
  ≡ permissionSurface directDeniedHumanProxy
sameDirectPermission = refl

reachableEffectDiffers :
  reachableEffect directDeniedNoProxy
  ≡ reachableEffect directDeniedHumanProxy → ⊥
reachableEffectDiffers ()

directPermissionCannotRecoverReachableEffect :
  INF.FactorsThrough permissionSurface reachableEffect → ⊥
directPermissionCannotRecoverReachableEffect =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      directDeniedNoProxy
      directDeniedHumanProxy
      sameDirectPermission
      reachableEffectDiffers)

------------------------------------------------------------------------
-- Synthetic consensus: approval count can be fixed while independence differs.
------------------------------------------------------------------------

data ConsensusState : Set where
  independentApprovals sharedSourceApprovals : ConsensusState

data ApprovalCount : Set where
  threeApprovals : ApprovalCount

data IndependenceClass : Set where
  independentFibres commonSourceFibre : IndependenceClass

approvalCount : ConsensusState → ApprovalCount
approvalCount _ = threeApprovals

independenceClass : ConsensusState → IndependenceClass
independenceClass independentApprovals = independentFibres
independenceClass sharedSourceApprovals = commonSourceFibre

sameApprovalCount :
  approvalCount independentApprovals ≡ approvalCount sharedSourceApprovals
sameApprovalCount = refl

independenceDiffers :
  independenceClass independentApprovals
  ≡ independenceClass sharedSourceApprovals → ⊥
independenceDiffers ()

approvalCountCannotRecoverIndependence :
  INF.FactorsThrough approvalCount independenceClass → ⊥
approvalCountCannotRecoverIndependence =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      independentApprovals
      sharedSourceApprovals
      sameApprovalCount
      independenceDiffers)

------------------------------------------------------------------------
-- Formation trajectory: sincere current endorsement does not recover whether
-- the option cone was progressively narrowed.  Social formation is not thereby
-- equated with coercion; the finite witness separates two possible histories.
------------------------------------------------------------------------

data FormationState : Set where
  revisablyEndorsed progressivelyNarrowed : FormationState

data CurrentEndorsement : Set where
  sincereYes : CurrentEndorsement

data FormationIntegrity : Set where
  revisableFormation narrowedFormation : FormationIntegrity

currentEndorsement : FormationState → CurrentEndorsement
currentEndorsement _ = sincereYes

formationIntegrity : FormationState → FormationIntegrity
formationIntegrity revisablyEndorsed = revisableFormation
formationIntegrity progressivelyNarrowed = narrowedFormation

sameSincereEndorsement :
  currentEndorsement revisablyEndorsed
  ≡ currentEndorsement progressivelyNarrowed
sameSincereEndorsement = refl

formationIntegrityDiffers :
  formationIntegrity revisablyEndorsed
  ≡ formationIntegrity progressivelyNarrowed → ⊥
formationIntegrityDiffers ()

currentEndorsementCannotRecoverFormationIntegrity :
  INF.FactorsThrough currentEndorsement formationIntegrity → ⊥
currentEndorsementCannotRecoverFormationIntegrity =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      revisablyEndorsed
      progressivelyNarrowed
      sameSincereEndorsement
      formationIntegrityDiffers)

------------------------------------------------------------------------
-- Existing-owner welds: these constants force the assay to consume, rather
-- than duplicate, the canonical realised-affordance and selection boundaries.
------------------------------------------------------------------------

socialEcologyBoundary : Ecology.ObserverRegimeBoundary
socialEcologyBoundary = Ecology.canonicalObserverRegimeBoundary

selectionBoundary : Selection.HistoryQualifiedSelectionBoundary
selectionBoundary = Selection.canonicalHistoryQualifiedSelectionBoundary

------------------------------------------------------------------------
-- Scope boundary.
------------------------------------------------------------------------

record SituatedDissentDeceptionBoundary : Set where
  constructor situated-dissent-deception-boundary
  field
    approvalEqualsDecisionIntegrity : Bool
    approvalEqualsDecisionIntegrityIsFalse :
      approvalEqualsDecisionIntegrity ≡ false
    formalRefusalEqualsEffectiveRefusal : Bool
    formalRefusalEqualsEffectiveRefusalIsFalse :
      formalRefusalEqualsEffectiveRefusal ≡ false
    recordedDissentEqualsEffectiveVeto : Bool
    recordedDissentEqualsEffectiveVetoIsFalse :
      recordedDissentEqualsEffectiveVeto ≡ false
    directDenialClosesEveryIndirectRoute : Bool
    directDenialClosesEveryIndirectRouteIsFalse :
      directDenialClosesEveryIndirectRoute ≡ false
    approvalCountProvesIndependence : Bool
    approvalCountProvesIndependenceIsFalse :
      approvalCountProvesIndependence ≡ false
    sincereCurrentChoiceProvesUnmanipulatedHistory : Bool
    sincereCurrentChoiceProvesUnmanipulatedHistoryIsFalse :
      sincereCurrentChoiceProvesUnmanipulatedHistory ≡ false
    everySocialInfluenceIsCoercion : Bool
    everySocialInfluenceIsCoercionIsFalse :
      everySocialInfluenceIsCoercion ≡ false
    finiteAssaySettlesSubstantiveMorality : Bool
    finiteAssaySettlesSubstantiveMoralityIsFalse :
      finiteAssaySettlesSubstantiveMorality ≡ false

canonicalSituatedDissentDeceptionBoundary : SituatedDissentDeceptionBoundary
canonicalSituatedDissentDeceptionBoundary =
  situated-dissent-deception-boundary
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
