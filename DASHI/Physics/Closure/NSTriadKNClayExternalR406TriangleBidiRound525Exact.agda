module DASHI.Physics.Closure.NSTriadKNClayExternalR406TriangleBidiRound525Exact where

------------------------------------------------------------------------
-- ROUND525 / TRIANGULAR BIDI: EXTERNAL FORCED PROBLEM <-> CLAY C/D <-> R406
--
-- R522 aligned the external smooth-forced program with DASHI's live forcing
-- quantifier. R524 aligned that external program with the source-exact Clay
-- breakdown alternatives C/D. This owner closes the triangle and uses the Clay
-- consumer to refine the formulation produced by R522.
--
-- The resulting comparison has THREE independent coordinate families:
--
--   E: external-construction coordinates
--      (literal forcing identity, construction domain, claimed breakdown mode)
--
--   C: Clay-admissibility coordinates
--      (domain, positive viscosity, source initial/forcing class,
--       exact NS equation, no-global-solution consumer)
--
--   D: DASHI analytic coordinates
--      (literal R406 carrier, signed forcing-budget membership,
--       theorem quantifier scope, candidate signed-cross estimate)
--
-- No edge may skip the middle coordinate it is meant to transport.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Physics.Closure.NSTriadKNForcedBlowupR406BidiRound522Exact as R522
import DASHI.Physics.Closure.NSTriadKNClayForcedBreakdownFormulationRound523Exact as R523
import DASHI.Physics.Closure.NSTriadKNBuckmasterToClayBreakdownBidiRound524Exact as R524
import DASHI.Physics.Closure.NSTriadKNLiteralR406ClayTerminalCutsetRound504Exact as R504

------------------------------------------------------------------------
-- Three-way typed coordinates.
------------------------------------------------------------------------

data TriangleCoordinate525 : Set where
  externalLiteralForcingIdentity525 : TriangleCoordinate525
  externalDomainAndBreakdownIdentity525 : TriangleCoordinate525
  claySourceAdmissibility525 : TriangleCoordinate525
  clayNoGlobalSolutionWeld525 : TriangleCoordinate525
  dashiSignedBudgetMembership525 : TriangleCoordinate525
  dashiR406QuantifierScope525 : TriangleCoordinate525
  dashiLiteralR406Estimate525 : TriangleCoordinate525

data TriangleRoute525 : Set where
  externalToClay525 : TriangleRoute525
  clayToExternal525 : TriangleRoute525
  clayToDashi525 : TriangleRoute525
  dashiToClay525 : TriangleRoute525
  externalToDashiViaClay525 : TriangleRoute525
  dashiToExternalViaClay525 : TriangleRoute525

data TriangleProducer525 : Set where
  externalCarrierInspection525 : TriangleProducer525
  clayCoordinateAudit525 : TriangleProducer525
  noGlobalSolutionCompilerAudit525 : TriangleProducer525
  signedBudgetMembershipAudit525 : TriangleProducer525
  r406QuantifierAudit525 : TriangleProducer525
  literalR406AdversarialTest525 : TriangleProducer525

record TriangleDemand525 : Set where
  constructor triangle-demand-525
  field
    route525 : TriangleRoute525
    coordinate525 : TriangleCoordinate525
    producer525 : TriangleProducer525

open TriangleDemand525 public

------------------------------------------------------------------------
-- Use Clay C/D to refine the formulation obtained in R522.
--
-- R522's first external-facing demand was literal forcing instantiation.  R524
-- shows that the same construction must ALSO be source-aligned to C or D before
-- it can count as a Clay-facing adversary.  Therefore the refined formulation
-- is not merely
--
--   forcing -> signed-budget membership.
--
-- It is
--
--   forcing
--     -> exact domain/breakdown identity
--     -> Clay admissibility
--     -> signed-budget membership
--     -> R406 quantifier/test.
------------------------------------------------------------------------

refinedExternalToDashiFirst525 : TriangleDemand525
refinedExternalToDashiFirst525 =
  triangle-demand-525
    externalToDashiViaClay525
    externalLiteralForcingIdentity525
    externalCarrierInspection525

refinedExternalToDashiSecond525 : TriangleDemand525
refinedExternalToDashiSecond525 =
  triangle-demand-525
    externalToDashiViaClay525
    externalDomainAndBreakdownIdentity525
    externalCarrierInspection525

refinedExternalToDashiThird525 : TriangleDemand525
refinedExternalToDashiThird525 =
  triangle-demand-525
    externalToDashiViaClay525
    claySourceAdmissibility525
    clayCoordinateAudit525

refinedExternalToDashiFourth525 : TriangleDemand525
refinedExternalToDashiFourth525 =
  triangle-demand-525
    externalToDashiViaClay525
    dashiSignedBudgetMembership525
    signedBudgetMembershipAudit525

refinedExternalToDashiFifth525 : TriangleDemand525
refinedExternalToDashiFifth525 =
  triangle-demand-525
    externalToDashiViaClay525
    dashiR406QuantifierScope525
    r406QuantifierAudit525

refinedExternalToDashiIfInClass525 : TriangleDemand525
refinedExternalToDashiIfInClass525 =
  triangle-demand-525
    externalToDashiViaClay525
    dashiLiteralR406Estimate525
    literalR406AdversarialTest525

------------------------------------------------------------------------
-- Reverse formulation: DASHI -> Clay -> external.
--
-- A candidate R406 theorem must first expose its exact forcing quantifier. Clay
-- then asks whether that quantified forcing class contains the exact C/D source
-- class. Only after this inclusion is established may the external construction
-- serve as an in-class counterexample/falsification fixture.
------------------------------------------------------------------------

data ForcingClassRelation525 : Set where
  clayClassInsideDashiClass525 : ForcingClassRelation525
  externalClassOutsideDashiClass525 : ForcingClassRelation525
  classRelationUnresolved525 : ForcingClassRelation525

data ReverseOutcome525 : Set where
  inClassAdversarialTest525 : ReverseOutcome525
  explicitSeparatingHypothesis525 : ReverseOutcome525
  needClassInclusionProof525 : ReverseOutcome525

reverseOutcomeFor525 : ForcingClassRelation525 → ReverseOutcome525
reverseOutcomeFor525 clayClassInsideDashiClass525 = inClassAdversarialTest525
reverseOutcomeFor525 externalClassOutsideDashiClass525 = explicitSeparatingHypothesis525
reverseOutcomeFor525 classRelationUnresolved525 = needClassInclusionProof525

currentReverseRelation525 : ForcingClassRelation525
currentReverseRelation525 = classRelationUnresolved525

currentReverseOutcome525 : ReverseOutcome525
currentReverseOutcome525 = reverseOutcomeFor525 currentReverseRelation525

currentReverseOutcomeNeedsClassInclusion525 :
  currentReverseOutcome525 ≡ needClassInclusionProof525
currentReverseOutcomeNeedsClassInclusion525 = refl

------------------------------------------------------------------------
-- Introspective collision: signed-budget membership alone is not enough to
-- determine Clay relevance. Two forcings can be equally inside DASHI's analytic
-- budget class while only one satisfies the exact C/D source class.
------------------------------------------------------------------------

data DashiBudgetObservation525 : Set where
  observedInsideSignedBudget525 : DashiBudgetObservation525

data ClayAdmissibilityAnswer525 : Set where
  clayAdmissible525 : ClayAdmissibilityAnswer525
  clayInadmissible525 : ClayAdmissibilityAnswer525

record BudgetWorld525 : Set where
  constructor budget-world-525
  field
    dashiObservation525 : DashiBudgetObservation525
    clayAnswer525 : ClayAdmissibilityAnswer525

open BudgetWorld525 public

budgetWorldClayYes525 : BudgetWorld525
budgetWorldClayYes525 =
  budget-world-525 observedInsideSignedBudget525 clayAdmissible525

budgetWorldClayNo525 : BudgetWorld525
budgetWorldClayNo525 =
  budget-world-525 observedInsideSignedBudget525 clayInadmissible525

coarseBudgetObserve525 : BudgetWorld525 → DashiBudgetObservation525
coarseBudgetObserve525 = dashiObservation525

budgetObserverCollision525 :
  coarseBudgetObserve525 budgetWorldClayYes525
  ≡ coarseBudgetObserve525 budgetWorldClayNo525
budgetObserverCollision525 = refl

------------------------------------------------------------------------
-- Cross-checks against the two previous BIDIs and the live Clay residual.
------------------------------------------------------------------------

round525R522StillStartsAtLiteralInstantiation :
  R522.coordinate R522.externalToInternalFirst522
  ≡ R522.externalForcingLiteralCarrierIdentity522
round525R522StillStartsAtLiteralInstantiation = refl

round525R524ClayCStillTargetsExactAlternative :
  R524.targetAlternative524 R524.reportedR3ToClayCFirst524
  ≡ R523.clayAlternativeC523
round525R524ClayCStillTargetsExactAlternative = refl

round525LiveR406ResidualStillFirst :
  R504.firstTerminalResidual R504.currentTerminalStatus
  ≡ R504.missingLiteralR406SignedCrossPayment
round525LiveR406ResidualStillFirst = R504.currentFirstTerminalResidual

------------------------------------------------------------------------
-- No-shortcut firewalls.
------------------------------------------------------------------------

data SignedBudgetImpliesClayAdmissibilityPermission525 : Set where
data ClayAdmissibilityImpliesSignedBudgetPermission525 : Set where
data ExternalBlowupImpliesR406FailurePermission525 : Set where
data R406BoundImpliesClayRegularityForAllForcingPermission525 : Set where

signedBudgetDoesNotCreateClayAdmissibility525 :
  SignedBudgetImpliesClayAdmissibilityPermission525 → ⊥
signedBudgetDoesNotCreateClayAdmissibility525 ()

clayAdmissibilityDoesNotCreateSignedBudget525 :
  ClayAdmissibilityImpliesSignedBudgetPermission525 → ⊥
clayAdmissibilityDoesNotCreateSignedBudget525 ()

externalBlowupDoesNotAutomaticallyRefuteR406525 :
  ExternalBlowupImpliesR406FailurePermission525 → ⊥
externalBlowupDoesNotAutomaticallyRefuteR406525 ()

r406BoundDoesNotAutomaticallyProveClayRegularityForAllForcing525 :
  R406BoundImpliesClayRegularityForAllForcingPermission525 → ⊥
r406BoundDoesNotAutomaticallyProveClayRegularityForAllForcing525 ()

------------------------------------------------------------------------
-- Ledger.
------------------------------------------------------------------------

round525TriangleBidiImplemented : Bool
round525TriangleBidiImplemented = true

round525ClayRefinesR522Formulation : Bool
round525ClayRefinesR522Formulation = true

round525FirstNewMissingCoordinateIsClassInclusion : Bool
round525FirstNewMissingCoordinateIsClassInclusion = true

round525GlobalR406ResidualChanged : Bool
round525GlobalR406ResidualChanged = false

round525ClayPromotion : Bool
round525ClayPromotion = false

round525TriangleBidiImplementedIsTrue :
  round525TriangleBidiImplemented ≡ true
round525TriangleBidiImplementedIsTrue = refl

round525ClayRefinesR522FormulationIsTrue :
  round525ClayRefinesR522Formulation ≡ true
round525ClayRefinesR522FormulationIsTrue = refl

round525FirstNewMissingCoordinateIsClassInclusionIsTrue :
  round525FirstNewMissingCoordinateIsClassInclusion ≡ true
round525FirstNewMissingCoordinateIsClassInclusionIsTrue = refl

round525GlobalR406ResidualChangedIsFalse :
  round525GlobalR406ResidualChanged ≡ false
round525GlobalR406ResidualChangedIsFalse = refl

round525ClayPromotionIsFalse : round525ClayPromotion ≡ false
round525ClayPromotionIsFalse = refl
