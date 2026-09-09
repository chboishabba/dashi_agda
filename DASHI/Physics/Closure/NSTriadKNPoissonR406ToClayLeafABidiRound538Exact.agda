module DASHI.Physics.Closure.NSTriadKNPoissonR406ToClayLeafABidiRound538Exact where

------------------------------------------------------------------------
-- ROUND538 / POISSON R406 TRANSPORT <-> CLAY LEAF-A BIDI
--
-- R537 makes the generic Poisson kernel a lawful producer of the R535
-- spectral-measure bridge only after a concrete Poisson problem/receipt is
-- supplied.  The present owner asks the next, Clay-facing question:
--
--   what additional receipts are required before that cross-domain equality can
--   count as payment of R504 terminal leaf A?
--
-- The answer is deliberately stronger than "Poisson equality":
--
--   concrete R406 Poisson instance
--     + same-object physical weld
--     + exact identity of the R535 bridge with that Poisson-produced bridge
--     + cutoff correspondence
--     + literal R406 cross-domain weld
--     + source-domain cutoff-uniform signed-cross budget
--     + preservation of that uniform bound on the target domain
--       ---------------------------------------------------------
--       target-domain literal R406 signed-cross payment (leaf A)
--
-- Even that advances the strict terminal cut only from leaf A to leaf B.
-- The independent phase-sensitive critical-production slice/initial ceiling
-- remains required.  No Poisson theorem is therefore a Clay promotion by
-- itself.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Analysis.PoissonSummationKernelBidiExact as Poisson
import DASHI.Physics.Closure.NSTriadKNPoissonKernelToLiteralR406MeasureBridgeRound537Exact as R537
import DASHI.Physics.Closure.NSTriadKNLiteralR406LatticeContinuumTransportConsumerRound535Exact as Consumer
import DASHI.Physics.Closure.NSTriadKNLiteralR406ClayTerminalCutsetRound504Exact as R504

------------------------------------------------------------------------
-- 1. Clay-facing completion data for one concrete Poisson/R406 instance.
--
-- The source-domain budget is intentionally kept abstract here.  R503 owns the
-- concrete direct-off-diagonal budget on the live trajectory; this bridge must
-- not duplicate that dynamics owner.  The fields below say only that the budget
-- used for transport is literally the R504 leaf-A budget and that its
-- cutoff-independent constant survives the domain transport.
------------------------------------------------------------------------

record PoissonR406ClayLeafACompletion538
    (P : Poisson.PoissonSummationProblem) : Set₂ where
  constructor poisson-r406-clay-leaf-a-completion-538
  field
    poissonR406Producer538 : R537.LiteralR406PoissonProducer537 P

    measureBridge538 : Consumer.SpectralMeasureBridge535
    measureBridgeIsProducedByPoisson538 :
      measureBridge538
      ≡ R537.measureBridgeFromLiteralR406PoissonProducer537
          poissonR406Producer538

    cutoffCorrespondence538 : Consumer.CutoffCorrespondence535 measureBridge538
    literalCrossDomainTransport538 :
      Consumer.LiteralR406CrossDomainTransport535
        measureBridge538 cutoffCorrespondence538

    SourceDomainLiteralSignedCrossBudget538 : Set
    sourceDomainLiteralSignedCrossBudget538 :
      SourceDomainLiteralSignedCrossBudget538

    TargetDomainLiteralSignedCrossBudget538 : Set
    transportSourceBudgetToTarget538 :
      SourceDomainLiteralSignedCrossBudget538 →
      TargetDomainLiteralSignedCrossBudget538

    sourceBudgetIsR504LeafA538 :
      SourceDomainLiteralSignedCrossBudget538 → Set

    targetBudgetIsR504LeafA538 :
      TargetDomainLiteralSignedCrossBudget538 → Set

    sourceBudgetLiterallyPaysLeafA538 :
      sourceBudgetIsR504LeafA538 sourceDomainLiteralSignedCrossBudget538

    transportedBudgetLiterallyPaysLeafA538 :
      targetBudgetIsR504LeafA538
        (transportSourceBudgetToTarget538 sourceDomainLiteralSignedCrossBudget538)

open PoissonR406ClayLeafACompletion538 public

------------------------------------------------------------------------
-- 2. Forward direction: a fully welded Poisson transport can advance the
-- terminal cut to leaf B, but no further.
------------------------------------------------------------------------

leafAPaidStatus538 : R504.TerminalStatus
leafAPaidStatus538 = R504.terminal-status true false

poissonLeafACompletionAdvancesTerminalCut538 :
  R504.firstTerminalResidual leafAPaidStatus538
  ≡ R504.missingLiteralR406CriticalProductionSlice
poissonLeafACompletionAdvancesTerminalCut538 = refl

------------------------------------------------------------------------
-- 3. Reverse BIDI: any claimed Poisson route "toward Clay" must expose each
-- consumer-visible coordinate rather than hiding them behind the word Poisson.
------------------------------------------------------------------------

data PoissonClayAuditCoordinate538 : Set where
  auditConcretePoissonR406Instance538 : PoissonClayAuditCoordinate538
  auditPoissonAnalyticHypotheses538 : PoissonClayAuditCoordinate538
  auditPoissonProducedMeasureBridgeIdentity538 : PoissonClayAuditCoordinate538
  auditLiteralPeriodicSameObject538 : PoissonClayAuditCoordinate538
  auditLiteralEuclideanSameObject538 : PoissonClayAuditCoordinate538
  auditR406Normalization538 : PoissonClayAuditCoordinate538
  auditR406CutoffGeometry538 : PoissonClayAuditCoordinate538
  auditSourceDomainUniformSignedCrossBudget538 : PoissonClayAuditCoordinate538
  auditTargetDomainUniformBoundPreservation538 : PoissonClayAuditCoordinate538
  auditIndependentCriticalProductionLeafB538 : PoissonClayAuditCoordinate538

record PoissonClayReverseAudit538
    (P : Poisson.PoissonSummationProblem) : Set₂ where
  constructor poisson-clay-reverse-audit-538
  field
    poissonReverseAudit538 : R537.R406PoissonReverseAudit537 P
    clayLeafACompletion538 : PoissonR406ClayLeafACompletion538 P
    CriticalProductionLeafBReceipt538 : Set

open PoissonClayReverseAudit538 public

------------------------------------------------------------------------
-- 4. Dependency classification.
------------------------------------------------------------------------

data R538Residual : Set where
  missingConcretePoissonR406Instantiation538 : R538Residual
  missingPoissonR406SameObjectWeld538 : R538Residual
  missingPoissonProducedMeasureBridgeIdentity538 : R538Residual
  missingR406CutoffCorrespondence538 : R538Residual
  missingSourceDomainLeafABudget538 : R538Residual
  missingUniformBoundTransport538 : R538Residual
  missingIndependentCriticalProductionLeafB538 : R538Residual
  terminalCutsetClosed538 : R538Residual

currentR538Residual : R538Residual
currentR538Residual = missingConcretePoissonR406Instantiation538

------------------------------------------------------------------------
-- 5. Firewalls.
------------------------------------------------------------------------

data PoissonEqualityPaysLeafAPermission538 : Set where
data CrossDomainLeafAPaysLeafBPermission538 : Set where
data PoissonRoutePromotesClayPermission538 : Set where

poissonEqualityAloneDoesNotPayLeafA538 :
  PoissonEqualityPaysLeafAPermission538 → ⊥
poissonEqualityAloneDoesNotPayLeafA538 ()

crossDomainLeafADoesNotPayLeafB538 :
  CrossDomainLeafAPaysLeafBPermission538 → ⊥
crossDomainLeafADoesNotPayLeafB538 ()

poissonRouteDoesNotAutoPromoteClay538 :
  PoissonRoutePromotesClayPermission538 → ⊥
poissonRouteDoesNotAutoPromoteClay538 ()

------------------------------------------------------------------------
-- 6. Status ledger.
------------------------------------------------------------------------

round538PoissonMeasureBridgeCanContributeToLeafA : Bool
round538PoissonMeasureBridgeCanContributeToLeafA = true

round538PoissonEqualityAlonePaysLeafA : Bool
round538PoissonEqualityAlonePaysLeafA = false

round538LeafACompletionLeavesCriticalProductionResidual : Bool
round538LeafACompletionLeavesCriticalProductionResidual = true

round538CurrentGlobalFirstResidualStillLeafA :
  R504.firstTerminalResidual R504.currentTerminalStatus
  ≡ R504.missingLiteralR406SignedCrossPayment
round538CurrentGlobalFirstResidualStillLeafA = R504.currentFirstTerminalResidual

round538ClayPromotion : Bool
round538ClayPromotion = false

round538PoissonMeasureBridgeCanContributeToLeafAIsTrue :
  round538PoissonMeasureBridgeCanContributeToLeafA ≡ true
round538PoissonMeasureBridgeCanContributeToLeafAIsTrue = refl

round538PoissonEqualityAlonePaysLeafAIsFalse :
  round538PoissonEqualityAlonePaysLeafA ≡ false
round538PoissonEqualityAlonePaysLeafAIsFalse = refl

round538LeafACompletionLeavesCriticalProductionResidualIsTrue :
  round538LeafACompletionLeavesCriticalProductionResidual ≡ true
round538LeafACompletionLeavesCriticalProductionResidualIsTrue = refl

round538ClayPromotionIsFalse : round538ClayPromotion ≡ false
round538ClayPromotionIsFalse = refl
