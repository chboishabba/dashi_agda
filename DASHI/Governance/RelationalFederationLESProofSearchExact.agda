module DASHI.Governance.RelationalFederationLESProofSearchExact where

-- Existing LES quantities, paths, planner, proof scheduler and ZKP owners
-- are canonical. New arithmetic is a two-site, one-unit, one-period weld.
-- No empirical calibration, legal authority or cryptographic security claim.
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using ([])
open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
open import Data.Nat using (_+_; z≤n)
open import Data.Nat.Properties using (+-assoc; +-comm)
import DASHI.Environment.QuantitiesConservation as Q
import DASHI.Environment.SpatialTransport as Spatial
import DASHI.Environment.SpringfieldPondGoldenScenario as Pond
import DASHI.Environment.LESSequentialExperimentPlannerExact as LES
import DASHI.Environment.ParetoPlanning as Pareto
import DASHI.Environment.SurrogateCalibration as Cal
import DASHI.Core.ProofSearchExperimentalParetoCrossPollinationExact as Search
import DASHI.Core.LiteralFrontierSchedulerExact as Scheduler
import DASHI.Core.ProofSearchLeastPrivilegeAdmissionExact as ProofSearch
import DASHI.Core.EvidenceAcquisitionSelectiveReopeningExact as Acquire
import DASHI.Interop.IntrospectiveProofLoopExact as Z
import DASHI.Interop.DistributedProofProducerABIExact as ABI
import DASHI.Computation.ZKPPrintingPressProtocol as Press

lesBoundary : LES.LESSequentialExperimentBoundary
lesBoundary = LES.canonicalLESSequentialExperimentBoundary

selectionBoundary : Pareto.SelectionSeparationBoundary
selectionBoundary = Pareto.canonicalSelectionSeparationBoundary

searchBoundary : Search.ProofSearchExperimentalParetoBoundary
searchBoundary = Search.canonicalProofSearchExperimentalParetoBoundary

schedulerBoundary : Scheduler.LiteralFrontierSchedulerBoundary
schedulerBoundary = Scheduler.canonicalLiteralFrontierSchedulerBoundary

originalPondFixture : Pond.SpringfieldPondGoldenScenario
originalPondFixture = Pond.canonicalSpringfieldPondGoldenScenario

-- Each receipt retains model, tolerance and unaccounted residual.
-- The consolidation retains both residuals, not a claim of exact physical
-- measurement or an assertion that all relevant stores are declared.
incoming : ∀ {u} → Q.BalanceReceipt u → Nat
incoming b = Q.magnitude (Q.openingStorage b) + Q.magnitude (Q.externalInput b)

retained : ∀ {u} → Q.BalanceReceipt u → Nat
retained b = (Q.magnitude (Q.closingStorage b) +
  Q.magnitude (Q.accountedTransformation b)) +
  Q.magnitude (Q.unaccountedResidual b)

exported : ∀ {u} → Q.BalanceReceipt u → Nat
exported b = Q.magnitude (Q.externalExport b)

localBalance : ∀ {u} (b : Q.BalanceReceipt u) →
  incoming b ≡ exported b + retained b
localBalance b =
  trans (cong Q.magnitude (Q.balanceEquation b))
    (trans (cong (λ n → n + r) (+-assoc e c t))
      (+-assoc e (c + t) r))
  where
    e = exported b
    c = Q.magnitude (Q.closingStorage b)
    t = Q.magnitude (Q.accountedTransformation b)
    r = Q.magnitude (Q.unaccountedResidual b)

-- Same exact unit. Sender's entire export is the recipient's entire input;
-- extra external edges require explicit decomposition in the generalization.
record MatchedTransfer {u : Q.Unit}
  (source target : Spatial.SpatialNode) (window : Spatial.TimeWindow)
  (sender receiver : Q.BalanceReceipt u) : Set where
  field
    path : Spatial.Path source target
    transferMatches : Q.externalExport sender ≡ Q.externalInput receiver

-- Algebraic cancellation; no netting of mismatched units, receipts or time.
twoSiteConservation :
  ∀ {u : Q.Unit} {source target : Spatial.SpatialNode}
    {window : Spatial.TimeWindow}
    (a b : Q.BalanceReceipt u) →
  MatchedTransfer source target window a b →
  incoming a + Q.magnitude (Q.openingStorage b)
    ≡ retained a + (exported b + retained b)
twoSiteConservation a b transfer =
  trans (cong (λ n → n + ob) (localBalance a))
  (trans (cong (λ n → n + ob) (+-comm xa (retained a)))
  (trans (+-assoc (retained a) xa ob)
  (trans (cong (λ n → retained a + (n + ob))
    (cong Q.magnitude (MatchedTransfer.transferMatches transfer)))
  (trans (cong (λ n → retained a + n) (+-comm ib ob))
    (cong (λ n → retained a + n) (localBalance b))))))
  where
    xa = exported a
    ob = Q.magnitude (Q.openingStorage b)
    ib = Q.magnitude (Q.externalInput b)

-- Synthetic nonzero extension of the existing pond path, NOT the original
-- pond's empirical quantities (that original fixture uses zero balances).
senderFixture : Q.PhosphorusBalance
senderFixture = Q.mkBalanceReceipt
  (Q.qty 8) (Q.qty 2) (Q.qty 4) (Q.qty 5) (Q.qty 1) (Q.qty 0)
  refl (Q.qty 0) z≤n "synthetic transfer fixture" []

receiverFixture : Q.PhosphorusBalance
receiverFixture = Q.mkBalanceReceipt
  (Q.qty 2) (Q.qty 4) (Q.qty 1) (Q.qty 4) (Q.qty 1) (Q.qty 0)
  refl (Q.qty 0) z≤n "synthetic transfer fixture" []

pondTransferFixture :
  MatchedTransfer Pond.upperCatchment Pond.pond Pond.window
    senderFixture receiverFixture
pondTransferFixture = record
  { path = Pond.phosphorusPath
  ; transferMatches = refl }

pondConsolidates :
  incoming senderFixture + Q.magnitude (Q.openingStorage receiverFixture)
  ≡ retained senderFixture + (exported receiverFixture + retained receiverFixture)
pondConsolidates = twoSiteConservation senderFixture receiverFixture pondTransferFixture

-- ZKPFrame is the repository's introspective planning frame, not a
-- cryptographic proof system. ReceiptBound is a typed provenance/visibility
-- contract with Nat hash labels, not proof of cryptographic binding.
-- Independent verifier, semantic review and exact target must still be paid.
record VerifiedTarget (target : ABI.ProofObligation)
  (Verify : ABI.ProofReceipt → Set)
  (SemanticReview : ABI.ProofObligation → Set) : Set where
  field
    frame : Z.ZKPFrame
    artifactReceipt : Press.Receipt
    artifactBound : Press.ReceiptBound artifactReceipt
    proofReceipt : ABI.ProofReceipt
    exactObligation : ABI.obligation proofReceipt ≡ target
    actualRun : ABI.executionObserved proofReceipt ≡ true
    success : ABI.resultKind proofReceipt ≡ ABI.proofSucceeded
    independentVerification : Verify proofReceipt
    semanticReview : SemanticReview target

-- A rejected or redirected move is not promoted by the new consumer.
-- Use the literal scheduler's existing closed-move capability.
closedMoveProgress :
  {move : Scheduler.LiteralFrontierMove} →
  Scheduler.ClosedLiteralMove move →
  ProofSearch.ProgrammeProgress
closedMoveProgress = Scheduler.programmeProgressFromClosed
