module DASHI.Core.SelectiveInvalidationWorklistBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.AristotleFrontierWorklistTruthMaintenanceBridgeExact as Aristotle
import DASHI.Core.SelectiveInvalidationParetoFrontierBidiExact as Pareto

------------------------------------------------------------------------
-- SELECTIVE INVALIDATION WORKLIST
--
-- Aristotle's Lean Worklist proves that grouping diagnostic rows into tasks is
-- an exact partition.  Here the same theorem shape is expressed dependently:
-- every recompute candidate has exactly one semantic task key, its class.
------------------------------------------------------------------------

record RecomputeTask (key : Pareto.RecomputeClass) : Set where
  constructor recompute-task
  field
    candidate : Pareto.CertificateCandidate
    classReceipt : Pareto.class candidate ≡ key
    taskReference : String

open RecomputeTask public

AnyRecomputeTask : Set
AnyRecomputeTask = Σ Pareto.RecomputeClass RecomputeTask

taskOfCandidate : Pareto.CertificateCandidate → AnyRecomputeTask
taskOfCandidate candidate =
  Pareto.class candidate ,
    recompute-task candidate refl
      "candidate grouped under exactly its declared recompute class"

candidateOfTask : AnyRecomputeTask → Pareto.CertificateCandidate
candidateOfTask (key , task) = candidate task

worklistGroupingLosesNothing :
  (candidate : Pareto.CertificateCandidate) →
  candidateOfTask (taskOfCandidate candidate) ≡ candidate
worklistGroupingLosesNothing candidate = refl

classKeyUnique :
  (candidate : Pareto.CertificateCandidate) →
  (left right : Pareto.RecomputeClass) →
  Pareto.class candidate ≡ left →
  Pareto.class candidate ≡ right →
  left ≡ right
classKeyUnique candidate left right refl refl = refl

------------------------------------------------------------------------
-- Repair safety is a second fibre, not implied by task membership.
------------------------------------------------------------------------

data RepairDisposition : Set where
  retainNoAction
  provenSemanticsPreservingRepair
  suggestedRepairNeedsProof
  humanReviewRequired
  authorityProducerRequired
  : RepairDisposition

record WorklistRepairTask (key : Pareto.RecomputeClass) : Set where
  constructor worklist-repair-task
  field
    recomputeTask : RecomputeTask key
    disposition : RepairDisposition
    preservationReceipt : Set
    repairReference : String

open WorklistRepairTask public

unaffectedRetentionTask : WorklistRepairTask Pareto.provablyUnaffected
unaffectedRetentionTask =
  worklist-repair-task
    (recompute-task Pareto.frameBranch refl
      "independent frame certificate grouped as provably unaffected")
    retainNoAction
    ⊤
    "retain certificate; no repair is executed"

authorityBoundaryTask : WorklistRepairTask Pareto.authorityBlocked
authorityBoundaryTask =
  worklist-repair-task
    (recompute-task Pareto.authorityReview refl
      "authority boundary grouped separately from epistemic recomputation")
    authorityProducerRequired
    ⊤
    "authority needs its own producer; Pareto/debug work does not manufacture it"

aristotleWorklistDonorRetained : Aristotle.AristotleMethodologyDonor
aristotleWorklistDonorRetained = Aristotle.canonicalAristotleMethodologyDonor

data TaskMembershipProvesRepairSafe : Set where
data ParetoPreferredMeansAutomaticProvenFix : Set where
data WorklistGroupingCreatesAuthority : Set where

taskMembershipDoesNotProveRepairSafe : TaskMembershipProvesRepairSafe → ⊥
taskMembershipDoesNotProveRepairSafe ()

paretoPreferenceDoesNotCreateAutomaticProof :
  ParetoPreferredMeansAutomaticProvenFix → ⊥
paretoPreferenceDoesNotCreateAutomaticProof ()

worklistGroupingDoesNotCreateAuthority : WorklistGroupingCreatesAuthority → ⊥
worklistGroupingDoesNotCreateAuthority ()
