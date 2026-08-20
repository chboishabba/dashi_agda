module DASHI.Core.EvidenceReliabilityPolarityExact where

------------------------------------------------------------------------
-- EVIDENCE POLARITY + RELIABILITY WITHOUT ARTIFICIAL OPPOSITION
--
-- Animalexic and LES both expose the same failure mode: missing or unreliable
-- evidence must not be silently converted into evidence against a claim.  The
-- shared kernel already distinguishes support / opposition / ignorance /
-- conflict; this module gives that four-way surface exact two-bit semantics and
-- a reliability discount law.
--
-- Calibration only (not proof authority):
-- Arthur P. Dempster, "Upper and Lower Probabilities Induced by a Multivalued
-- Mapping", Annals of Mathematical Statistics 38(2), 1967.
-- DOI: 10.1214/aoms/1177698950.
-- Glenn Shafer, "A Mathematical Theory of Evidence", Princeton Univ. Press,
-- 1976. DOI: 10.1515/9780691214696.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.ReopenableConsumerInterventionKernelExact as Kernel

------------------------------------------------------------------------
-- Two independent information coordinates: support and counter-support.
------------------------------------------------------------------------

record EvidenceBits : Set where
  constructor evidenceBits
  field
    supports : Bool
    opposes : Bool

open EvidenceBits public

classifyEvidence : EvidenceBits → Kernel.EvidenceDisposition
classifyEvidence (evidenceBits false false) = Kernel.ignorance
classifyEvidence (evidenceBits true false) = Kernel.support
classifyEvidence (evidenceBits false true) = Kernel.opposition
classifyEvidence (evidenceBits true true) = Kernel.conflict

ignoranceIsNoSupportNoOpposition :
  classifyEvidence (evidenceBits false false) ≡ Kernel.ignorance
ignoranceIsNoSupportNoOpposition = refl

conflictIsSupportAndOpposition :
  classifyEvidence (evidenceBits true true) ≡ Kernel.conflict
conflictIsSupportAndOpposition = refl

supportOnlyIsNotConflict :
  classifyEvidence (evidenceBits true false) ≡ Kernel.conflict → ⊥
supportOnlyIsNotConflict ()

ignoranceIsNotOpposition :
  classifyEvidence (evidenceBits false false) ≡ Kernel.opposition → ⊥
ignoranceIsNotOpposition ()

------------------------------------------------------------------------
-- Reliability discounting.
--
-- `trusted = false` does not flip polarity.  It moves the item to ignorance.
-- This is the exact reusable law requested by the cross-domain notes:
--
--   low reliability -> more ignorance, not more opposition.
------------------------------------------------------------------------

discountByReliability :
  Bool → Kernel.EvidenceDisposition → Kernel.EvidenceDisposition
discountByReliability true disposition = disposition
discountByReliability false disposition = Kernel.ignorance

lowReliabilityBecomesIgnorance :
  ∀ disposition →
  discountByReliability false disposition ≡ Kernel.ignorance
lowReliabilityBecomesIgnorance disposition = refl

trustedReliabilityPreservesDisposition :
  ∀ disposition →
  discountByReliability true disposition ≡ disposition
trustedReliabilityPreservesDisposition disposition = refl

lowReliabilityCannotCreateOpposition :
  ∀ disposition →
  discountByReliability false disposition ≡ Kernel.opposition → ⊥
lowReliabilityCannotCreateOpposition disposition ()

lowReliabilityCannotCreateSupport :
  ∀ disposition →
  discountByReliability false disposition ≡ Kernel.support → ⊥
lowReliabilityCannotCreateSupport disposition ()

------------------------------------------------------------------------
-- Reliability is evidence metadata, not an authority promotion.
------------------------------------------------------------------------

record ReliabilityAssessment : Set where
  constructor reliabilityAssessment
  field
    rawDisposition : Kernel.EvidenceDisposition
    trusted : Bool
    effectiveDisposition : Kernel.EvidenceDisposition
    discountLaw :
      effectiveDisposition ≡ discountByReliability trusted rawDisposition

open ReliabilityAssessment public
