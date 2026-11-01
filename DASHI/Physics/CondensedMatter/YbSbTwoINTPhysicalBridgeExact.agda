module DASHI.Physics.CondensedMatter.YbSbTwoINTPhysicalBridgeExact where

------------------------------------------------------------------------
-- Physical-identification boundary for YbSb2.
--
-- This owner deliberately does NOT identify the experimentally observed
-- spontaneous field with the finite selected INT state by construction.
-- It packages the two independently formalised lanes and makes the
-- missing same-object identification explicit.
------------------------------------------------------------------------

open import Data.Empty using (⊥)

import DASHI.Physics.CondensedMatter.SuperconductingTimeReversalGaugeObstructionExact as TR
import DASHI.Physics.CondensedMatter.YbSbTwoINTNonunitarySelectedExact as INT
import DASHI.Physics.CondensedMatter.YbSbTwoMuSRTRSBEvidenceExact as MuSR

record YbSbTwoEvidenceAndCandidate : Set where
  constructor evidenceAndCandidate
  field
    experimentalEvidence : MuSR.ZFMuSRTRSBEvidence
    candidateState : INT.INTState

open YbSbTwoEvidenceAndCandidate public

paperEvidenceSelectedINTCandidate :
  YbSbTwoEvidenceAndCandidate
paperEvidenceSelectedINTCandidate =
  evidenceAndCandidate MuSR.paperMuSREvidence INT.selectedINT

-- A future microscopic/phenomenological closure must justify this link.
-- It is not synthesized from the two records above.
record PhysicalINTIdentification
    (bundle : YbSbTwoEvidenceAndCandidate) : Set where
  field
    measuredTRSBIsAccountedForByCandidate : Set
    identificationWitness :
      measuredTRSBIsAccountedForByCandidate

-- Conditional terminal theorem: once a physically justified
-- identification is independently supplied, the candidate on the same
-- bundle carries the exact TR-up-to-gauge obstruction already proved in
-- the reusable INT lane.
identifiedSelectedCandidateBreaksTRUpToGauge :
  PhysicalINTIdentification paperEvidenceSelectedINTCandidate →
  TR.TRGaugeEquivalent INT.intTRSystem INT.selectedINT →
  ⊥
identifiedSelectedCandidateBreaksTRUpToGauge id =
  INT.selectedINTBreaksTRUpToGauge
