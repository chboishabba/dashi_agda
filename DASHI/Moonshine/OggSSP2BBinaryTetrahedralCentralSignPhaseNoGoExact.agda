module DASHI.Moonshine.OggSSP2BBinaryTetrahedralCentralSignPhaseNoGoExact where

------------------------------------------------------------------------
-- CENTRAL -1 IS NOT THE COMPLETION10 BINARY PHASE
--
-- Completion10 complement preserves the five-mode quotient and flips only
-- BinaryPhase.  In binary tetrahedral 2T, multiplication by central -1 moves
-- order strata 1 <-> 2 and 3 <-> 6, fixing only order 4.
--
-- Therefore a Mode5 <-> order-stratum recognition cannot simultaneously make
-- Completion10 BinaryPhase equal central-sign multiplication on the strata.
-- The remaining two provenance decisions must come from other sourced data.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Biology.NonaryCompletionPhaseQuotientExact as Completion
import DASHI.Moonshine.OggSSP2BBinaryTetrahedralDefectSourceExact as Defect
import DASHI.Moonshine.OggSSP2BDefectTwoBitProvenanceSelectorExact as Bits

centralSignOnStratum : Defect.OrderStratum → Defect.OrderStratum
centralSignOnStratum Defect.identity = Defect.centralMinusOne
centralSignOnStratum Defect.centralMinusOne = Defect.identity
centralSignOnStratum Defect.orderFour = Defect.orderFour
centralSignOnStratum Defect.orderThree = Defect.orderSix
centralSignOnStratum Defect.orderSix = Defect.orderThree

centralSignOnStratumInvolutive :
  (s : Defect.OrderStratum) →
  centralSignOnStratum (centralSignOnStratum s) ≡ s
centralSignOnStratumInvolutive Defect.identity = refl
centralSignOnStratumInvolutive Defect.centralMinusOne = refl
centralSignOnStratumInvolutive Defect.orderFour = refl
centralSignOnStratumInvolutive Defect.orderThree = refl
centralSignOnStratumInvolutive Defect.orderSix = refl

------------------------------------------------------------------------
-- The no-go is computed on the actual four candidate charts.
------------------------------------------------------------------------

centralSignChangesMode09 :
  (bits : Bits.ProvenanceBits) →
  centralSignOnStratum (Bits.chartFromBits bits Completion.mode09)
  ≡ Bits.chartFromBits bits Completion.mode09 →
  ⊥
centralSignChangesMode09
  (Bits.provenance-bits Bits.mode09IsIdentity Bits.mode36IsOrderThree) ()
centralSignChangesMode09
  (Bits.provenance-bits Bits.mode18IsIdentity Bits.mode36IsOrderThree) ()
centralSignChangesMode09
  (Bits.provenance-bits Bits.mode09IsIdentity Bits.mode45IsOrderThree) ()
centralSignChangesMode09
  (Bits.provenance-bits Bits.mode18IsIdentity Bits.mode45IsOrderThree) ()

/-- No one of the four defect-compatible charts can make central-sign
multiplication act trivially on every Mode5 stratum.  But Completion10
BinaryPhase is trivial on the Mode5 quotient, because complement preserves
Mode5.  Therefore central -1 cannot source-select BinaryPhase at this quotient
level. -/
noCandidateChartIntertwinesModePreservingPhaseWithCentralSign :
  (bits : Bits.ProvenanceBits) →
  ((mode : Completion.ComplementMode5) →
    centralSignOnStratum (Bits.chartFromBits bits mode)
    ≡ Bits.chartFromBits bits mode) →
  ⊥
noCandidateChartIntertwinesModePreservingPhaseWithCentralSign bits h =
  centralSignChangesMode09 bits (h Completion.mode09)

/-- Compatibility name for the canonical frontier. -/
completionModePreservingPhaseIsNotCentralSignOnStrata :
  (bits : Bits.ProvenanceBits) →
  ((mode : Completion.ComplementMode5) →
    centralSignOnStratum (Bits.chartFromBits bits mode)
    ≡ Bits.chartFromBits bits mode) →
  ⊥
completionModePreservingPhaseIsNotCentralSignOnStrata =
  noCandidateChartIntertwinesModePreservingPhaseWithCentralSign
