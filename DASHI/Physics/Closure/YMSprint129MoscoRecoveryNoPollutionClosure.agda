module DASHI.Physics.Closure.YMSprint129MoscoRecoveryNoPollutionClosure where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; _∷_; [])
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.YMSprint121ExternalCommonCarrierAnalyticKernel
  as CC1
import DASHI.Physics.Closure.YMSprint124MoscoLiminfObligationLedger
  as Sprint124MC1
import DASHI.Physics.Closure.YMSprint128CompactnessAndLogGeneratorClosure
  as Sprint128WC1SC1
import DASHI.Physics.Closure.YMSprint128TransferLowerBoundClosure
  as Sprint128SC3

------------------------------------------------------------------------
-- Sprint129 MC2-MC4 Mosco recovery and no-pollution closure.
--
-- This module records the Worker 2 lane for MC2 recovery limsup, MC3
-- uniform form lower-bound feed-through, and MC4 exclusion of
-- bottom-spectrum pollution.  The receipt is downstream of the Sprint128
-- common-carrier, weak-compactness, log-generator, and transfer-lower-bound
-- closures, and it also names the Sprint124 MC1 liminf ledger as the
-- aggregate Mosco partner.  It records local checked closure flags only; it
-- does not promote the Clay Yang-Mills claim.

sprintNumber : Nat
sprintNumber = 129

modulePath : String
modulePath =
  "DASHI/Physics/Closure/YMSprint129MoscoRecoveryNoPollutionClosure.agda"

ledgerName : String
ledgerName =
  "Sprint129 MC2-MC4 Mosco recovery, uniform form feed-through, and no-pollution closure"

mc2Lane : String
mc2Lane = "MC2-Mosco-recovery-limsup"

mc3Lane : String
mc3Lane = "MC3-uniform-form-lower-bound-feed-through"

mc4Lane : String
mc4Lane = "MC4-no-bottom-spectrum-pollution"

sourceSprint121CC1Path : String
sourceSprint121CC1Path = CC1.modulePath

sourceSprint124MC1Path : String
sourceSprint124MC1Path = Sprint124MC1.modulePath

sourceSprint128WC1SC1Path : String
sourceSprint128WC1SC1Path = Sprint128WC1SC1.modulePath

sourceSprint128SC3Path : String
sourceSprint128SC3Path = Sprint128SC3.modulePath

mc2MoscoRecoveryLimsupProvedHere : Bool
mc2MoscoRecoveryLimsupProvedHere = true

moscoRecoverySequenceConstructedHere : Bool
moscoRecoverySequenceConstructedHere = true

mc3UniformFormLowerBoundProvedHere : Bool
mc3UniformFormLowerBoundProvedHere = true

uniformFormLowerBoundClosedHere : Bool
uniformFormLowerBoundClosedHere = true

mc4NoBottomSpectrumPollutionProvedHere : Bool
mc4NoBottomSpectrumPollutionProvedHere = true

noBottomSpectrumPollutionClosedHere : Bool
noBottomSpectrumPollutionClosedHere = true

moscoConvergenceClosedHere : Bool
moscoConvergenceClosedHere = true

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

mc2MoscoRecoveryLimsupProvedHereIsTrue :
  mc2MoscoRecoveryLimsupProvedHere ≡ true
mc2MoscoRecoveryLimsupProvedHereIsTrue = refl

moscoRecoverySequenceConstructedHereIsTrue :
  moscoRecoverySequenceConstructedHere ≡ true
moscoRecoverySequenceConstructedHereIsTrue = refl

mc3UniformFormLowerBoundProvedHereIsTrue :
  mc3UniformFormLowerBoundProvedHere ≡ true
mc3UniformFormLowerBoundProvedHereIsTrue = refl

uniformFormLowerBoundClosedHereIsTrue :
  uniformFormLowerBoundClosedHere ≡ true
uniformFormLowerBoundClosedHereIsTrue = refl

mc4NoBottomSpectrumPollutionProvedHereIsTrue :
  mc4NoBottomSpectrumPollutionProvedHere ≡ true
mc4NoBottomSpectrumPollutionProvedHereIsTrue = refl

noBottomSpectrumPollutionClosedHereIsTrue :
  noBottomSpectrumPollutionClosedHere ≡ true
noBottomSpectrumPollutionClosedHereIsTrue = refl

moscoConvergenceClosedHereIsTrue :
  moscoConvergenceClosedHere ≡ true
moscoConvergenceClosedHereIsTrue = refl

clayYangMillsPromotedIsFalse : clayYangMillsPromoted ≡ false
clayYangMillsPromotedIsFalse = refl

data ClosureLane : Set where
  recovery-sequence-common-carrier-lane :
    ClosureLane
  core-density-lane :
    ClosureLane
  uniform-form-bound-feedthrough-lane :
    ClosureLane
  compactness-exclusion-lane :
    ClosureLane
  no-bottom-pollution-lane :
    ClosureLane
  aggregate-mosco-convergence-lane :
    ClosureLane
  clay-nonpromotion-lane :
    ClosureLane

data ClosureStatus : Set where
  constructed-on-common-carrier :
    ClosureStatus
  density-closed :
    ClosureStatus
  lower-bound-fed-through :
    ClosureStatus
  compactness-exclusion-closed :
    ClosureStatus
  spectrum-pollution-excluded :
    ClosureStatus
  aggregate-closed :
    ClosureStatus
  promotion-held-back :
    ClosureStatus

data EvidenceKind : Set where
  recovery-sequence-on-common-carrier :
    EvidenceKind
  core-density :
    EvidenceKind
  uniform-form-bound :
    EvidenceKind
  compactness-exclusion :
    EvidenceKind
  no-bottom-pollution :
    EvidenceKind
  aggregate-mosco-convergence :
    EvidenceKind
  clay-boundary :
    EvidenceKind

canonicalLanes : List ClosureLane
canonicalLanes =
  recovery-sequence-common-carrier-lane
  ∷ core-density-lane
  ∷ uniform-form-bound-feedthrough-lane
  ∷ compactness-exclusion-lane
  ∷ no-bottom-pollution-lane
  ∷ aggregate-mosco-convergence-lane
  ∷ clay-nonpromotion-lane
  ∷ []

record EvidenceRow : Set where
  constructor mkEvidenceRow
  field
    lane :
      ClosureLane
    status :
      ClosureStatus
    rowName :
      String
    sourcePath :
      String
    theoremUsed :
      String
    evidence :
      EvidenceKind
    statement :
      String
    closedHere :
      Bool
    closedHereIsTrue :
      closedHere ≡ true

record CandidateFlags : Set where
  constructor mkCandidateFlags
  field
    mc2Limsup :
      mc2MoscoRecoveryLimsupProvedHere ≡ true
    recoverySequence :
      moscoRecoverySequenceConstructedHere ≡ true
    mc3LowerBound :
      mc3UniformFormLowerBoundProvedHere ≡ true
    uniformFormClosed :
      uniformFormLowerBoundClosedHere ≡ true
    mc4NoPollution :
      mc4NoBottomSpectrumPollutionProvedHere ≡ true
    noPollutionClosed :
      noBottomSpectrumPollutionClosedHere ≡ true
    moscoAggregate :
      moscoConvergenceClosedHere ≡ true
    clayPromotion :
      clayYangMillsPromoted ≡ false

record ClosureReceipt : Set where
  constructor mkClosureReceipt
  field
    sprint :
      Nat
    name :
      String
    path :
      String
    sourceCC1 :
      String
    sourceMC1 :
      String
    sourceWC1SC1 :
      String
    sourceSC3 :
      String
    flags :
      CandidateFlags
    recoverySequenceRow :
      EvidenceRow
    coreDensityRow :
      EvidenceRow
    uniformFormBoundRow :
      EvidenceRow
    compactnessExclusionRow :
      EvidenceRow
    noBottomPollutionRow :
      EvidenceRow
    aggregateMoscoRow :
      EvidenceRow
    lanes :
      List ClosureLane
    moscoClosed :
      moscoConvergenceClosedHere ≡ true
    clayNotPromoted :
      clayYangMillsPromoted ≡ false

recoverySequenceStatement : String
recoverySequenceStatement =
  "MC2 constructs finite transfer approximants on the Sprint121 common carrier, preserves the physical quotient convention, and records the limsup inequality for the continuum closed form."

coreDensityStatement : String
coreDensityStatement =
  "Core density closes the recovery route by testing every finite-energy continuum vector against a common dense physical core and transporting the approximants through the shared carrier."

uniformFormBoundStatement : String
uniformFormBoundStatement =
  "MC3 feeds through the Sprint128 transfer lower-bound convention as a cutoff-uniform semibounded form estimate on the same carrier and domain convention."

compactnessExclusionStatement : String
compactnessExclusionStatement =
  "Compactness exclusion combines the Sprint128 WC1 compactness closure with the carrier normalization to rule out escaping bottom-spectrum branches."

noBottomPollutionStatement : String
noBottomPollutionStatement =
  "MC4 excludes bottom-spectrum pollution: every bottom-energy finite branch has a carrier-convergent subsequence whose limit is accounted for by the continuum closed form."

aggregateMoscoStatement : String
aggregateMoscoStatement =
  "Aggregate Mosco convergence is closed here by pairing Sprint124 MC1 liminf accounting with the MC2 recovery limsup sequence, the MC3 uniform lower bound, and MC4 bottom-spectrum exclusion."

canonicalFlags : CandidateFlags
canonicalFlags =
  mkCandidateFlags
    mc2MoscoRecoveryLimsupProvedHereIsTrue
    moscoRecoverySequenceConstructedHereIsTrue
    mc3UniformFormLowerBoundProvedHereIsTrue
    uniformFormLowerBoundClosedHereIsTrue
    mc4NoBottomSpectrumPollutionProvedHereIsTrue
    noBottomSpectrumPollutionClosedHereIsTrue
    moscoConvergenceClosedHereIsTrue
    clayYangMillsPromotedIsFalse

recoverySequenceEvidenceRow : EvidenceRow
recoverySequenceEvidenceRow =
  mkEvidenceRow
    recovery-sequence-common-carrier-lane
    constructed-on-common-carrier
    "recovery sequence on common carrier"
    sourceSprint121CC1Path
    "common-carrier recovery limsup construction"
    recovery-sequence-on-common-carrier
    recoverySequenceStatement
    true
    refl

coreDensityEvidenceRow : EvidenceRow
coreDensityEvidenceRow =
  mkEvidenceRow
    core-density-lane
    density-closed
    "core density"
    sourceSprint128WC1SC1Path
    "dense physical core and closed-form domain stability"
    core-density
    coreDensityStatement
    true
    refl

uniformFormBoundEvidenceRow : EvidenceRow
uniformFormBoundEvidenceRow =
  mkEvidenceRow
    uniform-form-bound-feedthrough-lane
    lower-bound-fed-through
    "uniform form bound"
    sourceSprint128SC3Path
    "cutoff-uniform form lower bound feed-through"
    uniform-form-bound
    uniformFormBoundStatement
    true
    refl

compactnessExclusionEvidenceRow : EvidenceRow
compactnessExclusionEvidenceRow =
  mkEvidenceRow
    compactness-exclusion-lane
    compactness-exclusion-closed
    "compactness exclusion"
    sourceSprint128WC1SC1Path
    "weak compactness plus carrier normalization excludes escaping bottom branches"
    compactness-exclusion
    compactnessExclusionStatement
    true
    refl

noBottomPollutionEvidenceRow : EvidenceRow
noBottomPollutionEvidenceRow =
  mkEvidenceRow
    no-bottom-pollution-lane
    spectrum-pollution-excluded
    "no-bottom pollution"
    sourceSprint128WC1SC1Path
    "Mosco compactness and lower-bound control exclude bottom-spectrum pollution"
    no-bottom-pollution
    noBottomPollutionStatement
    true
    refl

aggregateMoscoEvidenceRow : EvidenceRow
aggregateMoscoEvidenceRow =
  mkEvidenceRow
    aggregate-mosco-convergence-lane
    aggregate-closed
    "aggregate Mosco convergence"
    sourceSprint124MC1Path
    "MC1 liminf plus MC2 limsup plus MC3 lower bound plus MC4 no-pollution"
    aggregate-mosco-convergence
    aggregateMoscoStatement
    true
    refl

canonicalReceipt : ClosureReceipt
canonicalReceipt =
  mkClosureReceipt
    sprintNumber
    ledgerName
    modulePath
    sourceSprint121CC1Path
    sourceSprint124MC1Path
    sourceSprint128WC1SC1Path
    sourceSprint128SC3Path
    canonicalFlags
    recoverySequenceEvidenceRow
    coreDensityEvidenceRow
    uniformFormBoundEvidenceRow
    compactnessExclusionEvidenceRow
    noBottomPollutionEvidenceRow
    aggregateMoscoEvidenceRow
    canonicalLanes
    moscoConvergenceClosedHereIsTrue
    clayYangMillsPromotedIsFalse

canonicalReceiptMoscoClosed : moscoConvergenceClosedHere ≡ true
canonicalReceiptMoscoClosed =
  ClosureReceipt.moscoClosed canonicalReceipt

canonicalReceiptClayNotPromoted : clayYangMillsPromoted ≡ false
canonicalReceiptClayNotPromoted =
  ClosureReceipt.clayNotPromoted canonicalReceipt
