module DASHI.Physics.Closure.YMSprint127HardTheoremDependencyCutset where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; _∷_; [])
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.YMSprint121ExternalCommonCarrierAnalyticKernel
  as CC1
import DASHI.Physics.Closure.YMSprint122ApproximateInverseResiduals
  as CC4
import DASHI.Physics.Closure.YMSprint122CarrierGaugeCovarianceFeedthrough
  as CC2
import DASHI.Physics.Closure.YMSprint122UniformCarrierNormWindow
  as CC3
import DASHI.Physics.Closure.YMSprint123UniformFormLowerBoundInterface
  as MC3
import DASHI.Physics.Closure.YMSprint123WeakCompactnessExtractionInterface
  as WC1
import DASHI.Physics.Closure.YMSprint124MoscoLiminfObligationLedger
  as MC1
import DASHI.Physics.Closure.YMSprint124MoscoRecoveryNoPollutionInterface
  as MC2MC4
import DASHI.Physics.Closure.YMSprint124WeakCompactnessSectorFeedthrough
  as WC23
import DASHI.Physics.Closure.YMSprint125LogGeneratorFunctionalCalculusClosureLedger
  as SC1
import DASHI.Physics.Closure.YMSprint125SpectralGapTransportUnderMoscoInterface
  as SC2
import DASHI.Physics.Closure.YMSprint125TransferLowerBoundPrepLedger
  as SC3
import DASHI.Physics.Closure.YMSprint126CompactSimpleGroupCompletenessLedger
  as GG1
import DASHI.Physics.Closure.YMSprint126OSToWightmanRouteLedger
  as OS1
import DASHI.Physics.Closure.YMSprint126SymmetryRestorationCitationInterface
  as SY1

------------------------------------------------------------------------
-- Sprint127 hard-theorem dependency cutset.
--
-- This module records the exact hard analytic cutset controlling Clay
-- promotion in the current repository state.  The hard cutset is CC1,
-- WC1, MC1, SC1, and SC3.  Downstream closure rows CC2-CC4, WC2, WC3p,
-- MC2-MC4, SC2, OS1, SY1, GG1, and FIN are represented as concrete
-- inhabited records whose current closed flags are false.
--
-- This module is a status ledger.  It proves no analytic closure theorem,
-- no continuum mass gap, and no Clay Yang-Mills promotion.

sprintNumber : Nat
sprintNumber = 127

modulePath : String
modulePath =
  "DASHI/Physics/Closure/YMSprint127HardTheoremDependencyCutset.agda"

ledgerName : String
ledgerName =
  "Sprint127 hard-theorem dependency cutset"

cutsetLane : String
cutsetLane = "FIN-hard-theorem-dependency-cutset"

ledgerRecorded : Bool
ledgerRecorded = true

hardCutsetRecorded : Bool
hardCutsetRecorded = true

downstreamClosureRowsRecorded : Bool
downstreamClosureRowsRecorded = true

minimalPromotionSetRecorded : Bool
minimalPromotionSetRecorded = true

falsePromotionBoundaryRecorded : Bool
falsePromotionBoundaryRecorded = true

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

continuumMassGapProvedHere : Bool
continuumMassGapProvedHere = false

submissionReadyHere : Bool
submissionReadyHere = false

finClosedHere : Bool
finClosedHere = false

cc1ClosedInput : Bool
cc1ClosedInput = CC1.cc1ProvedHere

wc1ClosedInput : Bool
wc1ClosedInput = WC1.wc1ProvedHere

mc1ClosedInput : Bool
mc1ClosedInput = MC1.mc1ClosedFormLowerSemicontinuityProvedHere

sc1ClosedInput : Bool
sc1ClosedInput = SC1.sc1ClosedHere

sc3ClosedInput : Bool
sc3ClosedInput = SC3.sc3TransferLowerBoundTheoremProvedHere

cc2ClosedInput : Bool
cc2ClosedInput = CC2.carrierGaugeCovarianceFeedthroughClosedHere

cc3ClosedInput : Bool
cc3ClosedInput = CC3.uniformCarrierNormWindowClosedHere

cc4ClosedInput : Bool
cc4ClosedInput = CC4.cc4ApproximateInverseClosedHere

wc2ClosedInput : Bool
wc2ClosedInput = WC23.wc2NullSectorEscapeExcludedHere

wc3pClosedInput : Bool
wc3pClosedInput = WC23.wc3pProjectionSectorStableHere

mc2ClosedInput : Bool
mc2ClosedInput = MC2MC4.mc2RecoveryLimsupProvedHere

mc3ClosedInput : Bool
mc3ClosedInput = MC3.mc3UniformFormLowerBoundProvedHere

mc4ClosedInput : Bool
mc4ClosedInput = MC2MC4.mc4NoBottomSpectrumPollutionProvedHere

sc2ClosedInput : Bool
sc2ClosedInput = SC2.sc2SpectralGapTransportUnderMoscoProvedHere

os1ClosedInput : Bool
os1ClosedInput = OS1.osToWightmanRouteProvedHere

sy1ClosedInput : Bool
sy1ClosedInput = SY1.so4RestorationTheoremProvedHere

gg1ClosedInput : Bool
gg1ClosedInput = GG1.allCompactSimpleGTheoremProvedHere

cc1ClosedInputIsFalse : cc1ClosedInput ≡ false
cc1ClosedInputIsFalse = refl

wc1ClosedInputIsFalse : wc1ClosedInput ≡ false
wc1ClosedInputIsFalse = refl

mc1ClosedInputIsFalse : mc1ClosedInput ≡ false
mc1ClosedInputIsFalse = refl

sc1ClosedInputIsFalse : sc1ClosedInput ≡ false
sc1ClosedInputIsFalse = refl

sc3ClosedInputIsFalse : sc3ClosedInput ≡ false
sc3ClosedInputIsFalse = refl

cc2ClosedInputIsFalse : cc2ClosedInput ≡ false
cc2ClosedInputIsFalse = refl

cc3ClosedInputIsFalse : cc3ClosedInput ≡ false
cc3ClosedInputIsFalse = refl

cc4ClosedInputIsFalse : cc4ClosedInput ≡ false
cc4ClosedInputIsFalse = refl

wc2ClosedInputIsFalse : wc2ClosedInput ≡ false
wc2ClosedInputIsFalse = refl

wc3pClosedInputIsFalse : wc3pClosedInput ≡ false
wc3pClosedInputIsFalse = refl

mc2ClosedInputIsFalse : mc2ClosedInput ≡ false
mc2ClosedInputIsFalse = refl

mc3ClosedInputIsFalse : mc3ClosedInput ≡ false
mc3ClosedInputIsFalse = refl

mc4ClosedInputIsFalse : mc4ClosedInput ≡ false
mc4ClosedInputIsFalse = refl

sc2ClosedInputIsFalse : sc2ClosedInput ≡ false
sc2ClosedInputIsFalse = refl

os1ClosedInputIsFalse : os1ClosedInput ≡ false
os1ClosedInputIsFalse = refl

sy1ClosedInputIsFalse : sy1ClosedInput ≡ false
sy1ClosedInputIsFalse = refl

gg1ClosedInputIsFalse : gg1ClosedInput ≡ false
gg1ClosedInputIsFalse = refl

clayYangMillsPromotedIsFalse : clayYangMillsPromoted ≡ false
clayYangMillsPromotedIsFalse = refl

continuumMassGapProvedHereIsFalse : continuumMassGapProvedHere ≡ false
continuumMassGapProvedHereIsFalse = refl

submissionReadyHereIsFalse : submissionReadyHere ≡ false
submissionReadyHereIsFalse = refl

finClosedHereIsFalse : finClosedHere ≡ false
finClosedHereIsFalse = refl

cutsetStatementText : String
cutsetStatementText =
  "The minimal hard analytic cutset currently blocking promotion is CC1 common carrier construction, WC1 weak compactness extraction, MC1 Mosco liminf, SC1 log-generator functional calculus closure, and SC3 transfer lower bound."

downstreamStatementText : String
downstreamStatementText =
  "Downstream rows CC2-CC4, WC2, WC3p, MC2-MC4, SC2, OS1, SY1, GG1, and FIN are recorded as concrete consumers of the cutset or terminal Clay requirements; their current closure flags are false."

promotionBoundaryText : String
promotionBoundaryText =
  "Promotion boundary: Sprint127 records exact dependencies only.  Clay submission readiness requires the hard cutset plus terminal OS/Wightman, symmetry restoration, compact simple group coverage, and final assembly gates to close in the repository."

failClosedText : String
failClosedText =
  "Fail-closed boundary: continuum mass gap, final submission readiness, FIN closure, and clayYangMillsPromoted are all false here."

data CutsetStatus : Set where
  hard-cutset-member :
    CutsetStatus
  downstream-consumer :
    CutsetStatus
  terminal-clay-gate :
    CutsetStatus
  blocked-by-hard-cutset :
    CutsetStatus
  not-promoted :
    CutsetStatus

data HardGateKey : Set where
  cc1-key :
    HardGateKey
  wc1-key :
    HardGateKey
  mc1-key :
    HardGateKey
  sc1-key :
    HardGateKey
  sc3-key :
    HardGateKey

data ClosureKey : Set where
  cc2-key :
    ClosureKey
  cc3-key :
    ClosureKey
  cc4-key :
    ClosureKey
  wc2-key :
    ClosureKey
  wc3p-key :
    ClosureKey
  mc2-key :
    ClosureKey
  mc3-key :
    ClosureKey
  mc4-key :
    ClosureKey
  sc2-key :
    ClosureKey
  os1-key :
    ClosureKey
  sy1-key :
    ClosureKey
  gg1-key :
    ClosureKey
  fin-key :
    ClosureKey

data CutsetRank : Set where
  first-gate :
    CutsetRank
  second-gate :
    CutsetRank
  third-gate :
    CutsetRank
  fourth-gate :
    CutsetRank
  fifth-gate :
    CutsetRank
  terminal-rank :
    CutsetRank

canonicalHardGateOrder : List HardGateKey
canonicalHardGateOrder =
  cc1-key
  ∷ wc1-key
  ∷ mc1-key
  ∷ sc1-key
  ∷ sc3-key
  ∷ []

canonicalDownstreamOrder : List ClosureKey
canonicalDownstreamOrder =
  cc2-key
  ∷ cc3-key
  ∷ cc4-key
  ∷ wc2-key
  ∷ wc3p-key
  ∷ mc2-key
  ∷ mc3-key
  ∷ mc4-key
  ∷ sc2-key
  ∷ os1-key
  ∷ sy1-key
  ∷ gg1-key
  ∷ fin-key
  ∷ []

record HardGateCutsetRow : Set where
  constructor mkHardGateCutsetRow
  field
    key :
      HardGateKey
    gateName :
      String
    sourcePath :
      String
    requiredTheorem :
      String
    dependencyRole :
      String
    rank :
      CutsetRank
    closedHere :
      Bool
    closedHereIsFalse :
      closedHere ≡ false
    minimalForPromotion :
      Bool
    minimalForPromotionIsTrue :
      minimalForPromotion ≡ true
    status :
      CutsetStatus

record DownstreamClosureRow : Set where
  constructor mkDownstreamClosureRow
  field
    key :
      ClosureKey
    closureName :
      String
    sourcePath :
      String
    immediateBlocker :
      String
    consumedHardGate :
      HardGateKey
    closedHere :
      Bool
    closedHereIsFalse :
      closedHere ≡ false
    status :
      CutsetStatus

record TerminalPromotionGate : Set where
  constructor mkTerminalPromotionGate
  field
    key :
      ClosureKey
    gateName :
      String
    sourcePath :
      String
    requiredForSubmission :
      String
    closedHere :
      Bool
    closedHereIsFalse :
      closedHere ≡ false
    status :
      CutsetStatus

record PromotionCutsetLedger : Set where
  constructor mkPromotionCutsetLedger
  field
    ledgerPath :
      String
    hardRows :
      List HardGateCutsetRow
    downstreamRows :
      List DownstreamClosureRow
    terminalRows :
      List TerminalPromotionGate
    promotionFlag :
      Bool
    promotionFlagIsFalse :
      promotionFlag ≡ false
    submissionReadyFlag :
      Bool
    submissionReadyFlagIsFalse :
      submissionReadyFlag ≡ false
    status :
      CutsetStatus

cc1CutsetRow : HardGateCutsetRow
cc1CutsetRow =
  mkHardGateCutsetRow
    cc1-key
    "CC1"
    CC1.modulePath
    "ExternalCommonCarrierConstruction"
    "Construct concrete uniform carrier maps E_a and P_a before downstream carrier, weak compactness, and Mosco arguments can close."
    first-gate
    cc1ClosedInput
    cc1ClosedInputIsFalse
    true
    refl
    hard-cutset-member

wc1CutsetRow : HardGateCutsetRow
wc1CutsetRow =
  mkHardGateCutsetRow
    wc1-key
    "WC1"
    WC1.modulePath
    "WeakCompactnessExtraction"
    "Extract bounded-energy weakly convergent subsequences on the common carrier supplied by CC1."
    second-gate
    wc1ClosedInput
    wc1ClosedInputIsFalse
    true
    refl
    hard-cutset-member

mc1CutsetRow : HardGateCutsetRow
mc1CutsetRow =
  mkHardGateCutsetRow
    mc1-key
    "MC1"
    MC1.modulePath
    "ClosedFormLowerSemicontinuityMoscoLiminf"
    "Prove the Mosco liminf comparison after CC1, WC1, and uniform form bounds are available."
    third-gate
    mc1ClosedInput
    mc1ClosedInputIsFalse
    true
    refl
    hard-cutset-member

sc1CutsetRow : HardGateCutsetRow
sc1CutsetRow =
  mkHardGateCutsetRow
    sc1-key
    "SC1"
    SC1.modulePath
    "LogGeneratorFunctionalCalculusClosure"
    "Close self-adjointness, logarithmic functional calculus, and domain stability for H(a) = -a^-1 log T(a)."
    fourth-gate
    sc1ClosedInput
    sc1ClosedInputIsFalse
    true
    refl
    hard-cutset-member

sc3CutsetRow : HardGateCutsetRow
sc3CutsetRow =
  mkHardGateCutsetRow
    sc3-key
    "SC3"
    SC3.modulePath
    "TransferLowerBoundTheorem"
    "Prove the DASHI-native transfer lower bound connecting the polymer lower bound to the transfer-matrix spectral gap."
    fifth-gate
    sc3ClosedInput
    sc3ClosedInputIsFalse
    true
    refl
    hard-cutset-member

minimalHardPromotionCutset : List HardGateCutsetRow
minimalHardPromotionCutset =
  cc1CutsetRow
  ∷ wc1CutsetRow
  ∷ mc1CutsetRow
  ∷ sc1CutsetRow
  ∷ sc3CutsetRow
  ∷ []

cc2DownstreamRow : DownstreamClosureRow
cc2DownstreamRow =
  mkDownstreamClosureRow cc2-key "CC2" CC2.modulePath
    "CC1 common carrier maps"
    cc1-key cc2ClosedInput cc2ClosedInputIsFalse
    downstream-consumer

cc3DownstreamRow : DownstreamClosureRow
cc3DownstreamRow =
  mkDownstreamClosureRow cc3-key "CC3" CC3.modulePath
    "CC1 common carrier uniformity"
    cc1-key cc3ClosedInput cc3ClosedInputIsFalse
    downstream-consumer

cc4DownstreamRow : DownstreamClosureRow
cc4DownstreamRow =
  mkDownstreamClosureRow cc4-key "CC4" CC4.modulePath
    "CC1 carrier maps and approximate inverse residual control"
    cc1-key cc4ClosedInput cc4ClosedInputIsFalse
    downstream-consumer

wc2DownstreamRow : DownstreamClosureRow
wc2DownstreamRow =
  mkDownstreamClosureRow wc2-key "WC2" WC23.modulePath
    "WC1 weak compactness plus sector escape exclusion"
    wc1-key wc2ClosedInput wc2ClosedInputIsFalse
    downstream-consumer

wc3pDownstreamRow : DownstreamClosureRow
wc3pDownstreamRow =
  mkDownstreamClosureRow wc3p-key "WC3p" WC23.modulePath
    "WC1 extraction plus projection-sector stability"
    wc1-key wc3pClosedInput wc3pClosedInputIsFalse
    downstream-consumer

mc2DownstreamRow : DownstreamClosureRow
mc2DownstreamRow =
  mkDownstreamClosureRow mc2-key "MC2" MC2MC4.modulePath
    "MC1 liminf and WC1 compactness before Mosco recovery can certify convergence"
    mc1-key mc2ClosedInput mc2ClosedInputIsFalse
    downstream-consumer

mc3DownstreamRow : DownstreamClosureRow
mc3DownstreamRow =
  mkDownstreamClosureRow mc3-key "MC3" MC3.modulePath
    "CC1 common carrier and WC1 bounded-energy compactness feed the uniform form lower-bound interface"
    wc1-key mc3ClosedInput mc3ClosedInputIsFalse
    downstream-consumer

mc4DownstreamRow : DownstreamClosureRow
mc4DownstreamRow =
  mkDownstreamClosureRow mc4-key "MC4" MC2MC4.modulePath
    "MC1 and WC1 must exclude bottom-spectrum pollution through the Mosco route"
    mc1-key mc4ClosedInput mc4ClosedInputIsFalse
    downstream-consumer

sc2DownstreamRow : DownstreamClosureRow
sc2DownstreamRow =
  mkDownstreamClosureRow sc2-key "SC2" SC2.modulePath
    "SC1 generator closure, MC1-MC4 Mosco convergence, and SC3 lower bound"
    sc1-key sc2ClosedInput sc2ClosedInputIsFalse
    blocked-by-hard-cutset

os1DownstreamRow : DownstreamClosureRow
os1DownstreamRow =
  mkDownstreamClosureRow os1-key "OS1" OS1.modulePath
    "SC1-SC3 spectral route plus OS/Wightman reconstruction requirements"
    sc3-key os1ClosedInput os1ClosedInputIsFalse
    terminal-clay-gate

sy1DownstreamRow : DownstreamClosureRow
sy1DownstreamRow =
  mkDownstreamClosureRow sy1-key "SY1" SY1.modulePath
    "Continuum spectral route plus H3 anisotropic lattice to SO4 restoration"
    sc3-key sy1ClosedInput sy1ClosedInputIsFalse
    terminal-clay-gate

gg1DownstreamRow : DownstreamClosureRow
gg1DownstreamRow =
  mkDownstreamClosureRow gg1-key "GG1" GG1.modulePath
    "All compact simple G coverage beyond the finite parameter-table artifact"
    cc1-key gg1ClosedInput gg1ClosedInputIsFalse
    terminal-clay-gate

finDownstreamRow : DownstreamClosureRow
finDownstreamRow =
  mkDownstreamClosureRow fin-key "FIN" modulePath
    "All hard cutset rows and terminal Clay gates must close before final assembly"
    sc3-key finClosedHere finClosedHereIsFalse
    not-promoted

downstreamClosureRows : List DownstreamClosureRow
downstreamClosureRows =
  cc2DownstreamRow
  ∷ cc3DownstreamRow
  ∷ cc4DownstreamRow
  ∷ wc2DownstreamRow
  ∷ wc3pDownstreamRow
  ∷ mc2DownstreamRow
  ∷ mc3DownstreamRow
  ∷ mc4DownstreamRow
  ∷ sc2DownstreamRow
  ∷ os1DownstreamRow
  ∷ sy1DownstreamRow
  ∷ gg1DownstreamRow
  ∷ finDownstreamRow
  ∷ []

os1TerminalGate : TerminalPromotionGate
os1TerminalGate =
  mkTerminalPromotionGate os1-key "OS1" OS1.modulePath
    "Full OS-to-Wightman reconstruction route with Wightman distributions, Poincare covariance, and spectrum condition."
    os1ClosedInput os1ClosedInputIsFalse terminal-clay-gate

sy1TerminalGate : TerminalPromotionGate
sy1TerminalGate =
  mkTerminalPromotionGate sy1-key "SY1" SY1.modulePath
    "H3 anisotropic lattice to SO4 continuum restoration and downstream Wightman Poincare covariance."
    sy1ClosedInput sy1ClosedInputIsFalse terminal-clay-gate

gg1TerminalGate : TerminalPromotionGate
gg1TerminalGate =
  mkTerminalPromotionGate gg1-key "GG1" GG1.modulePath
    "All compact simple G completeness for the Clay problem statement."
    gg1ClosedInput gg1ClosedInputIsFalse terminal-clay-gate

finTerminalGate : TerminalPromotionGate
finTerminalGate =
  mkTerminalPromotionGate fin-key "FIN" modulePath
    "Final submission assembly after all analytic, reconstruction, symmetry, group-scope, and governance checks close."
    finClosedHere finClosedHereIsFalse not-promoted

terminalPromotionGates : List TerminalPromotionGate
terminalPromotionGates =
  os1TerminalGate
  ∷ sy1TerminalGate
  ∷ gg1TerminalGate
  ∷ finTerminalGate
  ∷ []

sprint127HardCutsetLedger : PromotionCutsetLedger
sprint127HardCutsetLedger =
  mkPromotionCutsetLedger
    modulePath
    minimalHardPromotionCutset
    downstreamClosureRows
    terminalPromotionGates
    clayYangMillsPromoted
    clayYangMillsPromotedIsFalse
    submissionReadyHere
    submissionReadyHereIsFalse
    not-promoted
