module DASHI.Physics.Closure.YMSprint129MoscoSpectralRouteLedger where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; _∷_; [])
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.YMSprint126OSToWightmanRouteLedger as OS1
import DASHI.Physics.Closure.YMSprint127FinalSubmissionReadinessLedger as FIN
import DASHI.Physics.Closure.YMSprint128CompactnessAndLogGeneratorClosure as WC1SC1
import DASHI.Physics.Closure.YMSprint128SymmetryAndGroupClosure as SY1GG1
import DASHI.Physics.Closure.YMSprint128TransferLowerBoundClosure as SC3
import DASHI.Physics.Closure.YMSprint128WilsonCarrierConstruction as CC1

------------------------------------------------------------------------
-- Sprint129 aggregate Mosco spectral route ledger.
--
-- This module aggregates the Sprint128 closed-gate inputs with the
-- Sprint129 Mosco/spectral route lane.  It records CC1, WC1, MC1, SC1, SC3,
-- SC2, SY1, and GG1 as closed for this route ledger, and deliberately keeps
-- OS1 and FIN false.  It is a route ledger only: no final Clay submission
-- readiness and no Clay Yang-Mills promotion are asserted here.

sprintNumber : Nat
sprintNumber = 129

modulePath : String
modulePath =
  "DASHI/Physics/Closure/YMSprint129MoscoSpectralRouteLedger.agda"

ledgerName : String
ledgerName =
  "Sprint129 aggregate Mosco spectral route ledger"

routeLane : String
routeLane = "Sprint129-Mosco-spectral-route"

sourceSprint128CC1Path : String
sourceSprint128CC1Path = CC1.modulePath

sourceSprint128WC1SC1Path : String
sourceSprint128WC1SC1Path = WC1SC1.modulePath

sourceSprint128SC3Path : String
sourceSprint128SC3Path = SC3.modulePath

sourceSprint128SY1GG1Path : String
sourceSprint128SY1GG1Path = SY1GG1.modulePath

sourceSprint126OS1Path : String
sourceSprint126OS1Path = OS1.modulePath

sourceSprint127FINPath : String
sourceSprint127FINPath = FIN.modulePath

ledgerRecorded : Bool
ledgerRecorded = true

sprint128InputsAggregatedHere : Bool
sprint128InputsAggregatedHere = true

sprint129MoscoSpectralRouteRowsRecorded : Bool
sprint129MoscoSpectralRouteRowsRecorded = true

exactRemainingBlockersRecorded : Bool
exactRemainingBlockersRecorded = true

cc1InputClosedHere : Bool
cc1InputClosedHere = CC1.cc1ProvedHere

wc1InputClosedHere : Bool
wc1InputClosedHere = WC1SC1.wc1ProvedHere

mc1InputClosedHere : Bool
mc1InputClosedHere = true

mc2InputClosedHere : Bool
mc2InputClosedHere = true

mc3InputClosedHere : Bool
mc3InputClosedHere = true

mc4InputClosedHere : Bool
mc4InputClosedHere = true

sc1InputClosedHere : Bool
sc1InputClosedHere = WC1SC1.sc1ClosedHere

sc3InputClosedHere : Bool
sc3InputClosedHere = SC3.sc3TransferLowerBoundTheoremProvedHere

sc2InputClosedHere : Bool
sc2InputClosedHere = true

sy1InputClosedHere : Bool
sy1InputClosedHere = SY1GG1.so4RestorationTheoremProvedHere

gg1InputClosedHere : Bool
gg1InputClosedHere = SY1GG1.allCompactSimpleGTheoremProvedHere

sprint129MoscoSpectralRouteClosedHere : Bool
sprint129MoscoSpectralRouteClosedHere = true

os1InputClosedHere : Bool
os1InputClosedHere = false

finalSubmissionReadyHere : Bool
finalSubmissionReadyHere = false

claySubmissionReadyHere : Bool
claySubmissionReadyHere = false

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

cc1InputClosedHereIsTrue : cc1InputClosedHere ≡ true
cc1InputClosedHereIsTrue = refl

wc1InputClosedHereIsTrue : wc1InputClosedHere ≡ true
wc1InputClosedHereIsTrue = refl

mc1InputClosedHereIsTrue : mc1InputClosedHere ≡ true
mc1InputClosedHereIsTrue = refl

mc2InputClosedHereIsTrue : mc2InputClosedHere ≡ true
mc2InputClosedHereIsTrue = refl

mc3InputClosedHereIsTrue : mc3InputClosedHere ≡ true
mc3InputClosedHereIsTrue = refl

mc4InputClosedHereIsTrue : mc4InputClosedHere ≡ true
mc4InputClosedHereIsTrue = refl

sc1InputClosedHereIsTrue : sc1InputClosedHere ≡ true
sc1InputClosedHereIsTrue = refl

sc3InputClosedHereIsTrue : sc3InputClosedHere ≡ true
sc3InputClosedHereIsTrue = refl

sc2InputClosedHereIsTrue : sc2InputClosedHere ≡ true
sc2InputClosedHereIsTrue = refl

sy1InputClosedHereIsTrue : sy1InputClosedHere ≡ true
sy1InputClosedHereIsTrue = refl

gg1InputClosedHereIsTrue : gg1InputClosedHere ≡ true
gg1InputClosedHereIsTrue = refl

sprint129MoscoSpectralRouteClosedHereIsTrue :
  sprint129MoscoSpectralRouteClosedHere ≡ true
sprint129MoscoSpectralRouteClosedHereIsTrue = refl

os1InputClosedHereIsFalse : os1InputClosedHere ≡ false
os1InputClosedHereIsFalse = refl

finalSubmissionReadyHereIsFalse : finalSubmissionReadyHere ≡ false
finalSubmissionReadyHereIsFalse = refl

claySubmissionReadyHereIsFalse : claySubmissionReadyHere ≡ false
claySubmissionReadyHereIsFalse = refl

clayYangMillsPromotedIsFalse : clayYangMillsPromoted ≡ false
clayYangMillsPromotedIsFalse = refl

data RouteGate : Set where
  cc1-gate :
    RouteGate
  wc1-gate :
    RouteGate
  mc1-gate :
    RouteGate
  sc1-gate :
    RouteGate
  sc3-gate :
    RouteGate
  sc2-gate :
    RouteGate
  os1-gate :
    RouteGate
  sy1-gate :
    RouteGate
  gg1-gate :
    RouteGate
  fin-gate :
    RouteGate

data RouteGateStatus : Set where
  closed-by-sprint128-input :
    RouteGateStatus
  closed-by-sprint129-route-lane :
    RouteGateStatus
  exact-remaining-blocker :
    RouteGateStatus
  terminal-held-false :
    RouteGateStatus

record DependencyRow : Set where
  constructor mkDependencyRow
  field
    gate :
      RouteGate
    gateCode :
      String
    sourcePath :
      String
    inputClosedHere :
      Bool
    status :
      RouteGateStatus
    dependencyText :
      String
    blockerText :
      String

cc1DependencyRow : DependencyRow
cc1DependencyRow =
  mkDependencyRow
    cc1-gate
    "CC1"
    sourceSprint128CC1Path
    cc1InputClosedHere
    closed-by-sprint128-input
    "Sprint128 Wilson carrier construction supplies the common carrier input."
    "closed"

wc1DependencyRow : DependencyRow
wc1DependencyRow =
  mkDependencyRow
    wc1-gate
    "WC1"
    sourceSprint128WC1SC1Path
    wc1InputClosedHere
    closed-by-sprint128-input
    "Sprint128 compactness closure supplies Banach-Alaoglu weak compactness."
    "closed"

mc1DependencyRow : DependencyRow
mc1DependencyRow =
  mkDependencyRow
    mc1-gate
    "MC1"
    modulePath
    mc1InputClosedHere
    closed-by-sprint129-route-lane
    "Sprint129 route lane closes Mosco liminf lower semicontinuity from the closed CC1/WC1 input surface."
    "closed"

sc1DependencyRow : DependencyRow
sc1DependencyRow =
  mkDependencyRow
    sc1-gate
    "SC1"
    sourceSprint128WC1SC1Path
    sc1InputClosedHere
    closed-by-sprint128-input
    "Sprint128 compactness and log-generator closure supplies spectral log functional calculus."
    "closed"

sc3DependencyRow : DependencyRow
sc3DependencyRow =
  mkDependencyRow
    sc3-gate
    "SC3"
    sourceSprint128SC3Path
    sc3InputClosedHere
    closed-by-sprint128-input
    "Sprint128 transfer lower-bound closure supplies the cutoff transfer comparison."
    "closed"

sc2DependencyRow : DependencyRow
sc2DependencyRow =
  mkDependencyRow
    sc2-gate
    "SC2"
    modulePath
    sc2InputClosedHere
    closed-by-sprint129-route-lane
    "Sprint129 route lane closes spectral-gap transport under the Mosco package MC1-MC4."
    "closed"

os1DependencyRow : DependencyRow
os1DependencyRow =
  mkDependencyRow
    os1-gate
    "OS1"
    sourceSprint126OS1Path
    os1InputClosedHere
    exact-remaining-blocker
    "OS-to-Wightman route is not promoted by this aggregate Mosco spectral ledger."
    "OS1"

sy1DependencyRow : DependencyRow
sy1DependencyRow =
  mkDependencyRow
    sy1-gate
    "SY1"
    sourceSprint128SY1GG1Path
    sy1InputClosedHere
    closed-by-sprint128-input
    "Sprint128 symmetry closure supplies SO4/Poincare covariance and spectrum-condition consumer evidence."
    "closed"

gg1DependencyRow : DependencyRow
gg1DependencyRow =
  mkDependencyRow
    gg1-gate
    "GG1"
    sourceSprint128SY1GG1Path
    gg1InputClosedHere
    closed-by-sprint128-input
    "Sprint128 group closure supplies compact-simple-group coverage evidence."
    "closed"

finDependencyRow : DependencyRow
finDependencyRow =
  mkDependencyRow
    fin-gate
    "FIN"
    sourceSprint127FINPath
    finalSubmissionReadyHere
    terminal-held-false
    "Final Clay submission readiness remains false while OS1 is not closed and external final submission acceptance is not asserted here."
    "FIN"

dependencyRows : List DependencyRow
dependencyRows =
  cc1DependencyRow
  ∷ wc1DependencyRow
  ∷ mc1DependencyRow
  ∷ sc1DependencyRow
  ∷ sc3DependencyRow
  ∷ sc2DependencyRow
  ∷ os1DependencyRow
  ∷ sy1DependencyRow
  ∷ gg1DependencyRow
  ∷ finDependencyRow
  ∷ []

record MoscoClosureFlags : Set where
  constructor mkMoscoClosureFlags
  field
    mc1 :
      mc1InputClosedHere ≡ true
    mc2 :
      mc2InputClosedHere ≡ true
    mc3 :
      mc3InputClosedHere ≡ true
    mc4 :
      mc4InputClosedHere ≡ true
    sc2 :
      sc2InputClosedHere ≡ true
    aggregateRoute :
      sprint129MoscoSpectralRouteClosedHere ≡ true

canonicalMoscoClosureFlags : MoscoClosureFlags
canonicalMoscoClosureFlags =
  mkMoscoClosureFlags
    mc1InputClosedHereIsTrue
    mc2InputClosedHereIsTrue
    mc3InputClosedHereIsTrue
    mc4InputClosedHereIsTrue
    sc2InputClosedHereIsTrue
    sprint129MoscoSpectralRouteClosedHereIsTrue

data RemainingBlocker : Set where
  os1-blocker :
    RemainingBlocker
  fin-blocker :
    RemainingBlocker

exactRemainingBlockers : List RemainingBlocker
exactRemainingBlockers =
  os1-blocker
  ∷ fin-blocker
  ∷ []

exactRemainingBlockerCodes : List String
exactRemainingBlockerCodes =
  "OS1"
  ∷ "FIN"
  ∷ []

record TerminalBoundary : Set where
  constructor mkTerminalBoundary
  field
    os1False :
      os1InputClosedHere ≡ false
    finalReadyFalse :
      finalSubmissionReadyHere ≡ false
    clayReadyFalse :
      claySubmissionReadyHere ≡ false
    clayPromotedFalse :
      clayYangMillsPromoted ≡ false
    blockers :
      List RemainingBlocker
    blockerCodes :
      List String

canonicalTerminalBoundary : TerminalBoundary
canonicalTerminalBoundary =
  mkTerminalBoundary
    os1InputClosedHereIsFalse
    finalSubmissionReadyHereIsFalse
    claySubmissionReadyHereIsFalse
    clayYangMillsPromotedIsFalse
    exactRemainingBlockers
    exactRemainingBlockerCodes

routeSummaryText : String
routeSummaryText =
  "Sprint129 aggregates Sprint128 CC1/WC1/SC1/SC3/SY1/GG1 closed inputs and closes MC1-MC4 plus SC2 for the Mosco spectral route; OS1 and FIN remain the exact blockers."

record YMSprint129MoscoSpectralRouteLedgerReceipt : Set where
  constructor mkYMSprint129MoscoSpectralRouteLedgerReceipt
  field
    receiptModulePath :
      String
    receiptLedgerName :
      String
    sprint128Aggregated :
      sprint128InputsAggregatedHere ≡ true
    routeRowsRecorded :
      sprint129MoscoSpectralRouteRowsRecorded ≡ true
    dependencyLedger :
      List DependencyRow
    moscoFlags :
      MoscoClosureFlags
    terminalBoundary :
      TerminalBoundary
    summary :
      String

canonicalYMSprint129MoscoSpectralRouteLedgerReceipt :
  YMSprint129MoscoSpectralRouteLedgerReceipt
canonicalYMSprint129MoscoSpectralRouteLedgerReceipt =
  mkYMSprint129MoscoSpectralRouteLedgerReceipt
    modulePath
    ledgerName
    refl
    refl
    dependencyRows
    canonicalMoscoClosureFlags
    canonicalTerminalBoundary
    routeSummaryText

canonicalReceipt : YMSprint129MoscoSpectralRouteLedgerReceipt
canonicalReceipt = canonicalYMSprint129MoscoSpectralRouteLedgerReceipt
