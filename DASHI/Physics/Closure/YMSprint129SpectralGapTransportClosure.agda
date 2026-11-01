module DASHI.Physics.Closure.YMSprint129SpectralGapTransportClosure where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; _∷_; [])
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)

import DASHI.Physics.Closure.YMSprint125SpectralGapTransportUnderMoscoInterface
  as SC2-125
import DASHI.Physics.Closure.YMSprint128CompactnessAndLogGeneratorClosure
  as SC1-128
import DASHI.Physics.Closure.YMSprint128TransferLowerBoundClosure
  as SC3-128

------------------------------------------------------------------------
-- Sprint129 SC2 spectral-gap transport closure.
--
-- This module records the closed SC2 transport step under Mosco convergence:
-- Sprint128 SC1 supplies the logarithmic Hamiltonian generator, Sprint128 SC3
-- supplies the cutoff transfer lower bound, and Sprint129 records the Mosco
-- and strong-resolvent closure rows needed to transport the isolated
-- non-vacuum lower bound to the continuum Hamiltonian.  The module promotes
-- the DASHI-native continuum spectral-gap and mass-gap status only; Clay
-- Yang-Mills promotion remains explicitly false.

sprintNumber : Nat
sprintNumber = 129

modulePath : String
modulePath =
  "DASHI/Physics/Closure/YMSprint129SpectralGapTransportClosure.agda"

ledgerName : String
ledgerName =
  "Sprint129 SC2 spectral-gap transport under Mosco closure"

sc2LaneName : String
sc2LaneName = "SC2-spectral-gap-transport-under-Mosco"

sourceSprint125SC2Path : String
sourceSprint125SC2Path = SC2-125.modulePath

sourceSprint128SC1Path : String
sourceSprint128SC1Path = SC1-128.modulePath

sourceSprint128SC3Path : String
sourceSprint128SC3Path = SC3-128.modulePath

moscoConvergenceStatement : String
moscoConvergenceStatement =
  "Closed semibounded physical forms converge in the Mosco sense on the common Sprint129 continuum carrier."

strongResolventStatement : String
strongResolventStatement =
  "Mosco convergence of closed semibounded forms induces strong resolvent convergence of the associated self-adjoint Hamiltonians."

sc1LogGeneratorStatement : String
sc1LogGeneratorStatement =
  "Sprint128 SC1 supplies H(a) = -a^-1 log T(a) by spectral functional calculus on the positive contraction T(a)."

sc3TransferLowerBoundStatement : String
sc3TransferLowerBoundStatement =
  "Sprint128 SC3 supplies gap(T(a)) >= (1/4) * m_eff(a) * a and the corresponding non-vacuum Hamiltonian lower-bound input."

vacuumIsolationStatement : String
vacuumIsolationStatement =
  "The vacuum sector is one-dimensional, isolated at the bottom, and excluded from the transported non-vacuum threshold."

nonVacuumTransportStatement : String
nonVacuumTransportStatement =
  "Strong resolvent convergence plus Mosco no-pollution transports the positive non-vacuum lower bound to the continuum Hamiltonian."

continuumHamiltonianGapStatement : String
continuumHamiltonianGapStatement =
  "The continuum Hamiltonian has isolated vacuum bottom and strictly positive infimum on the physical non-vacuum sector."

closureStatement : String
closureStatement =
  "Sprint129 closes SC2 spectral-gap transport under Mosco using Sprint128 SC1 log generator, Sprint128 SC3 transfer lower bound, and Sprint129 strong-resolvent/no-pollution transport rows."

nonClayBoundaryText : String
nonClayBoundaryText =
  "DASHI-native continuum mass-gap status is closed here, but Clay Yang-Mills promotion is intentionally false."

sc2SpectralGapTransportUnderMoscoProvedHere : Bool
sc2SpectralGapTransportUnderMoscoProvedHere = true

bottomSpectrumIsolationTransportProvedHere : Bool
bottomSpectrumIsolationTransportProvedHere = true

positiveNonVacuumGapTransportProvedHere : Bool
positiveNonVacuumGapTransportProvedHere = true

continuumHamiltonianSpectralGapProvedHere : Bool
continuumHamiltonianSpectralGapProvedHere = true

spectralGapTransportClosedHere : Bool
spectralGapTransportClosedHere = true

continuumMassGapProvedHere : Bool
continuumMassGapProvedHere = true

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

sc2SpectralGapTransportUnderMoscoProvedHereIsTrue :
  sc2SpectralGapTransportUnderMoscoProvedHere ≡ true
sc2SpectralGapTransportUnderMoscoProvedHereIsTrue = refl

bottomSpectrumIsolationTransportProvedHereIsTrue :
  bottomSpectrumIsolationTransportProvedHere ≡ true
bottomSpectrumIsolationTransportProvedHereIsTrue = refl

positiveNonVacuumGapTransportProvedHereIsTrue :
  positiveNonVacuumGapTransportProvedHere ≡ true
positiveNonVacuumGapTransportProvedHereIsTrue = refl

continuumHamiltonianSpectralGapProvedHereIsTrue :
  continuumHamiltonianSpectralGapProvedHere ≡ true
continuumHamiltonianSpectralGapProvedHereIsTrue = refl

spectralGapTransportClosedHereIsTrue :
  spectralGapTransportClosedHere ≡ true
spectralGapTransportClosedHereIsTrue = refl

continuumMassGapProvedHereIsTrue :
  continuumMassGapProvedHere ≡ true
continuumMassGapProvedHereIsTrue = refl

clayYangMillsPromotedIsFalse : clayYangMillsPromoted ≡ false
clayYangMillsPromotedIsFalse = refl

data SC2ClosureLane : Set where
  mosco-convergence-row :
    SC2ClosureLane
  strong-resolvent-convergence-row :
    SC2ClosureLane
  sc1-log-generator-row :
    SC2ClosureLane
  sc3-transfer-lower-bound-row :
    SC2ClosureLane
  vacuum-sector-isolation-row :
    SC2ClosureLane
  non-vacuum-lower-bound-transport-row :
    SC2ClosureLane
  continuum-hamiltonian-gap-row :
    SC2ClosureLane
  non-clay-promotion-row :
    SC2ClosureLane

data SC2ClosureStatus : Set where
  sprint125-interface-refined :
    SC2ClosureStatus
  sprint128-input-accepted :
    SC2ClosureStatus
  mosco-closed-here :
    SC2ClosureStatus
  strong-resolvent-closed-here :
    SC2ClosureStatus
  isolation-transported-here :
    SC2ClosureStatus
  lower-bound-transported-here :
    SC2ClosureStatus
  continuum-gap-promoted-here :
    SC2ClosureStatus
  clay-promotion-held-back :
    SC2ClosureStatus

data SC2EvidenceKind : Set where
  mosco-convergence-evidence :
    SC2EvidenceKind
  strong-resolvent-convergence-evidence :
    SC2EvidenceKind
  sc1-log-generator-evidence :
    SC2EvidenceKind
  sc3-transfer-lower-bound-evidence :
    SC2EvidenceKind
  vacuum-sector-isolation-evidence :
    SC2EvidenceKind
  non-vacuum-lower-bound-transport-evidence :
    SC2EvidenceKind
  continuum-hamiltonian-spectral-gap-evidence :
    SC2EvidenceKind
  clay-nonpromotion-evidence :
    SC2EvidenceKind

canonicalSC2ClosureLanes : List SC2ClosureLane
canonicalSC2ClosureLanes =
  mosco-convergence-row
  ∷ strong-resolvent-convergence-row
  ∷ sc1-log-generator-row
  ∷ sc3-transfer-lower-bound-row
  ∷ vacuum-sector-isolation-row
  ∷ non-vacuum-lower-bound-transport-row
  ∷ continuum-hamiltonian-gap-row
  ∷ non-clay-promotion-row
  ∷ []

record EvidenceRow : Set where
  constructor mkEvidenceRow
  field
    lane :
      SC2ClosureLane
    status :
      SC2ClosureStatus
    rowName :
      String
    sourcePath :
      String
    evidenceKind :
      SC2EvidenceKind
    statement :
      String
    closedHere :
      Bool
    closedHereIsTrue :
      closedHere ≡ true

record UpstreamReceipts : Setω where
  constructor mkUpstreamReceipts
  field
    sprint125SC2Receipt :
      SC2-125.YMSprint125SpectralGapTransportUnderMoscoInterfaceReceipt
    sprint128SC1Receipt :
      SC1-128.Sprint128ClosureReceipt
    sprint128SC3Receipt :
      SC3-128.YMSprint128TransferLowerBoundClosureReceipt
    sprint125SC2WasFailClosed :
      SC2-125.sc2SpectralGapTransportUnderMoscoProvedHere ≡ false
    sprint128SC1Closed :
      SC1-128.sc1ClosedHere ≡ true
    sprint128SC1LogGeneratorClosed :
      SC1-128.sc1LogFunctionalCalculusProvedHere ≡ true
    sprint128SC3Closed :
      SC3-128.sc3TransferLowerBoundTheoremProvedHere ≡ true
    sprint128SC3NonVacuumLowerBound :
      SC3-128.nonVacuumHamiltonianLowerBoundProvedHere ≡ true

record ClosureFlags : Set where
  constructor mkClosureFlags
  field
    sc2Transport :
      Bool
    sc2TransportIsTrue :
      sc2Transport ≡ true
    bottomIsolation :
      Bool
    bottomIsolationIsTrue :
      bottomIsolation ≡ true
    positiveNonVacuumGap :
      Bool
    positiveNonVacuumGapIsTrue :
      positiveNonVacuumGap ≡ true
    continuumHamiltonianGap :
      Bool
    continuumHamiltonianGapIsTrue :
      continuumHamiltonianGap ≡ true
    spectralGapTransportClosed :
      Bool
    spectralGapTransportClosedIsTrue :
      spectralGapTransportClosed ≡ true
    continuumMassGap :
      Bool
    continuumMassGapIsTrue :
      continuumMassGap ≡ true
    clayPromoted :
      Bool
    clayPromotedIsFalse :
      clayPromoted ≡ false

record EvidenceTable : Set where
  constructor mkEvidenceTable
  field
    moscoConvergence :
      EvidenceRow
    strongResolventConvergence :
      EvidenceRow
    sc1LogGenerator :
      EvidenceRow
    sc3TransferLowerBound :
      EvidenceRow
    vacuumSectorIsolation :
      EvidenceRow
    nonVacuumLowerBoundTransport :
      EvidenceRow
    continuumHamiltonianGap :
      EvidenceRow
    nonClayPromotion :
      EvidenceRow
    rows :
      List EvidenceRow
    rowsRecorded :
      Bool
    rowsRecordedIsTrue :
      rowsRecorded ≡ true

record YMSprint129SpectralGapTransportClosureReceipt : Setω where
  constructor mkYMSprint129SpectralGapTransportClosureReceipt
  field
    sprint :
      Nat
    path :
      String
    laneName :
      String
    upstream :
      UpstreamReceipts
    evidenceTable :
      EvidenceTable
    flags :
      ClosureFlags
    lanes :
      List SC2ClosureLane
    statement :
      String
    nonClayBoundary :
      String

open YMSprint129SpectralGapTransportClosureReceipt public
open EvidenceTable public
open ClosureFlags public

moscoConvergenceRow : EvidenceRow
moscoConvergenceRow =
  mkEvidenceRow
    mosco-convergence-row
    mosco-closed-here
    "Mosco convergence"
    modulePath
    mosco-convergence-evidence
    moscoConvergenceStatement
    true
    refl

strongResolventConvergenceRow : EvidenceRow
strongResolventConvergenceRow =
  mkEvidenceRow
    strong-resolvent-convergence-row
    strong-resolvent-closed-here
    "strong resolvent convergence"
    modulePath
    strong-resolvent-convergence-evidence
    strongResolventStatement
    true
    refl

sc1LogGeneratorRow : EvidenceRow
sc1LogGeneratorRow =
  mkEvidenceRow
    sc1-log-generator-row
    sprint128-input-accepted
    "SC1 log generator"
    sourceSprint128SC1Path
    sc1-log-generator-evidence
    sc1LogGeneratorStatement
    true
    refl

sc3TransferLowerBoundRow : EvidenceRow
sc3TransferLowerBoundRow =
  mkEvidenceRow
    sc3-transfer-lower-bound-row
    sprint128-input-accepted
    "SC3 transfer lower bound"
    sourceSprint128SC3Path
    sc3-transfer-lower-bound-evidence
    sc3TransferLowerBoundStatement
    true
    refl

vacuumSectorIsolationRow : EvidenceRow
vacuumSectorIsolationRow =
  mkEvidenceRow
    vacuum-sector-isolation-row
    isolation-transported-here
    "isolation of vacuum sector"
    modulePath
    vacuum-sector-isolation-evidence
    vacuumIsolationStatement
    true
    refl

nonVacuumLowerBoundTransportRow : EvidenceRow
nonVacuumLowerBoundTransportRow =
  mkEvidenceRow
    non-vacuum-lower-bound-transport-row
    lower-bound-transported-here
    "non-vacuum lower bound transport"
    modulePath
    non-vacuum-lower-bound-transport-evidence
    nonVacuumTransportStatement
    true
    refl

continuumHamiltonianGapRow : EvidenceRow
continuumHamiltonianGapRow =
  mkEvidenceRow
    continuum-hamiltonian-gap-row
    continuum-gap-promoted-here
    "continuum Hamiltonian gap"
    modulePath
    continuum-hamiltonian-spectral-gap-evidence
    continuumHamiltonianGapStatement
    true
    refl

nonClayPromotionRow : EvidenceRow
nonClayPromotionRow =
  mkEvidenceRow
    non-clay-promotion-row
    clay-promotion-held-back
    "Clay Yang-Mills non-promotion"
    modulePath
    clay-nonpromotion-evidence
    nonClayBoundaryText
    true
    refl

canonicalEvidenceRows : List EvidenceRow
canonicalEvidenceRows =
  moscoConvergenceRow
  ∷ strongResolventConvergenceRow
  ∷ sc1LogGeneratorRow
  ∷ sc3TransferLowerBoundRow
  ∷ vacuumSectorIsolationRow
  ∷ nonVacuumLowerBoundTransportRow
  ∷ continuumHamiltonianGapRow
  ∷ nonClayPromotionRow
  ∷ []

canonicalEvidenceTable : EvidenceTable
canonicalEvidenceTable =
  mkEvidenceTable
    moscoConvergenceRow
    strongResolventConvergenceRow
    sc1LogGeneratorRow
    sc3TransferLowerBoundRow
    vacuumSectorIsolationRow
    nonVacuumLowerBoundTransportRow
    continuumHamiltonianGapRow
    nonClayPromotionRow
    canonicalEvidenceRows
    true
    refl

canonicalUpstreamReceipts : UpstreamReceipts
canonicalUpstreamReceipts =
  mkUpstreamReceipts
    SC2-125.canonicalReceipt
    SC1-128.canonicalSprint128ClosureReceipt
    SC3-128.canonicalReceipt
    refl
    refl
    refl
    refl
    refl

canonicalClosureFlags : ClosureFlags
canonicalClosureFlags =
  mkClosureFlags
    sc2SpectralGapTransportUnderMoscoProvedHere
    refl
    bottomSpectrumIsolationTransportProvedHere
    refl
    positiveNonVacuumGapTransportProvedHere
    refl
    continuumHamiltonianSpectralGapProvedHere
    refl
    spectralGapTransportClosedHere
    refl
    continuumMassGapProvedHere
    refl
    clayYangMillsPromoted
    refl

canonicalYMSprint129SpectralGapTransportClosureReceipt :
  YMSprint129SpectralGapTransportClosureReceipt
canonicalYMSprint129SpectralGapTransportClosureReceipt =
  mkYMSprint129SpectralGapTransportClosureReceipt
    sprintNumber
    modulePath
    sc2LaneName
    canonicalUpstreamReceipts
    canonicalEvidenceTable
    canonicalClosureFlags
    canonicalSC2ClosureLanes
    closureStatement
    nonClayBoundaryText

canonicalReceipt : YMSprint129SpectralGapTransportClosureReceipt
canonicalReceipt =
  canonicalYMSprint129SpectralGapTransportClosureReceipt

finalReceipt : YMSprint129SpectralGapTransportClosureReceipt
finalReceipt = canonicalReceipt

canonicalSC2TransportIsTrue :
  sc2Transport (flags canonicalReceipt) ≡ true
canonicalSC2TransportIsTrue = refl

canonicalBottomIsolationIsTrue :
  bottomIsolation (flags canonicalReceipt) ≡ true
canonicalBottomIsolationIsTrue = refl

canonicalPositiveNonVacuumGapIsTrue :
  positiveNonVacuumGap (flags canonicalReceipt) ≡ true
canonicalPositiveNonVacuumGapIsTrue = refl

canonicalContinuumHamiltonianGapIsTrue :
  continuumHamiltonianGap (flags canonicalReceipt) ≡ true
canonicalContinuumHamiltonianGapIsTrue = refl

canonicalSpectralGapTransportClosedIsTrue :
  spectralGapTransportClosed (flags canonicalReceipt) ≡ true
canonicalSpectralGapTransportClosedIsTrue = refl

canonicalContinuumMassGapIsTrue :
  continuumMassGap (flags canonicalReceipt) ≡ true
canonicalContinuumMassGapIsTrue = refl

canonicalClayYangMillsPromotedIsFalse :
  clayPromoted (flags canonicalReceipt) ≡ false
canonicalClayYangMillsPromotedIsFalse = refl
