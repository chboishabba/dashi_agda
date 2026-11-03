{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.TSVFOSSameSelectedClockIterateExact where

-- HIGHEST-ALPHA P07: ACTUAL ORIGINAL TSVF ADMISSIBLE-HISTORY SOURCE
-- -> OBSERVER CLOCK -> THE ORIGINAL OS RECONSTRUCTED HAMILTONIAN.
--
-- Two distinct statements must not be conflated:
--  (i) finite source-owned observer/OS iteration commutes for ALL n once
--      a SINGLE physically measured one-step intertwiner is provided;
-- (ii) equality of real strongly continuous translation groups and
--      their self-adjoint generators requires full physical Stone/OS
--      Hilbert completion, common dense domain, source action/units.
--
-- Reuse original R331 OSIndexedTransferCoordinate and R577 source;
-- they select OS.hamiltonian reconstruction DEFINITIONALLY, so there
-- is no second unconnected Hamiltonian label to compare post hoc.
-- Reuse original TSFVKKSameMetricTransportExact for an OPTIONAL 5D-KK
-- (3,1)-metric upgrade. The pure 4D Clay YM clock bridge does not depend
-- on KK: it is the standalone core below.
--
-- No physical same-clock, nonzero YM mass gap, or full Stone theorem is
-- manufactured from finite iteration or from matching (3,1) signatures.

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
open import Data.Empty using (⊥)

import DASHI.Quantum.TSVF as TSVF
import DASHI.Physics.Foundations.BidirectionallyAdmissibleHistoryFibreExact as Bidi
import DASHI.Physics.Foundations.TSVFAdmissibleQuantumOverlapRobustnessExact as Source
import DASHI.Physics.Foundations.TSFVKKSameMetricTransportExact as SameMetric
import DASHI.Physics.Foundations.TSFVFiltrationArrowLorentzBridgeExact as Arrow
import DASHI.Physics.YangMills.BalabanOSMassGapClosure as OS
import DASHI.Physics.YangMills.BalabanOSIndexedTransferCoordinateRound331Exact as R331
import DASHI.Physics.Foundations.Lorentz31DirectionalProbeExact as L31
import DASHI.Physics.YangMills.YMClayLorentz31DirectionalKKHodgeExact as KK

------------------------------------------------------------------------
-- The chosen observer clock is the original Q.TSVF transition kernel,
-- not a new independent flow picked merely to match OS.
------------------------------------------------------------------------

iterate : ∀ {State : Set} →
  Nat → (State → State) → State → State
iterate zero step x = x
iterate (suc n) step x = step (iterate n step x)

record OriginalTSVFToOSClock
    {F : Bidi.BidirectionallyAdmissibleHistoryFibre}
    {Q : TSVF.QuantumSurface}
    (E : TSVF.TSVFEnsemble Q)
    {Observable Point Scalar : Set}
    {system : OS.ContinuumSchwingerSystem Observable Point Scalar}
    (reconstruction : OS.OSReconstructionAuthority Observable Point Scalar system)
    (Energy : Set) : Set₁ where
  field
    selectedHistorySource : Source.AdmissibleTSVFQuantumSource F Q E

    -- R331 directly indexes the physical transfer coordinate by THIS H.
    reconstructedTransfer :
      R331.OSIndexedTransferCoordinate reconstruction Energy

    OSState : Set
    OSObservable : Set
    osStep : OSState → OSState

    -- Physical identification and inverse between observer ket states
    -- and the selected reconstructed state carrier must be proved.
    embedObserver : TSVF.QuantumSurface.Ket Q → OSState
    decodeObserver : OSState → TSVF.QuantumSurface.Ket Q
    decodeEmbed : ∀ x → decodeObserver (embedObserver x) ≡ x
    embedDecode : ∀ x → embedObserver (decodeObserver x) ≡ x

    observerStep : TSVF.QuantumSurface.Ket Q →
                   TSVF.QuantumSurface.Ket Q

    observerStepIsOriginalTSVF :
      (x : TSVF.QuantumSurface.Ket Q) →
      observerStep x
      ≡ TSVF.QuantumSurface.evolveKet Q
          (TSVF.initialTime E) (TSVF.middleTime E) x

    -- Hard physical interface: the selected original TSVF observed step
    -- is carried by the SAME OS reconstructed translation semigroup.
    oneStepIntertwines :
      (x : TSVF.QuantumSurface.Ket Q) →
      embedObserver (observerStep x)
      ≡ osStep (embedObserver x)

    observerRead : TSVF.QuantumSurface.Ket Q → OSObservable
    osRead : OSState → OSObservable
    readTransport :
      (x : TSVF.QuantumSurface.Ket Q) →
      osRead (embedObserver x) ≡ observerRead x

    -- Critical scope: no continuum Stone group is packaged as an arbitrary
    -- freely chosen proof type here. The physical strongly continuous
    -- translation group, common dense domain, spectral correspondence and
    -- real OS gauge-invariant source are genuinely ABSENT and still required.

open OriginalTSVFToOSClock public

-- Actual all-n commuting result: source clock and OS transfer cannot
-- silently disagree at any finite number of measured steps.
observerOSClockAllFiniteTimes :
  ∀ {F Q E Observable Point Scalar system reconstruction Energy}
  (clock : OriginalTSVFToOSClock {F} {Q} E
    {Observable} {Point} {Scalar} {system} reconstruction Energy) →
  (n : Nat) (x : TSVF.QuantumSurface.Ket Q) →
  embedObserver clock (iterate n (observerStep clock) x)
  ≡ iterate n (osStep clock) (embedObserver clock x)
observerOSClockAllFiniteTimes clock zero x = refl
observerOSClockAllFiniteTimes clock (suc n) x =
  trans
    (oneStepIntertwines clock (iterate n (observerStep clock) x))
    (cong (osStep clock)
      (observerOSClockAllFiniteTimes clock n x))

observerOSAllFiniteReadouts :
  ∀ {F Q E Observable Point Scalar system reconstruction Energy}
  (clock : OriginalTSVFToOSClock {F} {Q} E
    {Observable} {Point} {Scalar} {system} reconstruction Energy) →
  (n : Nat) (x : TSVF.QuantumSurface.Ket Q) →
  osRead clock (iterate n (osStep clock) (embedObserver clock x))
  ≡ observerRead clock (iterate n (observerStep clock) x)
observerOSAllFiniteReadouts clock n x =
  trans
    (cong (osRead clock)
      (sym (observerOSClockAllFiniteTimes clock n x)))
    (readTransport clock (iterate n (observerStep clock) x))

selectedOSClockHamiltonian :
  ∀ {F Q E Observable Point Scalar system reconstruction Energy} →
  OriginalTSVFToOSClock {F} {Q} E
    {Observable} {Point} {Scalar} {system} reconstruction Energy →
  OS.Hamiltonian reconstruction
selectedOSClockHamiltonian {reconstruction = reconstruction} clock =
  OS.hamiltonian reconstruction

selectedTransferIsOfExactlyReconstructedH :
  ∀ {F Q E Observable Point Scalar system reconstruction Energy}
  (clock : OriginalTSVFToOSClock {F} {Q} E
    {Observable} {Point} {Scalar} {system} reconstruction Energy) →
  R331.TransferCoordinateOf (reconstructedTransfer clock)
    (selectedOSClockHamiltonian clock)
    (R331.coordinate (reconstructedTransfer clock))
selectedTransferIsOfExactlyReconstructedH clock =
  R331.coordinateOfReconstructedHamiltonian (reconstructedTransfer clock)

------------------------------------------------------------------------
-- Additional same-physical-metric Lorentz (3,1)/spacelike KK layer.
-- NOT needed for the standalone Euclidean 4D Clay YM proof.
------------------------------------------------------------------------

record SameMetric31ClockUpgrade
    {F Q E Observable Point Scalar system reconstruction Energy}
    (clock : OriginalTSVFToOSClock {F} {Q} E
      {Observable} {Point} {Scalar} {system} reconstruction Energy)
    : Set₁ where
  field
    sameObservedMetric : SameMetric.SameMetricTSFVKK

    -- The chosen arrow/metric physical state is now explicitly linked to
    -- the ORIGINAL observed forward TSVF ket, not just a signature label.
    observerKetToSelectedPhysicalState :
      TSVF.QuantumSurface.Ket Q →
      Arrow.SelectedTSFVToLorentzPhysicalSource.PhysicalState
        (SameMetric.arrowSource sameObservedMetric)

    observedForwardKetIsMetricPhysicalState :
      observerKetToSelectedPhysicalState (TSVF.forwardState E)
      ≡ Arrow.SelectedTSFVToLorentzPhysicalSource.selectedState
          (SameMetric.arrowSource sameObservedMetric)

open SameMetric31ClockUpgrade public

selectedObserverKetReallyIsMetricState :
  ∀ {F Q E Observable Point Scalar system reconstruction Energy}
    {clock : OriginalTSVFToOSClock {F} {Q} E
      {Observable} {Point} {Scalar} {system} reconstruction Energy} →
  (upgrade : SameMetric31ClockUpgrade clock) →
  observerKetToSelectedPhysicalState upgrade (TSVF.forwardState E)
  ≡ Arrow.SelectedTSFVToLorentzPhysicalSource.selectedState
      (SameMetric.arrowSource (sameObservedMetric upgrade))
selectedObserverKetReallyIsMetricState =
  observedForwardKetIsMetricPhysicalState

sameClockPhysicalMetricHas31Signature :
  ∀ {F Q E Observable Point Scalar system reconstruction Energy}
    {clock : OriginalTSVFToOSClock {F} {Q} E
      {Observable} {Point} {Scalar} {system} reconstruction Energy} →
  (upgrade : SameMetric31ClockUpgrade clock) →
  L31.actualAxisCounts
    (KK.SameSourceKKYMContinuation.signatureSigns
      (SameMetric.kkSource (sameObservedMetric upgrade)))
  ≡ L31.signature 3 1
sameClockPhysicalMetricHas31Signature upgrade =
  SameMetric.sameMetricKKSignatureFromTSFV (sameObservedMetric upgrade)

------------------------------------------------------------------------
-- Exact negative control: even matching a carrier and a time label is
-- INSUFFICIENT for the required one-step source intertwiner.
------------------------------------------------------------------------

data FiniteTick : Set where
  tickZero tickOne : FiniteTick

observerIdentityStep : FiniteTick → FiniteTick
observerIdentityStep x = x

wrongOSFlipStep : FiniteTick → FiniteTick
wrongOSFlipStep tickZero = tickOne
wrongOSFlipStep tickOne = tickZero

identityEmbeddingCannotIntertwineWrongOSStep :
  ((x : FiniteTick) →
    observerIdentityStep x ≡ wrongOSFlipStep x) → ⊥
identityEmbeddingCannotIntertwineWrongOSStep proposed
  with proposed tickZero
... | ()
