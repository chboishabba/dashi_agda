module DASHI.Physics.Motors.SmithFilsingerWindingOwnerReturnCutBidiExact where

-- User-transcribed Filsinger midpoint/spark proposal: accessible NST
-- midpoint M; capacitor across "the one coil you want"; 2 diodes off
-- cap and 2 "off here", all forward into joined positives P; return
-- "midpoint, earth, ground"; and "half the potential of the big coil".
-- Selected coil U-V is NOT thereby proved to equal NST full A-B,
-- half A-M, or separately documented Smith/Kelly L2. The full wiring,
-- phase, source work and actual reel's pin map remain unverified.
--
-- CONDITIONAL STATIONARY/RESTORED-CHARGE cut: when a U/V floating island
-- has ONLY four forward-only U/V->P diode edges crossing to external nodes,
-- no other return path and dQ_island/dt = 0, KCL + nonnegative diode
-- current yields ZERO all four package currents. During a finite transient
-- where Q_island declines, positive outward diode pulses are possible:
-- dQ_island/dt + sum_i i_Di = 0. This distinction is essential for the
-- transcribed spark-gap discharge. Do NOT apply instantaneous zero-outflow
-- to a precharged, nonstationary island. For restored cycle, integral
-- outward current = Q_initial - Q_final = 0 absent inward return. A capacitive M return
-- is a DIFFERENT circuit and can carry AC displacement current.
-- See local SymPy source: check_filsinger_midpoint_return_cut_bidi_sympy_20261122.py

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Physics.Motors.Circuit36927ComponentGraphExact as Original
import DASHI.Physics.Motors.SmithFilsingerTranscriptDiagramNumbersSourceIndexExact as Speech

data CoilOwner : Set where
  nativeFullSecondaryAB nativeHalfSecondaryAM separateTunedCoilUV : CoilOwner

data ReturnClass : Set where
  conductiveToM displacementToM noMReturn : ReturnClass

data HasReturnPath : CoilOwner → ReturnClass → Set where
  fullNativePath : HasReturnPath nativeFullSecondaryAB conductiveToM
  halfNativePath : HasReturnPath nativeHalfSecondaryAM conductiveToM
  separateCopperPath : HasReturnPath separateTunedCoilUV conductiveToM
  separateCapacitivePath : HasReturnPath separateTunedCoilUV displacementToM

noFullyFloatingReturn :
  HasReturnPath separateTunedCoilUV noMReturn → ⊥
noFullyFloatingReturn ()

sourceFourNarratedPackages :
  Speech.numberMagnitude Speech.midpointFourDiodes ≡ 4
sourceFourNarratedPackages = refl

-- Finite accumulated-charge bookkeeping, separately from STATIONARY KCL.
-- The supplied receipt says: initial charge = final charge + all outward
-- emitted charge (chosen nonnegative Nat count unit). This admits a finite
-- transient whose final charge is smaller. Internal differential LC charge
-- does NOT substitute for a net original exterior return connection.
record FiniteIslandChargeReceipt (qStart qEnd qOut : Nat) : Set where
  constructor finiteIslandChargeReceipt
  field
    chargeConserved : qStart ≡ qEnd + qOut

-- Concrete counterexample: 1 charge unit may leave a precharged island
-- even if no return recharges it over that interval.
oneOutwardTransientPossible : FiniteIslandChargeReceipt (suc zero) zero (suc zero)
oneOutwardTransientPossible = finiteIslandChargeReceipt refl

-- A replenished/restored island with external inward charge is a
-- DIFFERENT circuit. Its source/return and energy work must be sourced.

-- Current unit Nat enforces forward-only nonnegativity. Island KCL
-- a+(b+(c+d))=0 is an explicit STATIONARY or charge-restored condition,
-- NOT a universal instantaneous condition and NOT historical source evidence.
record FourZeroCurrents (a b c d : Nat) : Set where
  constructor allFourZero
  field
    currentAZero : a ≡ zero
    currentBZero : b ≡ zero
    currentCZero : c ≡ zero
    currentDZero : d ≡ zero

fourOutwardDiodesNoWorkWithoutReturn :
  (a b c d : Nat) →
  a + (b + (c + d)) ≡ zero →
  FourZeroCurrents a b c d
fourOutwardDiodesNoWorkWithoutReturn zero zero zero zero p =
  allFourZero refl refl refl refl
fourOutwardDiodesNoWorkWithoutReturn (suc a) b c d ()
fourOutwardDiodesNoWorkWithoutReturn zero (suc b) c d ()
fourOutwardDiodesNoWorkWithoutReturn zero zero (suc c) d ()
fourOutwardDiodesNoWorkWithoutReturn zero zero zero (suc d) ()

-- Inverse warning: equal opposite half-voltages with respect to M can
-- arise from both a genuine ideal centre-tap and a FLOATING source with
-- equal capacitive reference paths to M, in the unloaded linear model.
data ApparentMidpointMechanism : Set where
  hardSymmetricCentreTap floatingSymmetricCapacitance : ApparentMidpointMechanism

data VoltageSignature : Set where
  equalOppositeHalfVoltages : VoltageSignature

unloadedSignature : ApparentMidpointMechanism → VoltageSignature
unloadedSignature hardSymmetricCentreTap = equalOppositeHalfVoltages
unloadedSignature floatingSymmetricCapacitance = equalOppositeHalfVoltages

distinctMechanisms :
  hardSymmetricCentreTap ≡ floatingSymmetricCapacitance → ⊥
distinctMechanisms ()

noUniqueCentreTapFromUnloadedVoltage :
  (infer : VoltageSignature → ApparentMidpointMechanism) →
  ((m : ApparentMidpointMechanism) →
   infer (unloadedSignature m) ≡ m) → ⊥
noUniqueCentreTapFromUnloadedVoltage infer agrees =
  distinctMechanisms
    (trans (sym (agrees hardSymmetricCentreTap))
           (agrees floatingSymmetricCapacitance))

-- Reuse existing 369/27 part-pin owners instead of inventing real pins.
-- These are NOT inhabited factual Filsinger hardware claims; the
-- source-attestation and signed-energy obligations remain unclosed.
record OriginalSameRevisionPinReturnCut : Set₁ where
  field
    originalSourceCircuit : Original.SourceBoundCircuit
    claimedCoilOwner : CoilOwner
    claimedReturn : ReturnClass
    actualNSTMidpointPin : Original.Pin
    actualSelectedCoilFirstPin : Original.Pin
    actualSelectedCoilSecondPin : Original.Pin
    actualCapacitorFirstPin : Original.Pin
    actualCapacitorSecondPin : Original.Pin
    actualJoinedPositivePin : Original.Pin
    originalPinAndSameReelAttestation : Set
    originalPinAndSameReelWitness : originalPinAndSameReelAttestation
    originalSignedSourceWorkAttestation : Set
    originalSignedSourceWorkWitness : originalSignedSourceWorkAttestation
