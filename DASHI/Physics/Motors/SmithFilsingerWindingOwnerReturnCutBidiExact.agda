module DASHI.Physics.Motors.SmithFilsingerWindingOwnerReturnCutBidiExact where

-- User-transcribed Filsinger midpoint/spark proposal: accessible NST
-- midpoint M; capacitor across "the one coil you want"; 2 diodes off
-- cap and 2 "off here", all forward into joined positives P; return
-- "midpoint, earth, ground"; and "half the potential of the big coil".
-- Selected coil U-V is NOT thereby proved to equal NST full A-B,
-- half A-M, or separately documented Smith/Kelly L2. The full wiring,
-- phase, source work and actual reel's pin map remain unverified.
--
-- CONDITIONAL physical cut: when a U/V floating source island has
-- ONLY four forward-only U/V->P diode edges crossing to external nodes,
-- no other galvanic/displacement/return path, KCL + nonnegative diode
-- current yields ZERO all four package currents. A capacitive M return
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

-- Current unit Nat enforces forward-only nonnegativity. Island KCL
-- a+(b+(c+d))=0 is an explicit condition, NOT historical source evidence.
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
