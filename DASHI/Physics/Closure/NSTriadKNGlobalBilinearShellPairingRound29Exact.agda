module DASHI.Physics.Closure.NSTriadKNGlobalBilinearShellPairingRound29Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean-Michel Bony.
-- Title: "Calcul symbolique et propagation des singularites pour les
-- equations aux derivees partielles non lineaires".
-- DOI: 10.24033/asens.1404.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- DASHI CONTRIBUTION
--
-- One global physical output-fibre pairing is the authority. The HH/LH/HL/CC
-- and differentiated-commutator coordinates are derived from that single
-- pairing. A later trajectory only supplies the chain rule and viscous term;
-- it cannot change the static source signs or multiplicities.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _+_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNLuoFiniteBonyFourClassAccountingExact as Four
import DASHI.Physics.Closure.NSTriadKNLuoPhysicalFiveClassSumRound25Exact as Five

record StaticPhysicalShellPairing : Set where
  constructor static-physical-shell-pairing
  field
    cutoff : Nat
    output : Z3.FourierMode
    triadValue : Physical.PhysicalTriadIncidence → ℚ
    commutatorValue : Z3.FourierMode → ℚ
    globalBilinearPairing : ℚ
    globalPairingMeaning :
      globalBilinearPairing
      ≡ Five.fiveSourceTotal cutoff output triadValue commutatorValue

open StaticPhysicalShellPairing public

hhValue : StaticPhysicalShellPairing → ℚ
hhValue pairing =
  Four.highHighToLowSum
    (Five.physicalTaggedOutputFiber
      (cutoff pairing) (output pairing) (triadValue pairing))

lhValue : StaticPhysicalShellPairing → ℚ
lhValue pairing =
  Four.lowHighSum
    (Five.physicalTaggedOutputFiber
      (cutoff pairing) (output pairing) (triadValue pairing))

hlValue : StaticPhysicalShellPairing → ℚ
hlValue pairing =
  Four.highLowSum
    (Five.physicalTaggedOutputFiber
      (cutoff pairing) (output pairing) (triadValue pairing))

ccValue : StaticPhysicalShellPairing → ℚ
ccValue pairing =
  Four.comparableSum
    (Five.physicalTaggedOutputFiber
      (cutoff pairing) (output pairing) (triadValue pairing))

comValue : StaticPhysicalShellPairing → ℚ
comValue pairing = commutatorValue pairing (output pairing)

globalPairingFiveSourceIdentity :
  (pairing : StaticPhysicalShellPairing) →
  globalBilinearPairing pairing
  ≡ hhValue pairing + lhValue pairing + hlValue pairing
    + ccValue pairing + comValue pairing
globalPairingFiveSourceIdentity pairing =
  trans
    (globalPairingMeaning pairing)
    (Five.physicalFiveSourcePartitionExact
      (cutoff pairing)
      (output pairing)
      (triadValue pairing)
      (commutatorValue pairing))

record DynamicPhysicalShellBalance : Set where
  constructor dynamic-physical-shell-balance
  field
    staticPairing : StaticPhysicalShellPairing
    energyDerivative diffusion lowerBoundary upperBoundary : ℚ
    globalDynamicBalance :
      energyDerivative + diffusion
      ≡ globalBilinearPairing staticPairing
        + lowerBoundary + upperBoundary

open DynamicPhysicalShellBalance public

physicalShellBalanceExpandsOnce :
  (balance : DynamicPhysicalShellBalance) →
  energyDerivative balance + diffusion balance
  ≡
    hhValue (staticPairing balance)
    + lhValue (staticPairing balance)
    + hlValue (staticPairing balance)
    + ccValue (staticPairing balance)
    + comValue (staticPairing balance)
    + lowerBoundary balance
    + upperBoundary balance
physicalShellBalanceExpandsOnce balance =
  trans
    (globalDynamicBalance balance)
    (trans
      (cong
        (λ source → source + lowerBoundary balance + upperBoundary balance)
        (globalPairingFiveSourceIdentity (staticPairing balance)))
      (solve
        ( hhValue (staticPairing balance)
        ∷ lhValue (staticPairing balance)
        ∷ hlValue (staticPairing balance)
        ∷ ccValue (staticPairing balance)
        ∷ comValue (staticPairing balance)
        ∷ lowerBoundary balance
        ∷ upperBoundary balance
        ∷ [])))
  where
  open import Relation.Binary.PropositionalEquality using (cong)

staticPhysicalShellPairingClosed : Bool
staticPhysicalShellPairingClosed = true

physicalTimeDependentShellBalanceInstantiated : Bool
physicalTimeDependentShellBalanceInstantiated = false

staticPhysicalShellPairingClosedIsTrue :
  staticPhysicalShellPairingClosed ≡ true
staticPhysicalShellPairingClosedIsTrue = refl
