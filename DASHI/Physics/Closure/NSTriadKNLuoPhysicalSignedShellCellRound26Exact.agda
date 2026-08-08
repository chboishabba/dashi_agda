module DASHI.Physics.Closure.NSTriadKNLuoPhysicalSignedShellCellRound26Exact where

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
-- Author: Xiaoyutao Luo.
-- Title: "A Beale-Kato-Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- DOI: 10.1007/s00021-019-0411-z.
--
-- DASHI CONTRIBUTION
--
-- Round 25 proved that the actual physical output fibre evaluates exactly as
--
--   HH + LH + HL + CC + Com(output).
--
-- Round 26's signed critical ledger must not be populated by unrelated scalar
-- fields.  This file constructs one SignedCriticalShellCell directly from the
-- literal physical output-fibre evaluator.  The caller supplies only the
-- genuine shell energy balance
--
--   energyRate + dissipation
--     = physicalFiveSourceTotal + lowerBoundary + upperBoundary.
--
-- The five signed source coordinates are then forced by the Round 25 physical
-- partition; they cannot be chosen independently.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using (_∷_; [])
open import Data.Rational.Base using (ℚ; _+_)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNLuoFiniteBonyFourClassAccountingExact as Four
import DASHI.Physics.Closure.NSTriadKNLuoPhysicalFiveClassSumRound25Exact as PhysicalSum
import DASHI.Physics.Closure.NSTriadKNLuoSignedCriticalLedgerRound26Exact as Ledger

record PhysicalSignedShellInputs : Set where
  constructor physical-signed-shell-inputs
  field
    cutoff : Nat
    output : Z3.FourierMode
    triadValue : Physical.PhysicalTriadIncidence → ℚ
    commutatorValue : Z3.FourierMode → ℚ

    criticalWeight : ℚ
    energyRate : ℚ
    dissipation : ℚ
    lowerBoundary : ℚ
    upperBoundary : ℚ

    physicalShellBalance :
      energyRate + dissipation
      ≡
      PhysicalSum.fiveSourceTotal
        cutoff output triadValue commutatorValue
      + lowerBoundary + upperBoundary

open PhysicalSignedShellInputs public

physicalHH physicalLH physicalHL physicalCC physicalCom :
  PhysicalSignedShellInputs → ℚ
physicalHH I =
  Four.highHighToLowSum
    (PhysicalSum.physicalTaggedOutputFiber
      (cutoff I) (output I) (triadValue I))
physicalLH I =
  Four.lowHighSum
    (PhysicalSum.physicalTaggedOutputFiber
      (cutoff I) (output I) (triadValue I))
physicalHL I =
  Four.highLowSum
    (PhysicalSum.physicalTaggedOutputFiber
      (cutoff I) (output I) (triadValue I))
physicalCC I =
  Four.comparableSum
    (PhysicalSum.physicalTaggedOutputFiber
      (cutoff I) (output I) (triadValue I))
physicalCom I = commutatorValue I (output I)

physicalSignedShellBalance :
  (I : PhysicalSignedShellInputs) →
  energyRate I + dissipation I
  ≡
  physicalHH I + physicalLH I + physicalHL I + physicalCC I
  + physicalCom I + lowerBoundary I + upperBoundary I
physicalSignedShellBalance I =
  transPhysicalBalance
  where
  partition :
    PhysicalSum.fiveSourceTotal
      (cutoff I) (output I) (triadValue I) (commutatorValue I)
    ≡
    physicalHH I + physicalLH I + physicalHL I + physicalCC I
    + physicalCom I
  partition =
    PhysicalSum.physicalFiveSourcePartitionExact
      (cutoff I) (output I) (triadValue I) (commutatorValue I)

  transPhysicalBalance :
    energyRate I + dissipation I
    ≡
    physicalHH I + physicalLH I + physicalHL I + physicalCC I
    + physicalCom I + lowerBoundary I + upperBoundary I
  transPhysicalBalance
    rewrite physicalShellBalance I
          | partition =
    solve
      ( physicalHH I ∷ physicalLH I ∷ physicalHL I ∷ physicalCC I
      ∷ physicalCom I ∷ lowerBoundary I ∷ upperBoundary I ∷ [])

physicalSignedCriticalShellCell :
  PhysicalSignedShellInputs → Ledger.SignedCriticalShellCell
physicalSignedCriticalShellCell I =
  Ledger.signed-critical-shell-cell
    (criticalWeight I)
    (energyRate I)
    (dissipation I)
    (physicalHH I)
    (physicalLH I)
    (physicalHL I)
    (physicalCC I)
    (physicalCom I)
    (lowerBoundary I)
    (upperBoundary I)
    (physicalSignedShellBalance I)

physicalShellCellSourcesAreForced :
  (I : PhysicalSignedShellInputs) →
  Ledger.HHsource (physicalSignedCriticalShellCell I) ≡ physicalHH I
physicalShellCellSourcesAreForced I = refl
