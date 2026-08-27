module DASHI.Physics.YangMills.YangMillsLocalCurrentMicrocausalShellExact where

------------------------------------------------------------------------
-- ROUND86: LOCAL CURRENT + MICROCAUSALITY -> OUTER-SHELL COMMUTATOR VANISHES
--
-- PRIMARY CALIBRATION
--
-- Manfred Requardt,
-- "Symmetry Conservation and Integrals over Local Charge Densities in Quantum
-- Field Theory", Communications in Mathematical Physics 50 (1976), 259--263.
-- DOI: 10.1007/BF01609406.
--
-- Konrad Osterwalder and Robert Schrader,
-- "Axioms for Euclidean Green's Functions",
-- Communications in Mathematical Physics 31 (1973), 83--112.
-- DOI: 10.1007/BF01645738.
--
-- Konrad Osterwalder and Robert Schrader,
-- "Axioms for Euclidean Green's Functions II",
-- Communications in Mathematical Physics 42 (1975), 281--305.
-- DOI: 10.1007/BF01608978.
--
-- MATHEMATICAL ROLE
--
-- The Round86 local-charge compiler still exposed
-- `outerShellVanishesBeyondSupport` as a physical premise.  Once T_{0 nu} is an
-- actual LOCAL continuum field, that premise is not another independent YM
-- estimate.  At equal time, if the annular current shell lies outside the local
-- observable support, microcausality makes its commutator vanish.
--
-- This module packages precisely that implication.  The remaining same-theory
-- inputs are therefore:
--
--   * geometry: the chosen outer shell is spacelike/equal-time separated from A;
--   * locality/microcausality of the RENORMALIZED stress-current field;
--   * additive decomposition of nested cutoff charges.
--
-- The first is support geometry and the second belongs to the local-field/Ward
-- construction itself.  No separate nonperturbative cutoff-decay estimate is
-- required merely to kill a spacelike outer shell.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat.Base using (_≤_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.YangMillsLocalChargeCommutatorToCoreStabilizationExact as Charge

record MicrocausalLocalCurrentShell
    (Observable Current Target : Set) : Set₁ where
  field
    supportRadius : Observable → Nat

    zero : Target
    _⊕_ : Target → Target → Target
    rightIdentity : ∀ value → value ⊕ zero ≡ value

    cutoffCommutator : Nat → Observable → Target
    outerShellCurrent : Nat → Nat → Current
    currentCommutator : Current → Observable → Target

    cutoffSplitsIntoInnerPlusOuter :
      ∀ observable inner outer →
      inner ≤ outer →
      cutoffCommutator outer observable
      ≡ cutoffCommutator inner observable
        ⊕ currentCommutator (outerShellCurrent inner outer) observable

    SpacelikeSeparated : Current → Observable → Set

    outerShellSeparatedBeyondSupport :
      ∀ observable inner outer →
      supportRadius observable ≤ inner →
      inner ≤ outer →
      SpacelikeSeparated (outerShellCurrent inner outer) observable

    -- Local-field microcausality on the actual reconstructed continuum family.
    microcausalCommutatorZero :
      ∀ current observable →
      SpacelikeSeparated current observable →
      currentCommutator current observable ≡ zero

open MicrocausalLocalCurrentShell public

outerShellCommutatorZeroFromMicrocausality :
  ∀ {Observable Current Target}
    (dataSet : MicrocausalLocalCurrentShell Observable Current Target)
    observable inner outer →
  supportRadius dataSet observable ≤ inner →
  inner ≤ outer →
  currentCommutator dataSet (outerShellCurrent dataSet inner outer) observable
    ≡ zero dataSet
outerShellCommutatorZeroFromMicrocausality dataSet observable inner outer supportInside nested =
  microcausalCommutatorZero dataSet
    (outerShellCurrent dataSet inner outer)
    observable
    (outerShellSeparatedBeyondSupport dataSet observable inner outer supportInside nested)

microcausalShellToCutoffCommutatorShell :
  ∀ {Observable Current Target} →
  MicrocausalLocalCurrentShell Observable Current Target →
  Charge.LocalCutoffCommutatorShell Observable Target
microcausalShellToCutoffCommutatorShell dataSet = record
  { Charge.LocalCutoffCommutatorShell.supportRadius = supportRadius dataSet
  ; Charge.LocalCutoffCommutatorShell.zero = zero dataSet
  ; Charge.LocalCutoffCommutatorShell._⊕_ = _⊕_ dataSet
  ; Charge.LocalCutoffCommutatorShell.rightIdentity = rightIdentity dataSet
  ; Charge.LocalCutoffCommutatorShell.cutoffCommutator = cutoffCommutator dataSet
  ; Charge.LocalCutoffCommutatorShell.outerShellCommutator =
      λ inner outer observable →
        currentCommutator dataSet (outerShellCurrent dataSet inner outer) observable
  ; Charge.LocalCutoffCommutatorShell.cutoffSplitsIntoInnerPlusOuter =
      cutoffSplitsIntoInnerPlusOuter dataSet
  ; Charge.LocalCutoffCommutatorShell.outerShellVanishesBeyondSupport =
      outerShellCommutatorZeroFromMicrocausality dataSet
  }

microcausalOuterShellCompilerLevel : ProofLevel
microcausalOuterShellCompilerLevel = machineChecked

-- Once the stress current has already been constructed as a local continuum
-- field satisfying the accepted locality axiom, the remaining cutoff-specific
-- premise is only the nested-charge decomposition/support geometry.  It should
-- not be counted as a separate four-dimensional decay theorem.
physicalRenormalizedStressCurrentLocalityAndShellGeometryLevel : ProofLevel
physicalRenormalizedStressCurrentLocalityAndShellGeometryLevel = conditional
