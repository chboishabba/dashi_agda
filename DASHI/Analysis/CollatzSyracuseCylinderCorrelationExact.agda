module DASHI.Analysis.CollatzSyracuseCylinderCorrelationExact where

------------------------------------------------------------------------
-- REPAIRED FINITE CORRELATION TRANSPORT
--
-- Any consumer must retain the finite level-dependent prefactor.  The refuted
-- unit-prefactor one-step contraction is not an admissible source.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)

import DASHI.Analysis.CollatzSyracuseFiniteTransferSameObjectWeldExact as Transfer
import DASHI.Analysis.CollatzSyracuseCylinderInterfaceMatchExact as Interface

record CylinderCorrelationSource : Set₁ where
  field
    transferWeld : Transfer.SyracuseFiniteTransferWeld
    level : Nat
    transientPrefactor : Nat
    decayNumerator : Nat → Nat
    supportedCorrelationBound : (separation : Nat) → Set

open CylinderCorrelationSource public

record CorrelationBoundary : Set where
  constructor correlationBoundary
  field
    unitPrefactorRestored : Nat
    finitePrefactorRetained : Nat
    supportedObservableRequired : Nat

canonicalCorrelationBoundary : CorrelationBoundary
canonicalCorrelationBoundary = correlationBoundary 0 1 1
