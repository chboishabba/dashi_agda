module DASHI.Crypto.MLKEMNTTPriorCutNoGoExact where

------------------------------------------------------------------------
-- NO NONTRIVIAL DISCONNECTED CUT INSIDE ONE NTT PARITY FAMILY
--
-- Builds on MLKEMNTTDataflowCouplingExact.  Every constant-part NTT scalar
-- coordinate structurally depends on every even source coefficient; every
-- linear-part NTT scalar coordinate structurally depends on every odd source
-- coefficient.  Therefore a source-variable-disjoint decomposition cannot
-- split one parity family into two inhabited sides.
--
-- This is a dataflow/separator no-go, not a statistical-independence theorem
-- and not a cryptographic hardness theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

import DASHI.Crypto.MLKEMNTTDataflowCouplingExact as NTT

------------------------------------------------------------------------
-- A proposed disconnected cut for one scalar component.
------------------------------------------------------------------------

data Side : Set where
  leftSide rightSide : Side

record DisconnectedComponentCut
    (component : NTT.ResidueComponent) : Set₁ where
  constructor disconnectedComponentCut
  field
    side : Nat → Side
    noCrossSharedDependency : ∀ {i j} →
      side i ≡ leftSide →
      side j ≡ rightSide →
      NTT.SharesSourceDependency
        (NTT.scalarCoordinate i component)
        (NTT.scalarCoordinate j component) → ⊥

open DisconnectedComponentCut public

record NontrivialCutWitness
    {component : NTT.ResidueComponent}
    (cut : DisconnectedComponentCut component) : Set where
  constructor nontrivialCutWitness
  field
    leftIndex rightIndex : Nat
    leftReallyLeft : side cut leftIndex ≡ leftSide
    rightReallyRight : side cut rightIndex ≡ rightSide

open NontrivialCutWitness public

------------------------------------------------------------------------
-- Constant and linear families are each complete under shared-source
-- dependency, hence no proposed disconnected cut can have both sides inhabited.
------------------------------------------------------------------------

constantComponentHasNoNontrivialDisconnectedCut :
  (cut : DisconnectedComponentCut NTT.constantPart) →
  NontrivialCutWitness cut → ⊥
constantComponentHasNoNontrivialDisconnectedCut cut witness =
  noCrossSharedDependency cut
    (leftReallyLeft witness)
    (rightReallyRight witness)
    (NTT.constantCoordinatesShareSource
      (leftIndex witness) (rightIndex witness))

linearComponentHasNoNontrivialDisconnectedCut :
  (cut : DisconnectedComponentCut NTT.linearPart) →
  NontrivialCutWitness cut → ⊥
linearComponentHasNoNontrivialDisconnectedCut cut witness =
  noCrossSharedDependency cut
    (leftReallyLeft witness)
    (rightReallyRight witness)
    (NTT.linearCoordinatesShareSource
      (leftIndex witness) (rightIndex witness))

------------------------------------------------------------------------
-- The useful blue-team conclusion is narrow: any NTT-based decomposition that
-- claims source-variable-disjoint local prior lanes must cross or condition on
-- these globally shared parity families.  It may still admit a useful bounded
-- separator under stronger structure, but disconnected factorisation is ruled
-- out at this structural dependency level.
------------------------------------------------------------------------
