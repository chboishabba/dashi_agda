module DASHI.Analysis.CollatzSyracusePrefixAbsorptionWeldExact where

------------------------------------------------------------------------
-- INTEGER SYRACUSE PREFIX <-> FINITE CYLINDER ABSORPTION WELD
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)

import DASHI.Core.FinitePrefixAbsorptionExact as Prefix
import DASHI.NumberTheory.Collatz.SyracuseExact as Syracuse
import DASHI.NumberTheory.Collatz.SyracuseParityCylinderExact as Cylinder
import DASHI.Analysis.CollatzSyracuseSamplingPushforwardExact as Sampling

record SyracusePrefixAbsorptionSource : Set₁ where
  field
    cylinders : Cylinder.ParityCylinderSource
    State Word : Set
    sourceState : Syracuse.PositiveNat → State
    sourceWord : Word → Set
    killedPrefix : Word → State → Set
    extendWord : Word → Word → Word
    killedExtension :
      (prefix suffix : Word) →
      (state : State) →
      killedPrefix prefix state →
      killedPrefix (extendWord prefix suffix) state
    integerPrefixHitImpliesKilledCylinder :
      (x : Syracuse.PositiveNat) → (word : Word) → Set

open SyracusePrefixAbsorptionSource public

asPrefixAbsorptionReceipt :
  (source : SyracusePrefixAbsorptionSource) →
  Prefix.PrefixAbsorptionReceipt
asPrefixAbsorptionReceipt source = record
  { Prefix.State = State source
  ; Prefix.Word = Word source
  ; Prefix.killed = killedPrefix source
  ; Prefix.extend = extendWord source
  ; Prefix.killedExtension = killedExtension source
  }

record PrefixWeldBoundary : Set where
  constructor prefixWeldBoundary
  field
    endpointHitAloneSuffices : Nat
    actualPrefixSemanticsRequired : Nat
    killedPrefixPersistsUnderExtension : Nat

canonicalPrefixWeldBoundary : PrefixWeldBoundary
canonicalPrefixWeldBoundary = prefixWeldBoundary 0 1 1
