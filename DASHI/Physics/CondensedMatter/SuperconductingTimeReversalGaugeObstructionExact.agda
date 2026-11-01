module DASHI.Physics.CondensedMatter.SuperconductingTimeReversalGaugeObstructionExact where

------------------------------------------------------------------------
-- Reusable superconducting TR/gauge obstruction.
--
-- A superconducting order parameter is physically unchanged by a global
-- U(1) gauge phase.  Therefore "time-reversal invariant" means invariant
-- only up to such a gauge action.  Any observable/witness q that
--
--   * is invariant under global gauge,
--   * is odd under time reversal, and
--   * has no nonzero fixed point under q |-> -q,
--
-- must vanish for every time-reversal-invariant-up-to-gauge state.
--
-- This is deliberately independent of YbSb2 and of any particular matrix
-- representation.  It is intended as the reusable theorem consumed by
-- concrete INT, chiral, and other TRSB superconducting owners.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

record TROddGaugeWitnessSystem : Set₁ where
  field
    State Gauge Witness : Set

    gaugeAction : Gauge → State → State
    timeReverse : State → State

    witness : State → Witness
    zeroWitness : Witness
    negateWitness : Witness → Witness

    gaugeInvariant :
      (g : Gauge) (x : State) →
      witness (gaugeAction g x) ≡ witness x

    timeReverseOdd :
      (x : State) →
      witness (timeReverse x) ≡ negateWitness (witness x)

    fixedPointIsZero :
      (w : Witness) →
      w ≡ negateWitness w →
      w ≡ zeroWitness

open TROddGaugeWitnessSystem public

TRGaugeEquivalent :
  (S : TROddGaugeWitnessSystem) →
  State S → Set
TRGaugeEquivalent S x =
  Σ (Gauge S) λ g →
    timeReverse S x ≡ gaugeAction S g x

WitnessNonzero :
  (S : TROddGaugeWitnessSystem) →
  State S → Set
WitnessNonzero S x =
  witness S x ≡ zeroWitness S → ⊥

trGaugeEquivalentForcesWitnessZero :
  (S : TROddGaugeWitnessSystem) →
  (x : State S) →
  TRGaugeEquivalent S x →
  witness S x ≡ zeroWitness S
trGaugeEquivalentForcesWitnessZero S x (g , trEqualsGauge) =
  fixedPointIsZero S (witness S x) fixed
  where
    reverseToOriginal :
      witness S (timeReverse S x) ≡ witness S x
    reverseToOriginal =
      trans
        (cong (witness S) trEqualsGauge)
        (gaugeInvariant S g x)

    negToOriginal :
      negateWitness S (witness S x) ≡ witness S x
    negToOriginal =
      trans
        (sym (timeReverseOdd S x))
        reverseToOriginal

    fixed :
      witness S x ≡ negateWitness S (witness S x)
    fixed = sym negToOriginal

nonzeroTROddWitnessObstructsTRGaugeEquivalence :
  (S : TROddGaugeWitnessSystem) →
  (x : State S) →
  WitnessNonzero S x →
  TRGaugeEquivalent S x →
  ⊥
nonzeroTROddWitnessObstructsTRGaugeEquivalence S x nonzero trEquivalent =
  nonzero (trGaugeEquivalentForcesWitnessZero S x trEquivalent)
