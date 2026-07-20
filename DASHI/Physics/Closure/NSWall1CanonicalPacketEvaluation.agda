module DASHI.Physics.Closure.NSWall1CanonicalPacketEvaluation where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.Closure.NSIntegerFourierLattice
open import DASHI.Physics.Closure.NSWall1CanonicalModePacket
open import DASHI.Physics.Closure.NSWall1ExactEvaluationCarrier

------------------------------------------------------------------------
-- Exact evaluation data for the six-mode canonical Wall-1 packet.
--
-- The global evaluation functions remain total on Z^3, but every value needed
-- by the canonical packet is fixed by proof-relevant equations below.
------------------------------------------------------------------------

record CanonicalPacketScalars
    {s : Level}
    {Scalar : Set s}
    (A : ExactScalarAlgebra Scalar) : Set (lsuc s) where
  field
    half : Scalar
    halfPlusHalf : add A half half ≡ one A

open CanonicalPacketScalars public

record CanonicalPacketEvaluation
    {s : Level}
    {Scalar : Set s}
    (A : ExactScalarAlgebra Scalar)
    (S : CanonicalPacketScalars A)
    (E : ExactFourierEvaluation Scalar A) : Set (lsuc s) where
  field
    inverseNorm100 : inverseNormSquared E p100 ≡ one A
    inverseNorm010 : inverseNormSquared E p010 ≡ one A
    inverseNorm001 : inverseNormSquared E p001 ≡ one A

    inverseNorm110 : inverseNormSquared E p110 ≡ half S
    inverseNorm101 : inverseNormSquared E p101 ≡ half S
    inverseNorm011 : inverseNormSquared E p011 ≡ half S

    delta100100 : modeDelta E p100 p100 ≡ one A
    delta010010 : modeDelta E p010 p010 ≡ one A
    delta001001 : modeDelta E p001 p001 ≡ one A
    delta110110 : modeDelta E p110 p110 ≡ one A
    delta101101 : modeDelta E p101 p101 ≡ one A
    delta011011 : modeDelta E p011 p011 ≡ one A

    delta100010 : modeDelta E p100 p010 ≡ zero A
    delta100001 : modeDelta E p100 p001 ≡ zero A
    delta010100 : modeDelta E p010 p100 ≡ zero A
    delta010001 : modeDelta E p010 p001 ≡ zero A
    delta001100 : modeDelta E p001 p100 ≡ zero A
    delta001010 : modeDelta E p001 p010 ≡ zero A

    delta110101 : modeDelta E p110 p101 ≡ zero A
    delta110011 : modeDelta E p110 p011 ≡ zero A
    delta101110 : modeDelta E p101 p110 ≡ zero A
    delta101011 : modeDelta E p101 p011 ≡ zero A
    delta011110 : modeDelta E p011 p110 ≡ zero A
    delta011101 : modeDelta E p011 p101 ≡ zero A

    lowHighDeltaZero :
      ∀ low high →
      ((low ≡ p100) ⊎ (low ≡ p010) ⊎ (low ≡ p001)) →
      ((high ≡ p110) ⊎ (high ≡ p101) ⊎ (high ≡ p011)) →
      modeDelta E low high ≡ zero A

open import Data.Sum.Base using (_⊎_)
open CanonicalPacketEvaluation public
