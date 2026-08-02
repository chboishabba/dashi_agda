module DASHI.Physics.YangMills.BalabanClayGate4PlaquetteDerivativeCombinatoricsExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Exact derivative-term combinatorics for a four-link plaquette product.
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary Introduction",
-- second edition, Springer (2015).
-- DOI: 10.1007/978-3-319-13467-3.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- For P=U1 U2 U3^{-1} U4^{-1}:
--
--   D P:   4 single insertions;
--   D2 P:  4 same-link second derivatives + 12 ordered cross insertions;
--   D3 P:  4 third derivatives
--           + 36 choices of a second derivative and a first derivative
--           + 24 three-distinct-link insertions.
------------------------------------------------------------------------

firstDerivativeInsertionCount : Nat
firstDerivativeInsertionCount = 4

secondDerivativeDiagonalCount secondDerivativeCrossCount : Nat
secondDerivativeDiagonalCount = 4
secondDerivativeCrossCount = 12

secondDerivativeTotalCount : Nat
secondDerivativeTotalCount = 16

thirdDerivativeSingleCount thirdDerivativeDoubleSingleCount : Nat
thirdDerivativeSingleCount = 4
thirdDerivativeDoubleSingleCount = 36

thirdDerivativeThreeSingleCount thirdDerivativeTotalCount : Nat
thirdDerivativeThreeSingleCount = 24
thirdDerivativeTotalCount = 64

firstDerivativeInsertionCountExact :
  firstDerivativeInsertionCount ≡ 4
firstDerivativeInsertionCountExact = refl

secondDerivativeTotalCountExact :
  secondDerivativeDiagonalCount + secondDerivativeCrossCount
  ≡ secondDerivativeTotalCount
secondDerivativeTotalCountExact = refl

thirdDerivativeTotalCountExact :
  thirdDerivativeSingleCount
  + thirdDerivativeDoubleSingleCount
  + thirdDerivativeThreeSingleCount
  ≡ thirdDerivativeTotalCount
thirdDerivativeTotalCountExact = refl

record DerivativeEnvelopeAlgebra (Bound : Set) : Set₁ where
  field
    zero : Bound
    add multiply : Bound → Bound → Bound

open DerivativeEnvelopeAlgebra public

natScale :
  ∀ {Bound} → DerivativeEnvelopeAlgebra Bound → Bound → Nat → Bound
natScale algebra value zero = zero algebra
natScale algebra value (suc count) =
  add algebra value (natScale algebra value count)

record LinkExponentialDerivativeEnvelope (Bound : Set) : Set₁ where
  field
    algebra : DerivativeEnvelopeAlgebra Bound
    C1 C2 C3 : Bound

open LinkExponentialDerivativeEnvelope public

plaquetteFirstDerivativeEnvelope :
  ∀ {Bound} → LinkExponentialDerivativeEnvelope Bound → Bound
plaquetteFirstDerivativeEnvelope envelope =
  natScale (algebra envelope) (C1 envelope)
    firstDerivativeInsertionCount

plaquetteSecondDerivativeEnvelope :
  ∀ {Bound} → LinkExponentialDerivativeEnvelope Bound → Bound
plaquetteSecondDerivativeEnvelope envelope =
  add (algebra envelope)
    (natScale (algebra envelope) (C2 envelope)
      secondDerivativeDiagonalCount)
    (natScale (algebra envelope)
      (multiply (algebra envelope) (C1 envelope) (C1 envelope))
      secondDerivativeCrossCount)

plaquetteThirdDerivativeEnvelope :
  ∀ {Bound} → LinkExponentialDerivativeEnvelope Bound → Bound
plaquetteThirdDerivativeEnvelope envelope =
  add (algebra envelope)
    (natScale (algebra envelope) (C3 envelope)
      thirdDerivativeSingleCount)
    (add (algebra envelope)
      (natScale (algebra envelope)
        (multiply (algebra envelope) (C2 envelope) (C1 envelope))
        thirdDerivativeDoubleSingleCount)
      (natScale (algebra envelope)
        (multiply (algebra envelope) (C1 envelope)
          (multiply (algebra envelope) (C1 envelope) (C1 envelope)))
        thirdDerivativeThreeSingleCount))

record PhysicalPlaquetteDerivativeIdentification
    {Field Variation Bound : Set}
    (envelope : LinkExponentialDerivativeEnvelope Bound) : Set₁ where
  field
    plaquette : Field → Field
    firstDerivative : Field → Variation → Field
    secondDerivative : Field → Variation → Variation → Field
    thirdDerivative : Field → Variation → Variation → Variation → Field

    firstDerivativeNormBound : Set
    firstDerivativeNormBoundEvidence : firstDerivativeNormBound

    secondDerivativeNormBound : Set
    secondDerivativeNormBoundEvidence : secondDerivativeNormBound

    thirdDerivativeNormBound : Set
    thirdDerivativeNormBoundEvidence : thirdDerivativeNormBound

open PhysicalPlaquetteDerivativeIdentification public

plaquetteDerivativeTermCountsLevel : ProofLevel
plaquetteDerivativeTermCountsLevel = computed

plaquetteDerivativeEnvelopeConstructionLevel : ProofLevel
plaquetteDerivativeEnvelopeConstructionLevel = machineChecked

physicalLinkExponentialDerivativeInputsLevel : ProofLevel
physicalLinkExponentialDerivativeInputsLevel = conditional

physicalPlaquetteDerivativeIdentificationInputsLevel : ProofLevel
physicalPlaquetteDerivativeIdentificationInputsLevel = conditional
