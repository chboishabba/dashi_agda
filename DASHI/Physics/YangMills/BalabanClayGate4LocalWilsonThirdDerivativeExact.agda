module DASHI.Physics.YangMills.BalabanClayGate4LocalWilsonThirdDerivativeExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayGate4PlaquetteDerivativeCombinatoricsExact as Plaquette

------------------------------------------------------------------------
-- Local Wilson third-derivative envelope in four dimensions.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- A bond in four dimensions belongs to 2(d-1)=6 unoriented plaquettes.  Thus
-- the local action third derivative is bounded by six copies of the
-- beta-weighted plaquette third-derivative envelope.
------------------------------------------------------------------------

plaquettesPerUnorientedBond4D : Nat
plaquettesPerUnorientedBond4D = 6

plaquettesPerUnorientedBond4DExact :
  plaquettesPerUnorientedBond4D ≡ 6
plaquettesPerUnorientedBond4DExact = refl

record WilsonThirdDerivativeData (Bound : Set) : Set₁ where
  field
    linkEnvelope : Plaquette.LinkExponentialDerivativeEnvelope Bound
    beta : Bound

open WilsonThirdDerivativeData public

singlePlaquetteWilsonThirdEnvelope :
  ∀ {Bound} → WilsonThirdDerivativeData Bound → Bound
singlePlaquetteWilsonThirdEnvelope dataSet =
  Plaquette.multiply (Plaquette.algebra (linkEnvelope dataSet))
    (beta dataSet)
    (Plaquette.plaquetteThirdDerivativeEnvelope (linkEnvelope dataSet))

localBondWilsonThirdEnvelope :
  ∀ {Bound} → WilsonThirdDerivativeData Bound → Bound
localBondWilsonThirdEnvelope dataSet =
  Plaquette.natScale
    (Plaquette.algebra (linkEnvelope dataSet))
    (singlePlaquetteWilsonThirdEnvelope dataSet)
    plaquettesPerUnorientedBond4D

record PhysicalLocalWilsonThirdDerivative
    {Field Variation Bound : Set}
    (dataSet : WilsonThirdDerivativeData Bound) : Set₁ where
  field
    localAction : Field → Bound
    thirdDerivative : Field → Variation → Variation → Variation → Bound
    ThirdDerivativeNormBelow : Bound → Bound → Set

    thirdDerivativeBelowLocalEnvelope : ∀ field first second third →
      ThirdDerivativeNormBelow
        (thirdDerivative field first second third)
        (localBondWilsonThirdEnvelope dataSet)

open PhysicalLocalWilsonThirdDerivative public

fourDimensionalPlaquetteOverlapLevel : ProofLevel
fourDimensionalPlaquetteOverlapLevel = computed

localWilsonThirdEnvelopeConstructionLevel : ProofLevel
localWilsonThirdEnvelopeConstructionLevel = machineChecked

physicalLocalWilsonThirdDerivativeInputsLevel : ProofLevel
physicalLocalWilsonThirdDerivativeInputsLevel = conditional
