module DASHI.Physics.YangMills.BalabanPath4SU2PhysicalTangentExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational using (ℚ; 0ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
open import DASHI.Physics.YangMills.BalabanPath4AxisAverageExact using
  (side4; average0123)
open import DASHI.Physics.YangMills.BalabanPath4BondHodgeCoercivityExact

------------------------------------------------------------------------
-- The literal side-four SU(2) tangent carrier.
--
-- A tangent vector has three Lie-algebra components.  Each component is the
-- repository's existing positive-axis BondField: one value for (site, axis),
-- with no separate negative-orientation slot and therefore no hidden factor of
-- two.  The component projection below is exactly h^a_mu(x).
------------------------------------------------------------------------

data SU2Component : Set where
  component1 component2 component3 : SU2Component

PhysicalSU2Tangent4 : Set
PhysicalSU2Tangent4 = SU2Component → RationalBondField4

EncodedSU2BondTangent4 : Set
EncodedSU2BondTangent4 = SU2Component → RationalBondField4

encodeTangent : PhysicalSU2Tangent4 → EncodedSU2BondTangent4
encodeTangent tangent = tangent

decodeTangent : EncodedSU2BondTangent4 → PhysicalSU2Tangent4
decodeTangent encoded = encoded

encodeDecodeTangent : ∀ encoded component bond →
  encodeTangent (decodeTangent encoded) component bond ≡ encoded component bond
encodeDecodeTangent encoded component bond = refl

decodeEncodeTangent : ∀ tangent component bond →
  decodeTangent (encodeTangent tangent) component bond ≡ tangent component bond
decodeEncodeTangent tangent component bond = refl

physicalTangentComponent :
  PhysicalSU2Tangent4 →
  SU2Component → Axis4 → PhysicalBlockL side4 → ℚ
physicalTangentComponent tangent component axis site =
  tangent component (pair site axis)

componentProjectionMatchesBondCarrier : ∀ tangent component axis site →
  physicalTangentComponent tangent component axis site
  ≡ bondComponent (encodeTangent tangent component) axis site
componentProjectionMatchesBondCarrier tangent component axis site = refl

encodedBondNormSq : EncodedSU2BondTangent4 → ℚ
encodedBondNormSq tangent =
  bondNormSq (tangent component1)
  + (bondNormSq (tangent component2) + bondNormSq (tangent component3))

physicalUnweightedNormSq : PhysicalSU2Tangent4 → ℚ
physicalUnweightedNormSq = encodedBondNormSq

physicalNormSq : ℚ → PhysicalSU2Tangent4 → ℚ
physicalNormSq latticeWeight tangent =
  latticeWeight * physicalUnweightedNormSq tangent

physicalTangentNormMatchesBondNorm : ∀ latticeWeight tangent →
  physicalNormSq latticeWeight tangent
  ≡ latticeWeight * bondNormSq (encodeTangent tangent component1)
    + latticeWeight *
      (bondNormSq (encodeTangent tangent component2)
      + bondNormSq (encodeTangent tangent component3))
physicalTangentNormMatchesBondNorm latticeWeight tangent =
  ℚRing.solve-∀
    latticeWeight
    (bondNormSq (tangent component1))
    (bondNormSq (tangent component2))
    (bondNormSq (tangent component3))

------------------------------------------------------------------------
-- The literal side-four block map is the normalized four-axis average already
-- used by the scalar Poincare theorem.  Qh = 0 therefore supplies, rather than
-- assumes separately, the componentwise mean-zero premise.
------------------------------------------------------------------------

PhysicalBlockAverageZero : PhysicalSU2Tangent4 → Set
PhysicalBlockAverageZero tangent =
  ∀ component axis site →
  average0123 (bondComponent (tangent component) axis) site ≡ 0ℚ

physicalBlockConstraintRemovesComponentMeans :
  ∀ tangent → PhysicalBlockAverageZero tangent →
  ∀ component → BondComponentMeanZero (tangent component)
physicalBlockConstraintRemovesComponentMeans tangent blockZero component axis site =
  blockZero component axis site

physicalReferenceDifferenceEnergy : PhysicalSU2Tangent4 → ℚ
physicalReferenceDifferenceEnergy tangent =
  bondReferenceDifferenceEnergy (tangent component1)
  + (bondReferenceDifferenceEnergy (tangent component2)
  + bondReferenceDifferenceEnergy (tangent component3))

scaledPhysicalNormIsComponentFold : ∀ tangent →
  oneSixteenth * physicalUnweightedNormSq tangent
  ≡ oneSixteenth * bondNormSq (tangent component1)
    + (oneSixteenth * bondNormSq (tangent component2)
    + oneSixteenth * bondNormSq (tangent component3))
scaledPhysicalNormIsComponentFold tangent =
  ℚRing.solve-∀
    (bondNormSq (tangent component1))
    (bondNormSq (tangent component2))
    (bondNormSq (tangent component3))

physicalBlockConstrainedDifferencePoincare :
  ∀ tangent → PhysicalBlockAverageZero tangent →
  oneSixteenth * physicalUnweightedNormSq tangent
  ≤ physicalReferenceDifferenceEnergy tangent
physicalBlockConstrainedDifferencePoincare tangent blockZero =
  subst
    (λ left → left ≤ physicalReferenceDifferenceEnergy tangent)
    (sym (scaledPhysicalNormIsComponentFold tangent))
    (ℚP.+-mono-≤
      (path4BondDifferencePoincare
        (tangent component1)
        (physicalBlockConstraintRemovesComponentMeans
          tangent blockZero component1))
      (ℚP.+-mono-≤
        (path4BondDifferencePoincare
          (tangent component2)
          (physicalBlockConstraintRemovesComponentMeans
            tangent blockZero component2))
        (path4BondDifferencePoincare
          (tangent component3)
          (physicalBlockConstraintRemovesComponentMeans
            tangent blockZero component3))))

path4SU2PhysicalTangentCarrierLevel : ProofLevel
path4SU2PhysicalTangentCarrierLevel = machineChecked

physicalTangentNormMatchesBondNormLevel : ProofLevel
physicalTangentNormMatchesBondNormLevel = machineChecked

physicalBlockConstraintRemovesComponentMeansLevel : ProofLevel
physicalBlockConstraintRemovesComponentMeansLevel = machineChecked

physicalBlockConstrainedDifferencePoincareLevel : ProofLevel
physicalBlockConstrainedDifferencePoincareLevel = machineChecked
