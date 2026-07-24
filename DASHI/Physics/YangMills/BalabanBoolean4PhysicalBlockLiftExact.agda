module DASHI.Physics.YangMills.BalabanBoolean4PhysicalBlockLiftExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; NonNegative; nonNegative)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanBoolean4BlockPoincareExact

------------------------------------------------------------------------
-- Literal translated copies of the exact Boolean four-cell.
--
-- Translation is metadata because every translated copy has the same ordered
-- list of local coordinates.  All analytic quantities are therefore inherited
-- definitionally from the canonical cell, while the origin remains visible to
-- the physical block-tiling layer.
------------------------------------------------------------------------

record Translation4 : Set where
  constructor shift4
  field
    origin0 origin1 origin2 origin3 : Nat

open Translation4 public

record TranslatedBondBlock4 : Set where
  constructor translatedBlock
  field
    origin : Translation4
    localBlock : BondBlock4

open TranslatedBondBlock4 public

translatedNormSq : TranslatedBondBlock4 → ℚ
translatedNormSq block = bondNormSq (localBlock block)

translatedEdgeEnergy : TranslatedBondBlock4 → ℚ
translatedEdgeEnergy block = bondEdgeEnergy (localBlock block)

TranslatedBlockAverageZero : TranslatedBondBlock4 → Set
TranslatedBlockAverageZero block = BondBlockAverageZero (localBlock block)

translatedBlockPoincare : ∀ block →
  TranslatedBlockAverageZero block →
  twoℚ * translatedNormSq block ≤ translatedEdgeEnergy block
translatedBlockPoincare block zeroAverage =
  fourComponentBoolean4BlockPoincare (localBlock block) zeroAverage

------------------------------------------------------------------------
-- Halos enlarge the energy side by an explicit nonnegative contribution.
------------------------------------------------------------------------

record HaloContribution (block : TranslatedBondBlock4) : Set where
  constructor haloContribution
  field
    outsideEnergy : ℚ
    outsideEnergyNonnegative : 0ℚ ≤ outsideEnergy

open HaloContribution public

haloEnergy : ∀ {block} → HaloContribution block → ℚ
haloEnergy {block} halo = translatedEdgeEnergy block + outsideEnergy halo

translatedEdgeBelowHalo : ∀ {block} (halo : HaloContribution block) →
  translatedEdgeEnergy block ≤ haloEnergy halo
translatedEdgeBelowHalo {block} halo =
  baseBelowBasePlusRemainder
    (translatedEdgeEnergy block)
    (outsideEnergy halo)
    (outsideEnergyNonnegative halo)

translatedHaloPoincare : ∀ block (halo : HaloContribution block) →
  TranslatedBlockAverageZero block →
  twoℚ * translatedNormSq block ≤ haloEnergy halo
translatedHaloPoincare block halo zeroAverage =
  ℚP.≤-trans
    (translatedBlockPoincare block zeroAverage)
    (translatedEdgeBelowHalo halo)

------------------------------------------------------------------------
-- Reference Hodge terms are added as two further nonnegative squares.
------------------------------------------------------------------------

record ReferenceHodgeContribution
    (block : TranslatedBondBlock4)
    (halo : HaloContribution block) : Set where
  constructor referenceContribution
  field
    gaugeFixingEnergy blockPenaltyEnergy : ℚ
    gaugeFixingEnergyNonnegative : 0ℚ ≤ gaugeFixingEnergy
    blockPenaltyEnergyNonnegative : 0ℚ ≤ blockPenaltyEnergy

open ReferenceHodgeContribution public

referenceHodgeEnergy :
  ∀ {block} {halo : HaloContribution block} →
  ReferenceHodgeContribution block halo → ℚ
referenceHodgeEnergy {halo = halo} reference =
  haloEnergy halo
  + (gaugeFixingEnergy reference + blockPenaltyEnergy reference)

haloBelowReferenceHodge :
  ∀ {block} {halo : HaloContribution block}
    (reference : ReferenceHodgeContribution block halo) →
  haloEnergy halo ≤ referenceHodgeEnergy reference
haloBelowReferenceHodge {halo = halo} reference =
  baseBelowBasePlusRemainder
    (haloEnergy halo)
    (gaugeFixingEnergy reference + blockPenaltyEnergy reference)
    (ℚP.+-mono-≤
      (gaugeFixingEnergyNonnegative reference)
      (blockPenaltyEnergyNonnegative reference))

translatedReferenceHodgePoincare :
  ∀ block (halo : HaloContribution block)
    (reference : ReferenceHodgeContribution block halo) →
  TranslatedBlockAverageZero block →
  twoℚ * translatedNormSq block ≤ referenceHodgeEnergy reference
translatedReferenceHodgePoincare block halo reference zeroAverage =
  ℚP.≤-trans
    (translatedHaloPoincare block halo zeroAverage)
    (haloBelowReferenceHodge reference)

------------------------------------------------------------------------
-- Exact lattice-spacing normalization.
--
-- The physical bond norm is a^4 ||h||² and the derivative/Hodge energy is
-- a² E(h).  Supplying an exact inverse-square witness turns the dimensionless
-- Boolean gap into (2/a²) ||h||²_phys ≤ E_phys without division inside the
-- theorem statement.
------------------------------------------------------------------------

aSquared : ℚ → ℚ
aSquared a = a * a

aFourth : ℚ → ℚ
aFourth a = aSquared a * aSquared a

record PhysicalSpacing : Set where
  constructor physicalSpacing
  field
    spacing inverseSpacingSquared : ℚ
    spacingSquaredNonnegative : 0ℚ ≤ aSquared spacing
    inverseSquareLaw : inverseSpacingSquared * aSquared spacing ≡ 1ℚ

open PhysicalSpacing public

physicalBondNormSq : PhysicalSpacing → TranslatedBondBlock4 → ℚ
physicalBondNormSq scale block =
  aFourth (spacing scale) * translatedNormSq block

physicalDerivativeEnergy : PhysicalSpacing → TranslatedBondBlock4 → ℚ
physicalDerivativeEnergy scale block =
  aSquared (spacing scale) * translatedEdgeEnergy block

physicalReferenceHodgeEnergy :
  ∀ (scale : PhysicalSpacing) {block} {halo : HaloContribution block} →
  ReferenceHodgeContribution block halo → ℚ
physicalReferenceHodgeEnergy scale reference =
  aSquared (spacing scale) * referenceHodgeEnergy reference

scaledMassReassociate : ∀ inverse a2 norm →
  (twoℚ * inverse) * ((a2 * a2) * norm)
  ≡ (inverse * a2) * (a2 * (twoℚ * norm))
scaledMassReassociate = ℚRing.solve-∀

oneTimes : ∀ value → 1ℚ * value ≡ value
oneTimes = ℚRing.solve-∀

scaledMassIdentity : ∀ scale norm →
  (twoℚ * inverseSpacingSquared scale)
    * (aFourth (spacing scale) * norm)
  ≡ aSquared (spacing scale) * (twoℚ * norm)
scaledMassIdentity scale norm =
  trans
    (scaledMassReassociate
      (inverseSpacingSquared scale)
      (aSquared (spacing scale))
      norm)
    (trans
      (cong
        (λ coefficient →
          coefficient * (aSquared (spacing scale) * (twoℚ * norm)))
        (inverseSquareLaw scale))
      (oneTimes (aSquared (spacing scale) * (twoℚ * norm))))

physicalTranslatedBlockPoincare : ∀ scale block →
  TranslatedBlockAverageZero block →
  (twoℚ * inverseSpacingSquared scale) * physicalBondNormSq scale block
  ≤ physicalDerivativeEnergy scale block
physicalTranslatedBlockPoincare scale block zeroAverage =
  let
    instance
      spacingSqNonnegative : NonNegative (aSquared (spacing scale))
      spacingSqNonnegative = nonNegative (spacingSquaredNonnegative scale)

    scaledGap :
      aSquared (spacing scale) * (twoℚ * translatedNormSq block)
      ≤ aSquared (spacing scale) * translatedEdgeEnergy block
    scaledGap =
      ℚP.*-monoˡ-≤-nonNeg (aSquared (spacing scale))
        (translatedBlockPoincare block zeroAverage)
  in
  subst
    (λ left → left ≤ physicalDerivativeEnergy scale block)
    (sym (scaledMassIdentity scale (translatedNormSq block)))
    scaledGap

physicalReferenceHodgePoincare :
  ∀ scale block (halo : HaloContribution block)
    (reference : ReferenceHodgeContribution block halo) →
  TranslatedBlockAverageZero block →
  (twoℚ * inverseSpacingSquared scale) * physicalBondNormSq scale block
  ≤ physicalReferenceHodgeEnergy scale reference
physicalReferenceHodgePoincare scale block halo reference zeroAverage =
  let
    instance
      spacingSqNonnegative : NonNegative (aSquared (spacing scale))
      spacingSqNonnegative = nonNegative (spacingSquaredNonnegative scale)

    scaledReferenceDomination :
      physicalDerivativeEnergy scale block
      ≤ physicalReferenceHodgeEnergy scale reference
    scaledReferenceDomination =
      ℚP.*-monoˡ-≤-nonNeg (aSquared (spacing scale))
        (ℚP.≤-trans
          (translatedEdgeBelowHalo halo)
          (haloBelowReferenceHodge reference))
  in
  ℚP.≤-trans
    (physicalTranslatedBlockPoincare scale block zeroAverage)
    scaledReferenceDomination

translatedBoolean4BlockLevel : ProofLevel
translatedBoolean4BlockLevel = machineChecked

haloMonotonePoincareLevel : ProofLevel
haloMonotonePoincareLevel = machineChecked

physicalSpacingNormalizationLevel : ProofLevel
physicalSpacingNormalizationLevel = machineChecked

boolean4ReferenceHodgeLiftLevel : ProofLevel
boolean4ReferenceHodgeLiftLevel = machineChecked

arbitraryFixedSideTensorizedBlockLevel : ProofLevel
arbitraryFixedSideTensorizedBlockLevel = conditional

physicalHaloOverlapCountingLevel : ProofLevel
physicalHaloOverlapCountingLevel = conditional
