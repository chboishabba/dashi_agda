module DASHI.Physics.YangMills.BalabanPath4PhysicalFibreMatchExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational using (ℚ; 0ℚ; _+_; _-_; _*_; -_; _≤_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
open import DASHI.Physics.YangMills.BalabanBoolean4BlockPoincareExact using (sq)
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact
open import DASHI.Physics.YangMills.BalabanPath4GeneratedLDLCertificate

------------------------------------------------------------------------
-- Concrete physical consumption of the committed side-four LDL certificate.
--
-- The division-free centred fibre has zero sum.  Its first three entries are
-- therefore the independent coordinates of Path4Coordinates and the fourth is
-- exactly the generated final coordinate.  Norm and edge-energy folds are then
-- identified literally with the generated P4 certificate.
------------------------------------------------------------------------

fourSide : Nat
fourSide = four

index0 index1 index2 index3 : CyclicIndex fourSide
index0 = zeroᵢ
index1 = sucᵢ zeroᵢ
index2 = sucᵢ (sucᵢ zeroᵢ)
index3 = sucᵢ (sucᵢ (sucᵢ zeroᵢ))

physicalFibre4Coordinate :
  SiteField fourSide → Axis4 → Triple (CyclicIndex fourSide) →
  CyclicIndex fourSide → ℚ
physicalFibre4Coordinate fieldValue axis transverse =
  scaledCenteredFibreValue fieldValue axis transverse

path4CoordinatesFromPhysicalFibre :
  SiteField fourSide → Axis4 → Triple (CyclicIndex fourSide) →
  Path4Coordinates
path4CoordinatesFromPhysicalFibre fieldValue axis transverse =
  path4Coordinates
    (physicalFibre4Coordinate fieldValue axis transverse index0)
    (physicalFibre4Coordinate fieldValue axis transverse index1)
    (physicalFibre4Coordinate fieldValue axis transverse index2)

isolateFourthHelper : ∀ a b c d →
  d ≡ (a + (b + (c + (d + 0ℚ)))) - (a + (b + c))
isolateFourthHelper = ℚRing.solve-∀

zeroSubtractHelper : ∀ a b c →
  0ℚ - (a + (b + c)) ≡ - (a + (b + c))
zeroSubtractHelper = ℚRing.solve-∀

dropTrailingZero4 : ∀ u v w t →
  u + (v + (w + (t + 0ℚ))) ≡ u + (v + (w + t))
dropTrailingZero4 = ℚRing.solve-∀

dropTrailingZero3 : ∀ u v w →
  u + (v + (w + 0ℚ)) ≡ u + (v + w)
dropTrailingZero3 = ℚRing.solve-∀

isolateFourthFromZero : ∀ a b c d →
  a + (b + (c + (d + 0ℚ))) ≡ 0ℚ →
  d ≡ - (a + (b + c))
isolateFourthFromZero a b c d total =
  trans (isolateFourthHelper a b c d)
    (trans
      (cong (λ value → value - (a + (b + c))) total)
      (zeroSubtractHelper a b c))

physicalFourthCoordinateIsGeneratedLast :
  ∀ fieldValue axis transverse →
  physicalFibre4Coordinate fieldValue axis transverse index3
  ≡ lastCoordinate (path4CoordinatesFromPhysicalFibre fieldValue axis transverse)
physicalFourthCoordinateIsGeneratedLast fieldValue axis transverse =
  isolateFourthFromZero
    (physicalFibre4Coordinate fieldValue axis transverse index0)
    (physicalFibre4Coordinate fieldValue axis transverse index1)
    (physicalFibre4Coordinate fieldValue axis transverse index2)
    (physicalFibre4Coordinate fieldValue axis transverse index3)
    (scaledCenteredFibreSumZero fieldValue axis transverse)

physicalFibre4NormExpansion :
  ∀ fieldValue axis transverse →
  scaledCenteredFibreNormSq fieldValue axis transverse
  ≡ sq (physicalFibre4Coordinate fieldValue axis transverse index0)
    + (sq (physicalFibre4Coordinate fieldValue axis transverse index1)
    + (sq (physicalFibre4Coordinate fieldValue axis transverse index2)
    + (sq (physicalFibre4Coordinate fieldValue axis transverse index3) + 0ℚ)))
physicalFibre4NormExpansion fieldValue axis transverse = refl

physicalFibre4EnergyExpansion :
  ∀ fieldValue axis transverse →
  scaledCenteredFibreEdgeEnergy fieldValue axis transverse
  ≡ sq
      (physicalFibre4Coordinate fieldValue axis transverse index1
      - physicalFibre4Coordinate fieldValue axis transverse index0)
    + (sq
        (physicalFibre4Coordinate fieldValue axis transverse index2
        - physicalFibre4Coordinate fieldValue axis transverse index1)
    + (sq
        (physicalFibre4Coordinate fieldValue axis transverse index3
        - physicalFibre4Coordinate fieldValue axis transverse index2)
      + 0ℚ))
physicalFibre4EnergyExpansion fieldValue axis transverse = refl

physicalFibre4NormMatchesGenerated :
  ∀ fieldValue axis transverse →
  scaledCenteredFibreNormSq fieldValue axis transverse
  ≡ path4NormSq (path4CoordinatesFromPhysicalFibre fieldValue axis transverse)
physicalFibre4NormMatchesGenerated fieldValue axis transverse =
  trans
    (physicalFibre4NormExpansion fieldValue axis transverse)
    (trans
      (cong
        (λ fourth →
          sq (physicalFibre4Coordinate fieldValue axis transverse index0)
          + (sq (physicalFibre4Coordinate fieldValue axis transverse index1)
          + (sq (physicalFibre4Coordinate fieldValue axis transverse index2)
          + (sq fourth + 0ℚ))))
        (physicalFourthCoordinateIsGeneratedLast fieldValue axis transverse))
      (dropTrailingZero4
        (sq (physicalFibre4Coordinate fieldValue axis transverse index0))
        (sq (physicalFibre4Coordinate fieldValue axis transverse index1))
        (sq (physicalFibre4Coordinate fieldValue axis transverse index2))
        (sq (lastCoordinate (path4CoordinatesFromPhysicalFibre fieldValue axis transverse)))))

physicalFibre4EnergyMatchesGenerated :
  ∀ fieldValue axis transverse →
  scaledCenteredFibreEdgeEnergy fieldValue axis transverse
  ≡ path4Energy (path4CoordinatesFromPhysicalFibre fieldValue axis transverse)
physicalFibre4EnergyMatchesGenerated fieldValue axis transverse =
  trans
    (physicalFibre4EnergyExpansion fieldValue axis transverse)
    (trans
      (cong
        (λ fourth →
          sq
            (physicalFibre4Coordinate fieldValue axis transverse index1
            - physicalFibre4Coordinate fieldValue axis transverse index0)
          + (sq
              (physicalFibre4Coordinate fieldValue axis transverse index2
              - physicalFibre4Coordinate fieldValue axis transverse index1)
          + (sq
              (fourth
              - physicalFibre4Coordinate fieldValue axis transverse index2)
            + 0ℚ)))
        (physicalFourthCoordinateIsGeneratedLast fieldValue axis transverse))
      (dropTrailingZero3
        (sq
          (physicalFibre4Coordinate fieldValue axis transverse index1
          - physicalFibre4Coordinate fieldValue axis transverse index0))
        (sq
          (physicalFibre4Coordinate fieldValue axis transverse index2
          - physicalFibre4Coordinate fieldValue axis transverse index1))
        (sq
          (lastCoordinate (path4CoordinatesFromPhysicalFibre fieldValue axis transverse)
          - physicalFibre4Coordinate fieldValue axis transverse index2))))

physicalSide4FibrePoincare :
  ∀ fieldValue axis transverse →
  oneSixteenth * scaledCenteredFibreNormSq fieldValue axis transverse
  ≤ scaledCenteredFibreEdgeEnergy fieldValue axis transverse
physicalSide4FibrePoincare fieldValue axis transverse =
  subst
    (λ energyValue →
      oneSixteenth * scaledCenteredFibreNormSq fieldValue axis transverse
      ≤ energyValue)
    (sym (physicalFibre4EnergyMatchesGenerated fieldValue axis transverse))
    (subst
      (λ normValue →
        oneSixteenth * normValue
        ≤ path4Energy (path4CoordinatesFromPhysicalFibre fieldValue axis transverse))
      (sym (physicalFibre4NormMatchesGenerated fieldValue axis transverse))
      (path4Poincare (path4CoordinatesFromPhysicalFibre fieldValue axis transverse)))

path4PhysicalFibreCoordinateMatchLevel : ProofLevel
path4PhysicalFibreCoordinateMatchLevel = machineChecked

path4PhysicalFibreEnergyMatchLevel : ProofLevel
path4PhysicalFibreEnergyMatchLevel = machineChecked

path4PhysicalFibrePoincareLevel : ProofLevel
path4PhysicalFibrePoincareLevel = machineChecked
