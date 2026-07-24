module DASHI.Physics.YangMills.BalabanPath4ZeroMeanFibrePoincareExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational using (ℚ; 0ℚ; _+_; _-_; _*_; -_; _≤_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
open import DASHI.Physics.YangMills.BalabanBoolean4BlockPoincareExact using (sq)
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact
open import DASHI.Physics.YangMills.BalabanPath4PhysicalFibreMatchExact using
  (fourSide; index0; index1; index2; index3; isolateFourthFromZero)
open import DASHI.Physics.YangMills.BalabanPath4GeneratedLDLCertificate

------------------------------------------------------------------------
-- Direct consumption of the generated P4 certificate on an already mean-zero
-- physical fibre.  Unlike the division-free centering bridge, no L^2 rescaling
-- remains in the resulting Poincare estimate.
------------------------------------------------------------------------

zeroMeanPath4Coordinates :
  SiteField fourSide → Axis4 → Triple (CyclicIndex fourSide) →
  Path4Coordinates
zeroMeanPath4Coordinates field axis transverse =
  path4Coordinates
    (field (insertAxis axis index0 transverse))
    (field (insertAxis axis index1 transverse))
    (field (insertAxis axis index2 transverse))

physicalFibre4SumExpansion :
  ∀ field axis transverse →
  physicalFibreSum field axis transverse
  ≡ field (insertAxis axis index0 transverse)
    + (field (insertAxis axis index1 transverse)
    + (field (insertAxis axis index2 transverse)
    + (field (insertAxis axis index3 transverse) + 0ℚ)))
physicalFibre4SumExpansion field axis transverse = refl

zeroMeanFourthCoordinate :
  ∀ field axis transverse →
  physicalFibreSum field axis transverse ≡ 0ℚ →
  field (insertAxis axis index3 transverse)
  ≡ lastCoordinate (zeroMeanPath4Coordinates field axis transverse)
zeroMeanFourthCoordinate field axis transverse meanZero =
  isolateFourthFromZero
    (field (insertAxis axis index0 transverse))
    (field (insertAxis axis index1 transverse))
    (field (insertAxis axis index2 transverse))
    (field (insertAxis axis index3 transverse))
    (trans
      (sym (physicalFibre4SumExpansion field axis transverse))
      meanZero)

physicalFibre4NormExpansion :
  ∀ field axis transverse →
  physicalFibreNormSq field axis transverse
  ≡ sq (field (insertAxis axis index0 transverse))
    + (sq (field (insertAxis axis index1 transverse))
    + (sq (field (insertAxis axis index2 transverse))
    + (sq (field (insertAxis axis index3 transverse)) + 0ℚ)))
physicalFibre4NormExpansion field axis transverse = refl

physicalFibre4EnergyExpansion :
  ∀ field axis transverse →
  physicalFibreEdgeEnergy field axis transverse
  ≡ sq
      (field (insertAxis axis index1 transverse)
      - field (insertAxis axis index0 transverse))
    + (sq
        (field (insertAxis axis index2 transverse)
        - field (insertAxis axis index1 transverse))
    + (sq
        (field (insertAxis axis index3 transverse)
        - field (insertAxis axis index2 transverse))
      + 0ℚ))
physicalFibre4EnergyExpansion field axis transverse = refl

zeroMeanPhysicalNormMatchesGenerated :
  ∀ field axis transverse →
  physicalFibreSum field axis transverse ≡ 0ℚ →
  physicalFibreNormSq field axis transverse
  ≡ path4NormSq (zeroMeanPath4Coordinates field axis transverse)
zeroMeanPhysicalNormMatchesGenerated field axis transverse meanZero =
  trans
    (physicalFibre4NormExpansion field axis transverse)
    (subst
      (λ fourth →
        sq (field (insertAxis axis index0 transverse))
        + (sq (field (insertAxis axis index1 transverse))
        + (sq (field (insertAxis axis index2 transverse))
        + (sq fourth + 0ℚ)))
        ≡ path4NormSq (zeroMeanPath4Coordinates field axis transverse))
      (zeroMeanFourthCoordinate field axis transverse meanZero)
      (ℚRing.solve-∀
        (field (insertAxis axis index0 transverse))
        (field (insertAxis axis index1 transverse))
        (field (insertAxis axis index2 transverse))
        (lastCoordinate (zeroMeanPath4Coordinates field axis transverse))))

zeroMeanPhysicalEnergyMatchesGenerated :
  ∀ field axis transverse →
  physicalFibreSum field axis transverse ≡ 0ℚ →
  physicalFibreEdgeEnergy field axis transverse
  ≡ path4Energy (zeroMeanPath4Coordinates field axis transverse)
zeroMeanPhysicalEnergyMatchesGenerated field axis transverse meanZero =
  trans
    (physicalFibre4EnergyExpansion field axis transverse)
    (subst
      (λ fourth →
        sq
          (field (insertAxis axis index1 transverse)
          - field (insertAxis axis index0 transverse))
        + (sq
            (field (insertAxis axis index2 transverse)
            - field (insertAxis axis index1 transverse))
        + (sq
            (fourth - field (insertAxis axis index2 transverse))
          + 0ℚ))
        ≡ path4Energy (zeroMeanPath4Coordinates field axis transverse))
      (zeroMeanFourthCoordinate field axis transverse meanZero)
      (ℚRing.solve-∀
        (field (insertAxis axis index0 transverse))
        (field (insertAxis axis index1 transverse))
        (field (insertAxis axis index2 transverse))
        (lastCoordinate (zeroMeanPath4Coordinates field axis transverse))))

zeroMeanPhysicalFibrePoincare :
  ∀ field axis transverse →
  physicalFibreSum field axis transverse ≡ 0ℚ →
  oneSixteenth * physicalFibreNormSq field axis transverse
  ≤ physicalFibreEdgeEnergy field axis transverse
zeroMeanPhysicalFibrePoincare field axis transverse meanZero =
  subst
    (λ energyValue →
      oneSixteenth * physicalFibreNormSq field axis transverse
      ≤ energyValue)
    (sym (zeroMeanPhysicalEnergyMatchesGenerated
      field axis transverse meanZero))
    (subst
      (λ normValue →
        oneSixteenth * normValue
        ≤ path4Energy (zeroMeanPath4Coordinates field axis transverse))
      (sym (zeroMeanPhysicalNormMatchesGenerated
        field axis transverse meanZero))
      (path4Poincare (zeroMeanPath4Coordinates field axis transverse)))

path4ZeroMeanPhysicalFibreMatchLevel : ProofLevel
path4ZeroMeanPhysicalFibreMatchLevel = machineChecked

path4ZeroMeanPhysicalFibrePoincareLevel : ProofLevel
path4ZeroMeanPhysicalFibrePoincareLevel = machineChecked
