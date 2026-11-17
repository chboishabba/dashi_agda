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
zeroMeanPath4Coordinates fieldValue axis transverse =
  path4Coordinates
    (fieldValue (insertAxis axis index0 transverse))
    (fieldValue (insertAxis axis index1 transverse))
    (fieldValue (insertAxis axis index2 transverse))

physicalFibre4SumExpansion :
  ∀ fieldValue axis transverse →
  physicalFibreSum fieldValue axis transverse
  ≡ fieldValue (insertAxis axis index0 transverse)
    + (fieldValue (insertAxis axis index1 transverse)
    + (fieldValue (insertAxis axis index2 transverse)
    + (fieldValue (insertAxis axis index3 transverse) + 0ℚ)))
physicalFibre4SumExpansion fieldValue axis transverse = refl

zeroMeanFourthCoordinate :
  ∀ fieldValue axis transverse →
  physicalFibreSum fieldValue axis transverse ≡ 0ℚ →
  fieldValue (insertAxis axis index3 transverse)
  ≡ lastCoordinate (zeroMeanPath4Coordinates fieldValue axis transverse)
zeroMeanFourthCoordinate fieldValue axis transverse meanZero =
  isolateFourthFromZero
    (fieldValue (insertAxis axis index0 transverse))
    (fieldValue (insertAxis axis index1 transverse))
    (fieldValue (insertAxis axis index2 transverse))
    (fieldValue (insertAxis axis index3 transverse))
    (trans
      (sym (physicalFibre4SumExpansion fieldValue axis transverse))
      meanZero)

physicalFibre4NormExpansion :
  ∀ fieldValue axis transverse →
  physicalFibreNormSq fieldValue axis transverse
  ≡ sq (fieldValue (insertAxis axis index0 transverse))
    + (sq (fieldValue (insertAxis axis index1 transverse))
    + (sq (fieldValue (insertAxis axis index2 transverse))
    + (sq (fieldValue (insertAxis axis index3 transverse)) + 0ℚ)))
physicalFibre4NormExpansion fieldValue axis transverse = refl

physicalFibre4EnergyExpansion :
  ∀ fieldValue axis transverse →
  physicalFibreEdgeEnergy fieldValue axis transverse
  ≡ sq
      (fieldValue (insertAxis axis index1 transverse)
      - fieldValue (insertAxis axis index0 transverse))
    + (sq
        (fieldValue (insertAxis axis index2 transverse)
        - fieldValue (insertAxis axis index1 transverse))
    + (sq
        (fieldValue (insertAxis axis index3 transverse)
        - fieldValue (insertAxis axis index2 transverse))
      + 0ℚ))
physicalFibre4EnergyExpansion fieldValue axis transverse = refl

zeroMeanPhysicalNormMatchesGenerated :
  ∀ fieldValue axis transverse →
  physicalFibreSum fieldValue axis transverse ≡ 0ℚ →
  physicalFibreNormSq fieldValue axis transverse
  ≡ path4NormSq (zeroMeanPath4Coordinates fieldValue axis transverse)
zeroMeanPhysicalNormMatchesGenerated fieldValue axis transverse meanZero =
  trans
    (physicalFibre4NormExpansion fieldValue axis transverse)
    (subst
      (λ fourth →
        sq (fieldValue (insertAxis axis index0 transverse))
        + (sq (fieldValue (insertAxis axis index1 transverse))
        + (sq (fieldValue (insertAxis axis index2 transverse))
        + (sq fourth + 0ℚ)))
        ≡ path4NormSq (zeroMeanPath4Coordinates fieldValue axis transverse))
      (zeroMeanFourthCoordinate fieldValue axis transverse meanZero)
      (ℚRing.solve-∀))

zeroMeanPhysicalEnergyMatchesGenerated :
  ∀ fieldValue axis transverse →
  physicalFibreSum fieldValue axis transverse ≡ 0ℚ →
  physicalFibreEdgeEnergy fieldValue axis transverse
  ≡ path4Energy (zeroMeanPath4Coordinates fieldValue axis transverse)
zeroMeanPhysicalEnergyMatchesGenerated fieldValue axis transverse meanZero =
  trans
    (physicalFibre4EnergyExpansion fieldValue axis transverse)
    (subst
      (λ fourth →
        sq
          (fieldValue (insertAxis axis index1 transverse)
          - fieldValue (insertAxis axis index0 transverse))
        + (sq
            (fieldValue (insertAxis axis index2 transverse)
            - fieldValue (insertAxis axis index1 transverse))
        + (sq
            (fourth - fieldValue (insertAxis axis index2 transverse))
          + 0ℚ))
        ≡ path4Energy (zeroMeanPath4Coordinates fieldValue axis transverse))
      (zeroMeanFourthCoordinate fieldValue axis transverse meanZero)
      (ℚRing.solve-∀))

zeroMeanPhysicalFibrePoincare :
  ∀ fieldValue axis transverse →
  physicalFibreSum fieldValue axis transverse ≡ 0ℚ →
  oneSixteenth * physicalFibreNormSq fieldValue axis transverse
  ≤ physicalFibreEdgeEnergy fieldValue axis transverse
zeroMeanPhysicalFibrePoincare fieldValue axis transverse meanZero =
  subst
    (λ energyValue →
      oneSixteenth * physicalFibreNormSq fieldValue axis transverse
      ≤ energyValue)
    (sym (zeroMeanPhysicalEnergyMatchesGenerated
      fieldValue axis transverse meanZero))
    (subst
      (λ normValue →
        oneSixteenth * normValue
        ≤ path4Energy (zeroMeanPath4Coordinates fieldValue axis transverse))
      (sym (zeroMeanPhysicalNormMatchesGenerated
        fieldValue axis transverse meanZero))
      (path4Poincare (zeroMeanPath4Coordinates fieldValue axis transverse)))

path4ZeroMeanPhysicalFibreMatchLevel : ProofLevel
path4ZeroMeanPhysicalFibreMatchLevel = machineChecked

path4ZeroMeanPhysicalFibrePoincareLevel : ProofLevel
path4ZeroMeanPhysicalFibrePoincareLevel = machineChecked
