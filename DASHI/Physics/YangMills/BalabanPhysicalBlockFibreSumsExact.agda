module DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.List.Base using (length)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; -_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
open import DASHI.Physics.YangMills.BalabanBoolean4BlockPoincareExact using (sq)
open import DASHI.Physics.YangMills.BalabanFourDimensionalHaloOverlapExact using
  (lengthAllCyclicIndices)
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier

------------------------------------------------------------------------
-- Division-free centering on a literal physical axis fibre.
--
-- Rather than introduce 1/L before positivity and nonzero side conditions are
-- available, use
--
--   g(t) = L f(t) - sum_s f(s).
--
-- Then sum_t g(t)=0 exactly, and every edge difference of g is L times the
-- corresponding edge difference of f.  This is precisely the mean-zero
-- coordinate consumed by an arbitrary-L path LDL certificate after a harmless
-- L^2 rescaling.
------------------------------------------------------------------------

natAsRational : Nat → ℚ
natAsRational zero = 0ℚ
natAsRational (suc n) = 1ℚ + natAsRational n

sumRational : ∀ {A : Set} → List A → (A → ℚ) → ℚ
sumRational [] term = 0ℚ
sumRational (value ∷ values) term =
  term value + sumRational values term

sumRationalCong :
  ∀ {A : Set} (values : List A) (left right : A → ℚ) →
  (∀ value → left value ≡ right value) →
  sumRational values left ≡ sumRational values right
sumRationalCong [] left right pointwise = refl
sumRationalCong (value ∷ values) left right pointwise =
  cong₂ _+_
    (pointwise value)
    (sumRationalCong values left right pointwise)

scaleZero : ∀ coefficient → coefficient * 0ℚ ≡ 0ℚ
scaleZero = ℚRing.solve-∀

scalePlus : ∀ coefficient left right →
  coefficient * (left + right)
  ≡ coefficient * left + coefficient * right
scalePlus = ℚRing.solve-∀

sumRationalScale :
  ∀ {A : Set} coefficient (values : List A) (term : A → ℚ) →
  sumRational values (λ value → coefficient * term value)
  ≡ coefficient * sumRational values term
sumRationalScale coefficient [] term =
  sym (scaleZero coefficient)
sumRationalScale coefficient (value ∷ values) term
  rewrite sumRationalScale coefficient values term =
  sym (scalePlus coefficient (term value) (sumRational values term))

sumRationalNegate :
  ∀ {A : Set} (values : List A) (term : A → ℚ) →
  sumRational values (λ value → - term value)
  ≡ - sumRational values term
sumRationalNegate [] term = refl
sumRationalNegate (value ∷ values) term
  rewrite sumRationalNegate values term = ℚRing.solve []

scaledDifferenceSumAlgebra : ∀ scale value rest total count →
  (scale * value - total)
    + (scale * rest - count * total)
  ≡ scale * (value + rest) - (1ℚ + count) * total
scaledDifferenceSumAlgebra = ℚRing.solve-∀

sumScaledDifferenceFormula :
  ∀ {A : Set} scale total (values : List A) (term : A → ℚ) →
  sumRational values (λ value → scale * term value - total)
  ≡ scale * sumRational values term
    - natAsRational (length values) * total
sumScaledDifferenceFormula scale total [] term
  rewrite ℚP.*-zeroʳ scale
  | ℚP.*-zeroˡ total = refl
sumScaledDifferenceFormula scale total (value ∷ values) term
  rewrite sumScaledDifferenceFormula scale total values term =
  scaledDifferenceSumAlgebra
    scale
    (term value)
    (sumRational values term)
    total
    (natAsRational (length values))

SiteField : Nat → Set
SiteField L = PhysicalBlockL L → ℚ

physicalFibreSum :
  ∀ {L} → SiteField L → Axis4 → Triple (CyclicIndex L) → ℚ
physicalFibreSum {L} siteF axis transverse =
  sumRational (allCyclicIndices L)
    (λ coordinate → siteF (insertAxis axis coordinate transverse))

scaledCenteredFibreValue :
  ∀ {L} → SiteField L → Axis4 → Triple (CyclicIndex L) →
  CyclicIndex L → ℚ
scaledCenteredFibreValue {L} siteF axis transverse coordinate =
  natAsRational L * siteF (insertAxis axis coordinate transverse)
  - physicalFibreSum siteF axis transverse

subtractSelfZero : ∀ value → value - value ≡ 0ℚ
subtractSelfZero = ℚRing.solve-∀

scaledCenteredFibreSumZero :
  ∀ {L} siteF axis transverse →
  sumRational (allCyclicIndices L)
    (scaledCenteredFibreValue siteF axis transverse)
  ≡ 0ℚ
scaledCenteredFibreSumZero {L} siteF axis transverse
  rewrite sumScaledDifferenceFormula
    (natAsRational L)
    (physicalFibreSum siteF axis transverse)
    (allCyclicIndices L)
    (λ coordinate → siteF (insertAxis axis coordinate transverse))
  | lengthAllCyclicIndices L =
  subtractSelfZero
    (natAsRational L * physicalFibreSum siteF axis transverse)

centeredDifferenceAlgebra :
  ∀ (scale right left total : ℚ) →
  (scale * right - total) - (scale * left - total)
  ≡ scale * (right - left)
centeredDifferenceAlgebra = ℚRing.solve-∀

scaledCenteredDifferenceExact :
  ∀ {L}
    (siteF : SiteField L) (axis : Axis4) (transverse : Triple (CyclicIndex L))
    (left right : CyclicIndex L) →
  scaledCenteredFibreValue siteF axis transverse right
    - scaledCenteredFibreValue siteF axis transverse left
  ≡ natAsRational L
    * (siteF (insertAxis axis right transverse)
      - siteF (insertAxis axis left transverse))
scaledCenteredDifferenceExact {L} siteF axis transverse left right =
  centeredDifferenceAlgebra
    (natAsRational L)
    (siteF (insertAxis axis right transverse))
    (siteF (insertAxis axis left transverse))
    (physicalFibreSum siteF axis transverse)

squareScaleExact : ∀ scale delta →
  (scale * delta) * (scale * delta) ≡ (scale * scale) * (delta * delta)
squareScaleExact scale delta =
  trans
    (ℚP.*-assoc scale delta (scale * delta))
    (trans
      (cong (scale *_) (sym (ℚP.*-assoc delta scale delta)))
      (trans
        (cong (λ z → scale * (z * delta)) (ℚP.*-comm delta scale))
        (trans
          (cong (scale *_) (ℚP.*-assoc scale delta delta))
          (sym (ℚP.*-assoc scale scale (delta * delta))))))

scaledCenteredDifferenceSquareExact :
  ∀ {L}
    (siteF : SiteField L) (axis : Axis4) (transverse : Triple (CyclicIndex L))
    (left right : CyclicIndex L) →
  sq
    (scaledCenteredFibreValue siteF axis transverse right
      - scaledCenteredFibreValue siteF axis transverse left)
  ≡ sq (natAsRational L)
    * sq
      (siteF (insertAxis axis right transverse)
        - siteF (insertAxis axis left transverse))
scaledCenteredDifferenceSquareExact {L} siteF axis transverse left right =
  trans
    (cong sq
      (scaledCenteredDifferenceExact siteF axis transverse left right))
    (squareScaleExact
      (natAsRational L)
      (siteF (insertAxis axis right transverse)
        - siteF (insertAxis axis left transverse)))

physicalFibreEdgeEnergy :
  ∀ {L} → SiteField L → Axis4 → Triple (CyclicIndex L) → ℚ
physicalFibreEdgeEnergy {zero} siteF axis transverse = 0ℚ
physicalFibreEdgeEnergy {suc n} siteF axis transverse =
  sumRational (allCyclicIndices n)
    (λ predecessor →
      sq
        (siteF (insertAxis axis (sucᵢ predecessor) transverse)
        - siteF (insertAxis axis (weakenIndex predecessor) transverse)))

scaledCenteredFibreEdgeEnergy :
  ∀ {L} → SiteField L → Axis4 → Triple (CyclicIndex L) → ℚ
scaledCenteredFibreEdgeEnergy {zero} siteF axis transverse = 0ℚ
scaledCenteredFibreEdgeEnergy {suc n} siteF axis transverse =
  sumRational (allCyclicIndices n)
    (λ predecessor →
      sq
        (scaledCenteredFibreValue siteF axis transverse (sucᵢ predecessor)
        - scaledCenteredFibreValue siteF axis transverse
            (weakenIndex predecessor)))

scaledCenteredFibreEnergyExact :
  ∀ {L}
    (siteF : SiteField L) (axis : Axis4) (transverse : Triple (CyclicIndex L)) →
  scaledCenteredFibreEdgeEnergy siteF axis transverse
  ≡ sq (natAsRational L) * physicalFibreEdgeEnergy siteF axis transverse
scaledCenteredFibreEnergyExact {zero} siteF axis transverse =
  ℚRing.solve-∀
scaledCenteredFibreEnergyExact {suc n} siteF axis transverse =
  trans
    (sumRationalCong
      (allCyclicIndices n)
      (λ predecessor →
        sq
          (scaledCenteredFibreValue siteF axis transverse (sucᵢ predecessor)
          - scaledCenteredFibreValue siteF axis transverse
              (weakenIndex predecessor)))
      (λ predecessor →
        sq (natAsRational (suc n))
        * sq
          (siteF (insertAxis axis (sucᵢ predecessor) transverse)
          - siteF (insertAxis axis (weakenIndex predecessor) transverse)))
      (λ predecessor →
        scaledCenteredDifferenceSquareExact
          siteF axis transverse
          (weakenIndex predecessor) (sucᵢ predecessor)))
    (sumRationalScale
      (sq (natAsRational (suc n)))
      (allCyclicIndices n)
      (λ predecessor →
        sq
          (siteF (insertAxis axis (sucᵢ predecessor) transverse)
          - siteF (insertAxis axis (weakenIndex predecessor) transverse))))

------------------------------------------------------------------------
-- Exact scaled variance identity on each fibre.
------------------------------------------------------------------------

physicalFibreNormSq :
  ∀ {L} → SiteField L → Axis4 → Triple (CyclicIndex L) → ℚ
physicalFibreNormSq {L} siteF axis transverse =
  sumRational (allCyclicIndices L)
    (λ coordinate → sq (siteF (insertAxis axis coordinate transverse)))

scaledCenteredFibreNormSq :
  ∀ {L} → SiteField L → Axis4 → Triple (CyclicIndex L) → ℚ
scaledCenteredFibreNormSq {L} siteF axis transverse =
  sumRational (allCyclicIndices L)
    (λ coordinate → sq (scaledCenteredFibreValue siteF axis transverse coordinate))

centeredSquareInductionAlgebra :
  ∀ (scale total value restSquares restSum tailCount : ℚ) →
  (scale * value - total) * (scale * value - total)
  + ((scale * scale) * restSquares
    - (1ℚ + 1ℚ) * scale * total * restSum
    + tailCount * (total * total))
  ≡ (scale * scale) * ((value * value) + restSquares)
    - (1ℚ + 1ℚ) * scale * total * (value + restSum)
    + (1ℚ + tailCount) * (total * total)
centeredSquareInductionAlgebra scale total value restSquares restSum tailCount =
  ℚRing.solve (scale ∷ total ∷ value ∷ restSquares ∷ restSum ∷ tailCount ∷ [])

sumCenteredSquaresFormula :
  ∀ {A : Set} scale total (values : List A) (term : A → ℚ) →
  sumRational values (λ value → sq (scale * term value - total))
  ≡ sq scale * sumRational values (λ value → sq (term value))
    - (1ℚ + 1ℚ) * scale * total * sumRational values term
    + natAsRational (length values) * sq total
sumCenteredSquaresFormula scale total [] term
  rewrite ℚP.*-zeroʳ (sq scale)
  | ℚP.*-zeroʳ ((1ℚ + 1ℚ) * scale * total)
  | ℚP.*-zeroˡ (sq total) = refl
sumCenteredSquaresFormula scale total (value ∷ values) term
  rewrite sumCenteredSquaresFormula scale total values term =
  centeredSquareInductionAlgebra
    scale total (term value)
    (sumRational values (λ item → sq (term item)))
    (sumRational values term)
    (natAsRational (length values))

scaledVarianceNormalization : ∀ scale normSqValue total →
  (scale * scale) * normSqValue
    - (1ℚ + 1ℚ) * scale * total * total
    + scale * (total * total)
  ≡ (scale * scale) * normSqValue - scale * (total * total)
scaledVarianceNormalization scale normSqValue total =
  ℚRing.solve (scale ∷ normSqValue ∷ total ∷ [])

scaledCenteredFibreNormExact :
  ∀ {L} siteF axis transverse →
  scaledCenteredFibreNormSq siteF axis transverse
  ≡ sq (natAsRational L) * physicalFibreNormSq siteF axis transverse
    - natAsRational L * sq (physicalFibreSum siteF axis transverse)
scaledCenteredFibreNormExact {L} siteF axis transverse
  rewrite sumCenteredSquaresFormula
    (natAsRational L)
    (physicalFibreSum siteF axis transverse)
    (allCyclicIndices L)
    (λ coordinate → siteF (insertAxis axis coordinate transverse))
  | lengthAllCyclicIndices L =
  scaledVarianceNormalization
    (natAsRational L)
    (physicalFibreNormSq siteF axis transverse)
    (physicalFibreSum siteF axis transverse)

physicalFibreScaledMeanZeroLevel : ProofLevel
physicalFibreScaledMeanZeroLevel = machineChecked

physicalFibreCenteredDifferenceLevel : ProofLevel
physicalFibreCenteredDifferenceLevel = machineChecked

physicalFibreEdgeEnergyIdentificationLevel : ProofLevel
physicalFibreEdgeEnergyIdentificationLevel = machineChecked

physicalFibreScaledVarianceIdentityLevel : ProofLevel
physicalFibreScaledVarianceIdentityLevel = machineChecked

physicalFourAxisAverageOrthogonalityLevel : ProofLevel
physicalFourAxisAverageOrthogonalityLevel = conditional
