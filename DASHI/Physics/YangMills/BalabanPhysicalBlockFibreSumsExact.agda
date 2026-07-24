module DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.List.Base using (length)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong₂; trans)

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

sumRationalScale :
  ∀ {A : Set} coefficient (values : List A) (term : A → ℚ) →
  sumRational values (λ value → coefficient * term value)
  ≡ coefficient * sumRational values term
sumRationalScale coefficient [] term = ℚRing.solve-∀ coefficient
sumRationalScale coefficient (value ∷ values) term
  rewrite sumRationalScale coefficient values term =
  ℚRing.solve-∀ coefficient (term value) (sumRational values term)

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
sumScaledDifferenceFormula scale total [] term =
  ℚRing.solve-∀ scale total
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
physicalFibreSum {L} field axis transverse =
  sumRational (allCyclicIndices L)
    (λ coordinate → field (insertAxis axis coordinate transverse))

scaledCenteredFibreValue :
  ∀ {L} → SiteField L → Axis4 → Triple (CyclicIndex L) →
  CyclicIndex L → ℚ
scaledCenteredFibreValue {L} field axis transverse coordinate =
  natAsRational L * field (insertAxis axis coordinate transverse)
  - physicalFibreSum field axis transverse

subtractSelfZero : ∀ value → value - value ≡ 0ℚ
subtractSelfZero = ℚRing.solve-∀

scaledCenteredFibreSumZero :
  ∀ {L} field axis transverse →
  sumRational (allCyclicIndices L)
    (scaledCenteredFibreValue field axis transverse)
  ≡ 0ℚ
scaledCenteredFibreSumZero {L} field axis transverse
  rewrite sumScaledDifferenceFormula
    (natAsRational L)
    (physicalFibreSum field axis transverse)
    (allCyclicIndices L)
    (λ coordinate → field (insertAxis axis coordinate transverse))
  | lengthAllCyclicIndices L =
  subtractSelfZero
    (natAsRational L * physicalFibreSum field axis transverse)

scaledCenteredDifferenceExact :
  ∀ {L} field axis transverse left right →
  scaledCenteredFibreValue field axis transverse right
    - scaledCenteredFibreValue field axis transverse left
  ≡ natAsRational L
    * (field (insertAxis axis right transverse)
      - field (insertAxis axis left transverse))
scaledCenteredDifferenceExact = ℚRing.solve-∀

scaledCenteredDifferenceSquareExact :
  ∀ {L} field axis transverse left right →
  sq
    (scaledCenteredFibreValue field axis transverse right
      - scaledCenteredFibreValue field axis transverse left)
  ≡ sq (natAsRational L)
    * sq
      (field (insertAxis axis right transverse)
        - field (insertAxis axis left transverse))
scaledCenteredDifferenceSquareExact = ℚRing.solve-∀

physicalFibreEdgeEnergy :
  ∀ {L} → SiteField L → Axis4 → Triple (CyclicIndex L) → ℚ
physicalFibreEdgeEnergy {zero} field axis transverse = 0ℚ
physicalFibreEdgeEnergy {suc n} field axis transverse =
  sumRational (allCyclicIndices n)
    (λ predecessor →
      sq
        (field (insertAxis axis (sucᵢ predecessor) transverse)
        - field (insertAxis axis (weakenIndex predecessor) transverse)))

scaledCenteredFibreEdgeEnergy :
  ∀ {L} → SiteField L → Axis4 → Triple (CyclicIndex L) → ℚ
scaledCenteredFibreEdgeEnergy {zero} field axis transverse = 0ℚ
scaledCenteredFibreEdgeEnergy {suc n} field axis transverse =
  sumRational (allCyclicIndices n)
    (λ predecessor →
      sq
        (scaledCenteredFibreValue field axis transverse (sucᵢ predecessor)
        - scaledCenteredFibreValue field axis transverse
            (weakenIndex predecessor)))

scaledCenteredFibreEnergyExact :
  ∀ {L} field axis transverse →
  scaledCenteredFibreEdgeEnergy field axis transverse
  ≡ sq (natAsRational L) * physicalFibreEdgeEnergy field axis transverse
scaledCenteredFibreEnergyExact {zero} field axis transverse =
  ℚRing.solve-∀
scaledCenteredFibreEnergyExact {suc n} field axis transverse =
  trans
    (sumRationalCong
      (allCyclicIndices n)
      (λ predecessor →
        sq
          (scaledCenteredFibreValue field axis transverse (sucᵢ predecessor)
          - scaledCenteredFibreValue field axis transverse
              (weakenIndex predecessor)))
      (λ predecessor →
        sq (natAsRational (suc n))
        * sq
          (field (insertAxis axis (sucᵢ predecessor) transverse)
          - field (insertAxis axis (weakenIndex predecessor) transverse)))
      (λ predecessor →
        scaledCenteredDifferenceSquareExact
          field axis transverse
          (weakenIndex predecessor)
          (sucᵢ predecessor)))
    (sumRationalScale
      (sq (natAsRational (suc n)))
      (allCyclicIndices n)
      (λ predecessor →
        sq
          (field (insertAxis axis (sucᵢ predecessor) transverse)
          - field (insertAxis axis (weakenIndex predecessor) transverse))))

------------------------------------------------------------------------
-- Exact scaled variance identity on each fibre.
------------------------------------------------------------------------

physicalFibreNormSq :
  ∀ {L} → SiteField L → Axis4 → Triple (CyclicIndex L) → ℚ
physicalFibreNormSq {L} field axis transverse =
  sumRational (allCyclicIndices L)
    (λ coordinate → sq (field (insertAxis axis coordinate transverse)))

scaledCenteredFibreNormSq :
  ∀ {L} → SiteField L → Axis4 → Triple (CyclicIndex L) → ℚ
scaledCenteredFibreNormSq {L} field axis transverse =
  sumRational (allCyclicIndices L)
    (λ coordinate → sq (scaledCenteredFibreValue field axis transverse coordinate))

centeredSquareInductionAlgebra :
  ∀ scale total value restSquares restSum count →
  sq (scale * value - total)
  + (sq scale * restSquares
    - (1ℚ + 1ℚ) * scale * total * restSum
    + count * sq total)
  ≡ sq scale * (sq value + restSquares)
    - (1ℚ + 1ℚ) * scale * total * (value + restSum)
    + (1ℚ + count) * sq total
centeredSquareInductionAlgebra = ℚRing.solve-∀

sumCenteredSquaresFormula :
  ∀ {A : Set} scale total (values : List A) (term : A → ℚ) →
  sumRational values (λ value → sq (scale * term value - total))
  ≡ sq scale * sumRational values (λ value → sq (term value))
    - (1ℚ + 1ℚ) * scale * total * sumRational values term
    + natAsRational (length values) * sq total
sumCenteredSquaresFormula scale total [] term =
  ℚRing.solve-∀ scale total
sumCenteredSquaresFormula scale total (value ∷ values) term
  rewrite sumCenteredSquaresFormula scale total values term =
  centeredSquareInductionAlgebra
    scale total (term value)
    (sumRational values (λ item → sq (term item)))
    (sumRational values term)
    (natAsRational (length values))

scaledVarianceNormalization : ∀ scale normSqValue total →
  sq scale * normSqValue
    - (1ℚ + 1ℚ) * scale * total * total
    + scale * sq total
  ≡ sq scale * normSqValue - scale * sq total
scaledVarianceNormalization = ℚRing.solve-∀

scaledCenteredFibreNormExact :
  ∀ {L} field axis transverse →
  scaledCenteredFibreNormSq field axis transverse
  ≡ sq (natAsRational L) * physicalFibreNormSq field axis transverse
    - natAsRational L * sq (physicalFibreSum field axis transverse)
scaledCenteredFibreNormExact {L} field axis transverse
  rewrite sumCenteredSquaresFormula
    (natAsRational L)
    (physicalFibreSum field axis transverse)
    (allCyclicIndices L)
    (λ coordinate → field (insertAxis axis coordinate transverse))
  | lengthAllCyclicIndices L =
  scaledVarianceNormalization
    (natAsRational L)
    (physicalFibreNormSq field axis transverse)
    (physicalFibreSum field axis transverse)

physicalFibreScaledMeanZeroLevel : ProofLevel
physicalFibreScaledMeanZeroLevel = machineChecked

physicalFibreEdgeEnergyIdentificationLevel : ProofLevel
physicalFibreEdgeEnergyIdentificationLevel = machineChecked

physicalFibreScaledVarianceIdentityLevel : ProofLevel
physicalFibreScaledVarianceIdentityLevel = machineChecked

physicalFourAxisAverageOrthogonalityLevel : ProofLevel
physicalFourAxisAverageOrthogonalityLevel = conditional
