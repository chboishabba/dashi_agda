module DASHI.Physics.YangMills.BalabanConfiguredSide4PeriodicReindexingExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational using (ℚ; 0ℚ; _+_; _-_; _*_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier using
  (PhysicalBlockL; physicalBlockSites)
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact using
  (sumRational; sumRationalCong)
open import DASHI.Physics.YangMills.BalabanPath4AxisAverageExact using (side4)

------------------------------------------------------------------------
-- List-fold algebra needed to expose the literal fourfold site enumeration.
------------------------------------------------------------------------

sumRationalAppend :
  ∀ {A : Set} (left right : List A) (term : A → ℚ) →
  sumRational (left ++ right) term
  ≡ sumRational left term + sumRational right term
sumRationalAppend [] right term = sym (ℚRing.solve-∀ (sumRational right term))
sumRationalAppend (value ∷ values) right term
  rewrite sumRationalAppend values right term =
  ℚRing.solve-∀ (term value) (sumRational values term) (sumRational right term)

sumRationalMap :
  ∀ {A B : Set} (f : A → B) (values : List A) (term : B → ℚ) →
  sumRational (map f values) term
  ≡ sumRational values (λ value → term (f value))
sumRationalMap f [] term = refl
sumRationalMap f (value ∷ values) term
  rewrite sumRationalMap f values term = refl

sumRationalCartesian :
  ∀ {A B : Set} (xs : List A) (ys : List B)
    (term : Product A B → ℚ) →
  sumRational (cartesian xs ys) term
  ≡ sumRational xs
      (λ x → sumRational ys (λ y → term (pair x y)))
sumRationalCartesian [] ys term = refl
sumRationalCartesian (x ∷ xs) ys term
  rewrite sumRationalAppend
      (map (λ y → pair x y) ys) (cartesian xs ys) term
        | sumRationalMap (λ y → pair x y) ys term
        | sumRationalCartesian xs ys term = refl

------------------------------------------------------------------------
-- Literal successor and predecessor on the configured four-cycle.
------------------------------------------------------------------------

next4 : CyclicIndex four → CyclicIndex four
next4 zeroᵢ = sucᵢ zeroᵢ
next4 (sucᵢ zeroᵢ) = sucᵢ (sucᵢ zeroᵢ)
next4 (sucᵢ (sucᵢ zeroᵢ)) = sucᵢ (sucᵢ (sucᵢ zeroᵢ))
next4 (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) = zeroᵢ

previous4 : CyclicIndex four → CyclicIndex four
previous4 zeroᵢ = sucᵢ (sucᵢ (sucᵢ zeroᵢ))
previous4 (sucᵢ zeroᵢ) = zeroᵢ
previous4 (sucᵢ (sucᵢ zeroᵢ)) = sucᵢ zeroᵢ
previous4 (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) = sucᵢ (sucᵢ zeroᵢ)

nextPrevious4 : ∀ coordinate → next4 (previous4 coordinate) ≡ coordinate
nextPrevious4 zeroᵢ = refl
nextPrevious4 (sucᵢ zeroᵢ) = refl
nextPrevious4 (sucᵢ (sucᵢ zeroᵢ)) = refl
nextPrevious4 (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) = refl

previousNext4 : ∀ coordinate → previous4 (next4 coordinate) ≡ coordinate
previousNext4 zeroᵢ = refl
previousNext4 (sucᵢ zeroᵢ) = refl
previousNext4 (sucᵢ (sucᵢ zeroᵢ)) = refl
previousNext4 (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) = refl

sumNext4Invariant : ∀ (term : CyclicIndex four → ℚ) →
  sumRational (allCyclicIndices four) (λ coordinate → term (next4 coordinate))
  ≡ sumRational (allCyclicIndices four) term
sumNext4Invariant term =
  ℚRing.solve-∀
    (term zeroᵢ)
    (term (sucᵢ zeroᵢ))
    (term (sucᵢ (sucᵢ zeroᵢ)))
    (term (sucᵢ (sucᵢ (sucᵢ zeroᵢ))))

sumPrevious4Invariant : ∀ (term : CyclicIndex four → ℚ) →
  sumRational (allCyclicIndices four) (λ coordinate → term (previous4 coordinate))
  ≡ sumRational (allCyclicIndices four) term
sumPrevious4Invariant term =
  ℚRing.solve-∀
    (term zeroᵢ)
    (term (sucᵢ zeroᵢ))
    (term (sucᵢ (sucᵢ zeroᵢ)))
    (term (sucᵢ (sucᵢ (sucᵢ zeroᵢ))))

------------------------------------------------------------------------
-- Periodic translations of the literal four-torus.
------------------------------------------------------------------------

shiftForward4 : Axis4 → PhysicalBlockL side4 → PhysicalBlockL side4
shiftForward4 zeroᵢ (pair (pair x0 x1) (pair x2 x3)) =
  pair (pair (next4 x0) x1) (pair x2 x3)
shiftForward4 (sucᵢ zeroᵢ) (pair (pair x0 x1) (pair x2 x3)) =
  pair (pair x0 (next4 x1)) (pair x2 x3)
shiftForward4 (sucᵢ (sucᵢ zeroᵢ)) (pair (pair x0 x1) (pair x2 x3)) =
  pair (pair x0 x1) (pair (next4 x2) x3)
shiftForward4 (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))
  (pair (pair x0 x1) (pair x2 x3)) =
  pair (pair x0 x1) (pair x2 (next4 x3))

shiftBackward4 : Axis4 → PhysicalBlockL side4 → PhysicalBlockL side4
shiftBackward4 zeroᵢ (pair (pair x0 x1) (pair x2 x3)) =
  pair (pair (previous4 x0) x1) (pair x2 x3)
shiftBackward4 (sucᵢ zeroᵢ) (pair (pair x0 x1) (pair x2 x3)) =
  pair (pair x0 (previous4 x1)) (pair x2 x3)
shiftBackward4 (sucᵢ (sucᵢ zeroᵢ)) (pair (pair x0 x1) (pair x2 x3)) =
  pair (pair x0 x1) (pair (previous4 x2) x3)
shiftBackward4 (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))
  (pair (pair x0 x1) (pair x2 x3)) =
  pair (pair x0 x1) (pair x2 (previous4 x3))

forwardAfterBackward4 : ∀ axis site →
  shiftForward4 axis (shiftBackward4 axis site) ≡ site
forwardAfterBackward4 zeroᵢ (pair (pair x0 x1) (pair x2 x3))
  rewrite nextPrevious4 x0 = refl
forwardAfterBackward4 (sucᵢ zeroᵢ) (pair (pair x0 x1) (pair x2 x3))
  rewrite nextPrevious4 x1 = refl
forwardAfterBackward4 (sucᵢ (sucᵢ zeroᵢ))
  (pair (pair x0 x1) (pair x2 x3))
  rewrite nextPrevious4 x2 = refl
forwardAfterBackward4 (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))
  (pair (pair x0 x1) (pair x2 x3))
  rewrite nextPrevious4 x3 = refl

backwardAfterForward4 : ∀ axis site →
  shiftBackward4 axis (shiftForward4 axis site) ≡ site
backwardAfterForward4 zeroᵢ (pair (pair x0 x1) (pair x2 x3))
  rewrite previousNext4 x0 = refl
backwardAfterForward4 (sucᵢ zeroᵢ) (pair (pair x0 x1) (pair x2 x3))
  rewrite previousNext4 x1 = refl
backwardAfterForward4 (sucᵢ (sucᵢ zeroᵢ))
  (pair (pair x0 x1) (pair x2 x3))
  rewrite previousNext4 x2 = refl
backwardAfterForward4 (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))
  (pair (pair x0 x1) (pair x2 x3))
  rewrite previousNext4 x3 = refl

------------------------------------------------------------------------
-- Exact site-fold reindexing.
------------------------------------------------------------------------

siteSum4 : (PhysicalBlockL side4 → ℚ) → ℚ
siteSum4 term = sumRational (physicalBlockSites side4) term

siteSumAsCoordinates : ∀ term →
  siteSum4 term
  ≡ sumRational (allCyclicIndices four) (λ x0 →
      sumRational (allCyclicIndices four) (λ x1 →
        sumRational (allCyclicIndices four) (λ x2 →
          sumRational (allCyclicIndices four) (λ x3 →
            term (pair (pair x0 x1) (pair x2 x3))))))
siteSumAsCoordinates term
  rewrite sumRationalCartesian
      (cartesian (allCyclicIndices four) (allCyclicIndices four))
      (cartesian (allCyclicIndices four) (allCyclicIndices four)) term
        | sumRationalCartesian (allCyclicIndices four) (allCyclicIndices four)
            (λ p01 → sumRational
              (cartesian (allCyclicIndices four) (allCyclicIndices four))
              (λ p23 → term (pair p01 p23))) =
  sumRationalCong (allCyclicIndices four)
    (λ x0 → sumRational (allCyclicIndices four) (λ x1 →
      sumRational (cartesian (allCyclicIndices four) (allCyclicIndices four))
        (λ p23 → term (pair (pair x0 x1) p23))))
    (λ x0 → sumRational (allCyclicIndices four) (λ x1 →
      sumRational (allCyclicIndices four) (λ x2 →
        sumRational (allCyclicIndices four) (λ x3 →
          term (pair (pair x0 x1) (pair x2 x3))))))
    (λ x0 → sumRationalCong (allCyclicIndices four)
      (λ x1 → sumRational
        (cartesian (allCyclicIndices four) (allCyclicIndices four))
        (λ p23 → term (pair (pair x0 x1) p23)))
      (λ x1 → sumRational (allCyclicIndices four) (λ x2 →
        sumRational (allCyclicIndices four) (λ x3 →
          term (pair (pair x0 x1) (pair x2 x3)))))
      (λ x1 → sumRationalCartesian
        (allCyclicIndices four) (allCyclicIndices four)
        (λ p23 → term (pair (pair x0 x1) p23))))

periodicForwardReindexing : ∀ axis term →
  siteSum4 (λ site → term (shiftForward4 axis site)) ≡ siteSum4 term
periodicForwardReindexing zeroᵢ term
  rewrite siteSumAsCoordinates (λ site → term (shiftForward4 zeroᵢ site))
        | siteSumAsCoordinates term =
  sumNext4Invariant (λ x0 →
    sumRational (allCyclicIndices four) (λ x1 →
      sumRational (allCyclicIndices four) (λ x2 →
        sumRational (allCyclicIndices four) (λ x3 →
          term (pair (pair x0 x1) (pair x2 x3))))))
periodicForwardReindexing (sucᵢ zeroᵢ) term
  rewrite siteSumAsCoordinates (λ site → term (shiftForward4 (sucᵢ zeroᵢ) site))
        | siteSumAsCoordinates term =
  sumRationalCong (allCyclicIndices four) _ _
    (λ x0 → sumNext4Invariant (λ x1 →
      sumRational (allCyclicIndices four) (λ x2 →
        sumRational (allCyclicIndices four) (λ x3 →
          term (pair (pair x0 x1) (pair x2 x3))))))
periodicForwardReindexing (sucᵢ (sucᵢ zeroᵢ)) term
  rewrite siteSumAsCoordinates (λ site → term (shiftForward4 (sucᵢ (sucᵢ zeroᵢ)) site))
        | siteSumAsCoordinates term =
  sumRationalCong (allCyclicIndices four) _ _ (λ x0 →
    sumRationalCong (allCyclicIndices four) _ _ (λ x1 →
      sumNext4Invariant (λ x2 →
        sumRational (allCyclicIndices four) (λ x3 →
          term (pair (pair x0 x1) (pair x2 x3))))))
periodicForwardReindexing (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) term
  rewrite siteSumAsCoordinates
      (λ site → term (shiftForward4 (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) site))
        | siteSumAsCoordinates term =
  sumRationalCong (allCyclicIndices four) _ _ (λ x0 →
    sumRationalCong (allCyclicIndices four) _ _ (λ x1 →
      sumRationalCong (allCyclicIndices four) _ _ (λ x2 →
        sumNext4Invariant (λ x3 →
          term (pair (pair x0 x1) (pair x2 x3))))))

periodicBackwardReindexing : ∀ axis term →
  siteSum4 (λ site → term (shiftBackward4 axis site)) ≡ siteSum4 term
periodicBackwardReindexing axis term =
  trans
    (sym (periodicForwardReindexing axis
      (λ site → term (shiftBackward4 axis site))))
    (sumRationalCong (physicalBlockSites side4)
      (λ site → term (shiftBackward4 axis (shiftForward4 axis site)))
      term
      (λ site → cong term (backwardAfterForward4 axis site)))

------------------------------------------------------------------------
-- Forward/backward differences and periodic summation by parts.
------------------------------------------------------------------------

forwardDifference4 : Axis4 → (PhysicalBlockL side4 → ℚ) →
  PhysicalBlockL side4 → ℚ
forwardDifference4 axis field site =
  field (shiftForward4 axis site) - field site

backwardDifference4 : Axis4 → (PhysicalBlockL side4 → ℚ) →
  PhysicalBlockL side4 → ℚ
backwardDifference4 axis field site =
  field site - field (shiftBackward4 axis site)

periodicForwardBackwardSummationByParts : ∀ axis f g →
  siteSum4 (λ site → forwardDifference4 axis f site * g site)
  ≡ - siteSum4 (λ site → f site * backwardDifference4 axis g site)
periodicForwardBackwardSummationByParts axis f g =
  trans
    (cong₂ _-_
      (periodicBackwardReindexing axis
        (λ site → f site * g (shiftBackward4 axis site)))
      refl)
    (sumRationalCong (physicalBlockSites side4) _ _
      (λ site → ℚRing.solve-∀
        (f site) (g site) (g (shiftBackward4 axis site))))

configuredSide4PeriodicReindexingLevel : ProofLevel
configuredSide4PeriodicReindexingLevel = machineChecked

configuredSide4SummationByPartsLevel : ProofLevel
configuredSide4SummationByPartsLevel = machineChecked
