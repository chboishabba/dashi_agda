module DASHI.Physics.YangMills.BalabanSide4TranslationDifferenceExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier using
  (PhysicalBlockL)
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact using
  (sumRational; sumRationalCong)
open import DASHI.Physics.YangMills.BalabanPath4AxisAverageExact using (side4)
open import DASHI.Physics.YangMills.BalabanConfiguredSide4PeriodicReindexingExact
  using
    ( next4
    ; previous4
    ; nextPrevious4
    ; previousNext4
    ; sumNext4Invariant
    ; sumPrevious4Invariant
    ; siteSum4
    ; siteSumAsCoordinates
    )
open import DASHI.Physics.YangMills.BalabanSide4ScalarGreenKernelComputed
  using (zeroSite4; scalarDeltaAtZero)

------------------------------------------------------------------------
-- The additive C4 action, its inverse, and subtraction.
------------------------------------------------------------------------

add4 : CyclicIndex four → CyclicIndex four → CyclicIndex four
add4 zeroᵢ value = value
add4 (sucᵢ zeroᵢ) value = next4 value
add4 (sucᵢ (sucᵢ zeroᵢ)) value = next4 (next4 value)
add4 (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) value = previous4 value

negate4 : CyclicIndex four → CyclicIndex four
negate4 zeroᵢ = zeroᵢ
negate4 (sucᵢ zeroᵢ) = sucᵢ (sucᵢ (sucᵢ zeroᵢ))
negate4 (sucᵢ (sucᵢ zeroᵢ)) = sucᵢ (sucᵢ zeroᵢ)
negate4 (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) = sucᵢ zeroᵢ

subtract4 : CyclicIndex four → CyclicIndex four → CyclicIndex four
subtract4 left right = add4 (negate4 right) left

add4Next : ∀ amount value →
  add4 amount (next4 value) ≡ next4 (add4 amount value)
add4Next zeroᵢ value = refl
add4Next (sucᵢ zeroᵢ) value = refl
add4Next (sucᵢ (sucᵢ zeroᵢ)) value = refl
add4Next (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) value =
  trans (previousNext4 value) (sym (nextPrevious4 value))

add4Previous : ∀ amount value →
  add4 amount (previous4 value) ≡ previous4 (add4 amount value)
add4Previous zeroᵢ value = refl
add4Previous (sucᵢ zeroᵢ) value =
  trans (nextPrevious4 value) (sym (previousNext4 value))
add4Previous (sucᵢ (sucᵢ zeroᵢ)) value
  rewrite nextPrevious4 value | previousNext4 (next4 value) = refl
add4Previous (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) value = refl

subtract4Next : ∀ left right →
  subtract4 (next4 left) right ≡ next4 (subtract4 left right)
subtract4Next left right = add4Next (negate4 right) left

subtract4Previous : ∀ left right →
  subtract4 (previous4 left) right ≡ previous4 (subtract4 left right)
subtract4Previous left right = add4Previous (negate4 right) left

subtract4SelfZero : ∀ value → subtract4 value value ≡ zeroᵢ
subtract4SelfZero zeroᵢ = refl
subtract4SelfZero (sucᵢ zeroᵢ) = refl
subtract4SelfZero (sucᵢ (sucᵢ zeroᵢ)) = refl
subtract4SelfZero (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) = refl

subtract4ZeroImpliesEqual : ∀ {left right} →
  subtract4 left right ≡ zeroᵢ → left ≡ right
subtract4ZeroImpliesEqual {zeroᵢ} {zeroᵢ} equality = refl
subtract4ZeroImpliesEqual {zeroᵢ} {sucᵢ zeroᵢ} ()
subtract4ZeroImpliesEqual {zeroᵢ} {sucᵢ (sucᵢ zeroᵢ)} ()
subtract4ZeroImpliesEqual {zeroᵢ} {sucᵢ (sucᵢ (sucᵢ zeroᵢ))} ()
subtract4ZeroImpliesEqual {sucᵢ zeroᵢ} {zeroᵢ} ()
subtract4ZeroImpliesEqual {sucᵢ zeroᵢ} {sucᵢ zeroᵢ} equality = refl
subtract4ZeroImpliesEqual {sucᵢ zeroᵢ} {sucᵢ (sucᵢ zeroᵢ)} ()
subtract4ZeroImpliesEqual {sucᵢ zeroᵢ}
  {sucᵢ (sucᵢ (sucᵢ zeroᵢ))} ()
subtract4ZeroImpliesEqual {sucᵢ (sucᵢ zeroᵢ)} {zeroᵢ} ()
subtract4ZeroImpliesEqual {sucᵢ (sucᵢ zeroᵢ)} {sucᵢ zeroᵢ} ()
subtract4ZeroImpliesEqual {sucᵢ (sucᵢ zeroᵢ)}
  {sucᵢ (sucᵢ zeroᵢ)} equality = refl
subtract4ZeroImpliesEqual {sucᵢ (sucᵢ zeroᵢ)}
  {sucᵢ (sucᵢ (sucᵢ zeroᵢ))} ()
subtract4ZeroImpliesEqual {sucᵢ (sucᵢ (sucᵢ zeroᵢ))} {zeroᵢ} ()
subtract4ZeroImpliesEqual {sucᵢ (sucᵢ (sucᵢ zeroᵢ))}
  {sucᵢ zeroᵢ} ()
subtract4ZeroImpliesEqual {sucᵢ (sucᵢ (sucᵢ zeroᵢ))}
  {sucᵢ (sucᵢ zeroᵢ)} ()
subtract4ZeroImpliesEqual {sucᵢ (sucᵢ (sucᵢ zeroᵢ))}
  {sucᵢ (sucᵢ (sucᵢ zeroᵢ))} equality = refl

------------------------------------------------------------------------
-- Four-dimensional translations and differences.
------------------------------------------------------------------------

negateSite4 : PhysicalBlockL side4 → PhysicalBlockL side4
negateSite4 (pair (pair x0 x1) (pair x2 x3)) =
  pair (pair (negate4 x0) (negate4 x1))
    (pair (negate4 x2) (negate4 x3))

translateSite4 :
  PhysicalBlockL side4 → PhysicalBlockL side4 → PhysicalBlockL side4
translateSite4 (pair (pair a0 a1) (pair a2 a3))
  (pair (pair x0 x1) (pair x2 x3)) =
  pair (pair (add4 a0 x0) (add4 a1 x1))
    (pair (add4 a2 x2) (add4 a3 x3))

subtractSite4 :
  PhysicalBlockL side4 → PhysicalBlockL side4 → PhysicalBlockL side4
subtractSite4 left right = translateSite4 (negateSite4 right) left

subtractSiteForward : ∀ axis left right →
  subtractSite4
    (DASHI.Physics.YangMills.BalabanConfiguredSide4PeriodicReindexingExact.shiftForward4
      axis left) right
  ≡ DASHI.Physics.YangMills.BalabanConfiguredSide4PeriodicReindexingExact.shiftForward4
      axis (subtractSite4 left right)
subtractSiteForward zeroᵢ
    (pair (pair l0 l1) (pair l2 l3))
    (pair (pair r0 r1) (pair r2 r3)) =
  cong (λ value → pair (pair value (subtract4 l1 r1))
    (pair (subtract4 l2 r2) (subtract4 l3 r3)))
    (subtract4Next l0 r0)
subtractSiteForward (sucᵢ zeroᵢ)
    (pair (pair l0 l1) (pair l2 l3))
    (pair (pair r0 r1) (pair r2 r3)) =
  cong (λ value → pair (pair (subtract4 l0 r0) value)
    (pair (subtract4 l2 r2) (subtract4 l3 r3)))
    (subtract4Next l1 r1)
subtractSiteForward (sucᵢ (sucᵢ zeroᵢ))
    (pair (pair l0 l1) (pair l2 l3))
    (pair (pair r0 r1) (pair r2 r3)) =
  cong (λ value → pair (pair (subtract4 l0 r0) (subtract4 l1 r1))
    (pair value (subtract4 l3 r3)))
    (subtract4Next l2 r2)
subtractSiteForward (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))
    (pair (pair l0 l1) (pair l2 l3))
    (pair (pair r0 r1) (pair r2 r3)) =
  cong (λ value → pair (pair (subtract4 l0 r0) (subtract4 l1 r1))
    (pair (subtract4 l2 r2) value))
    (subtract4Next l3 r3)

subtractSiteBackward : ∀ axis left right →
  subtractSite4
    (DASHI.Physics.YangMills.BalabanConfiguredSide4PeriodicReindexingExact.shiftBackward4
      axis left) right
  ≡ DASHI.Physics.YangMills.BalabanConfiguredSide4PeriodicReindexingExact.shiftBackward4
      axis (subtractSite4 left right)
subtractSiteBackward zeroᵢ
    (pair (pair l0 l1) (pair l2 l3))
    (pair (pair r0 r1) (pair r2 r3)) =
  cong (λ value → pair (pair value (subtract4 l1 r1))
    (pair (subtract4 l2 r2) (subtract4 l3 r3)))
    (subtract4Previous l0 r0)
subtractSiteBackward (sucᵢ zeroᵢ)
    (pair (pair l0 l1) (pair l2 l3))
    (pair (pair r0 r1) (pair r2 r3)) =
  cong (λ value → pair (pair (subtract4 l0 r0) value)
    (pair (subtract4 l2 r2) (subtract4 l3 r3)))
    (subtract4Previous l1 r1)
subtractSiteBackward (sucᵢ (sucᵢ zeroᵢ))
    (pair (pair l0 l1) (pair l2 l3))
    (pair (pair r0 r1) (pair r2 r3)) =
  cong (λ value → pair (pair (subtract4 l0 r0) (subtract4 l1 r1))
    (pair value (subtract4 l3 r3)))
    (subtract4Previous l2 r2)
subtractSiteBackward (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))
    (pair (pair l0 l1) (pair l2 l3))
    (pair (pair r0 r1) (pair r2 r3)) =
  cong (λ value → pair (pair (subtract4 l0 r0) (subtract4 l1 r1))
    (pair (subtract4 l2 r2) value))
    (subtract4Previous l3 r3)

subtractSiteSelfZero : ∀ site → subtractSite4 site site ≡ zeroSite4
subtractSiteSelfZero (pair (pair x0 x1) (pair x2 x3))
  rewrite subtract4SelfZero x0
        | subtract4SelfZero x1
        | subtract4SelfZero x2
        | subtract4SelfZero x3 = refl

pair4Cong : ∀ {a0 a1 a2 a3 b0 b1 b2 b3 : CyclicIndex four} →
  a0 ≡ b0 → a1 ≡ b1 → a2 ≡ b2 → a3 ≡ b3 →
  pair (pair a0 a1) (pair a2 a3) ≡ pair (pair b0 b1) (pair b2 b3)
pair4Cong refl refl refl refl = refl

subtractSiteZeroImpliesEqual : ∀ {left right} →
  subtractSite4 left right ≡ zeroSite4 → left ≡ right
subtractSiteZeroImpliesEqual
    {pair (pair l0 l1) (pair l2 l3)}
    {pair (pair r0 r1) (pair r2 r3)} equality =
  pair4Cong
    (subtract4ZeroImpliesEqual
      (productFirstInjective (productFirstInjective equality)))
    (subtract4ZeroImpliesEqual
      (productSecondInjective (productFirstInjective equality)))
    (subtract4ZeroImpliesEqual
      (productFirstInjective (productSecondInjective equality)))
    (subtract4ZeroImpliesEqual
      (productSecondInjective (productSecondInjective equality)))

siteDelta4 : PhysicalBlockL side4 → PhysicalBlockL side4 → ℚ
siteDelta4 left right with periodicTorus4DecidableEquality four left right
... | yes equality = 1ℚ
... | no inequality = 0ℚ

scalarDeltaAtZeroSubtract : ∀ left right →
  scalarDeltaAtZero (subtractSite4 left right) ≡ siteDelta4 left right
scalarDeltaAtZeroSubtract left right
  with periodicTorus4DecidableEquality four left right
... | yes equality
  rewrite equality | subtractSiteSelfZero right = refl
... | no inequality
  with periodicTorus4DecidableEquality four (subtractSite4 left right) zeroSite4
... | yes differenceZero with inequality (subtractSiteZeroImpliesEqual differenceZero)
... | ()
... | no differenceNonzero = refl

------------------------------------------------------------------------
-- Translation preserves the complete site fold.
------------------------------------------------------------------------

sumAdd4Invariant : ∀ amount (term : CyclicIndex four → ℚ) →
  sumRational (allCyclicIndices four) (λ value → term (add4 amount value))
  ≡ sumRational (allCyclicIndices four) term
sumAdd4Invariant zeroᵢ term = refl
sumAdd4Invariant (sucᵢ zeroᵢ) term = sumNext4Invariant term
sumAdd4Invariant (sucᵢ (sucᵢ zeroᵢ)) term =
  trans (sumNext4Invariant (λ value → term (next4 value)))
    (sumNext4Invariant term)
sumAdd4Invariant (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) term =
  sumPrevious4Invariant term

siteSumTranslateInvariant : ∀ amount term →
  siteSum4 (λ site → term (translateSite4 amount site)) ≡ siteSum4 term
siteSumTranslateInvariant (pair (pair a0 a1) (pair a2 a3)) term
  rewrite siteSumAsCoordinates (λ site →
            term (translateSite4 (pair (pair a0 a1) (pair a2 a3)) site))
        | siteSumAsCoordinates term =
  trans
    (sumAdd4Invariant a0 (λ x0 →
      sumRational (allCyclicIndices four) (λ x1 →
        sumRational (allCyclicIndices four) (λ x2 →
          sumRational (allCyclicIndices four) (λ x3 →
            term (pair (pair x0 (add4 a1 x1))
              (pair (add4 a2 x2) (add4 a3 x3))))))))
    (trans
      (sumRationalCong (allCyclicIndices four) _ _ (λ x0 →
        sumAdd4Invariant a1 (λ x1 →
          sumRational (allCyclicIndices four) (λ x2 →
            sumRational (allCyclicIndices four) (λ x3 →
              term (pair (pair x0 x1)
                (pair (add4 a2 x2) (add4 a3 x3))))))))
      (trans
        (sumRationalCong (allCyclicIndices four) _ _ (λ x0 →
          sumRationalCong (allCyclicIndices four) _ _ (λ x1 →
            sumAdd4Invariant a2 (λ x2 →
              sumRational (allCyclicIndices four) (λ x3 →
                term (pair (pair x0 x1) (pair x2 (add4 a3 x3))))))))
        (sumRationalCong (allCyclicIndices four) _ _ (λ x0 →
          sumRationalCong (allCyclicIndices four) _ _ (λ x1 →
            sumRationalCong (allCyclicIndices four) _ _ (λ x2 →
              sumAdd4Invariant a3 (λ x3 →
                term (pair (pair x0 x1) (pair x2 x3)))))))))

siteSumSubtractInvariant : ∀ center term →
  siteSum4 (λ site → term (subtractSite4 site center)) ≡ siteSum4 term
siteSumSubtractInvariant center term =
  siteSumTranslateInvariant (negateSite4 center) term

side4TranslationDifferenceLevel : ProofLevel
side4TranslationDifferenceLevel = machineChecked

side4TranslatedDeltaLevel : ProofLevel
side4TranslatedDeltaLevel = machineChecked

side4TranslationFoldInvarianceLevel : ProofLevel
side4TranslationFoldInvarianceLevel = machineChecked
