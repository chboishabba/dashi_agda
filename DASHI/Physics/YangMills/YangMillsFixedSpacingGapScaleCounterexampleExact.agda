module DASHI.Physics.YangMills.YangMillsFixedSpacingGapScaleCounterexampleExact where

------------------------------------------------------------------------
-- PURPOSE
--
-- A positive lattice gap at every displayed cutoff is not yet a positive
-- physical mass.  If the lattice gap scales quadratically in the spacing,
--
--   Delta_latt(a) = a^2,
--
-- then rescaling by a^-1 gives Delta_phys(a)=a, which collapses as the spacing
-- is refined.  This module proves the exact rational algebra and gives two
-- inhabited cutoff samples.  No limiting theorem is hidden in the example.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _*_; _<_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; trans)

quadraticLatticeGap : ℚ → ℚ
quadraticLatticeGap spacing = spacing * spacing

physicalRescaledGap : ℚ → ℚ → ℚ
physicalRescaledGap inverseSpacing spacing =
  inverseSpacing * quadraticLatticeGap spacing

quadraticGapRescalesToSpacing :
  ∀ inverseSpacing spacing →
  inverseSpacing * spacing ≡ (+ 1 / 1) →
  physicalRescaledGap inverseSpacing spacing ≡ spacing
quadraticGapRescalesToSpacing inverseSpacing spacing inverseLaw =
  trans
    (ℚRing.solve-∀ inverseSpacing spacing)
    (trans
      (cong (λ selected → selected * spacing) inverseLaw)
      (ℚRing.solve-∀ spacing))

spacingHalf spacingQuarter : ℚ
spacingHalf = + 1 / 2
spacingQuarter = + 1 / 4

inverseHalf inverseQuarter : ℚ
inverseHalf = + 2 / 1
inverseQuarter = + 4 / 1

gapHalf gapQuarter : ℚ
gapHalf = quadraticLatticeGap spacingHalf
gapQuarter = quadraticLatticeGap spacingQuarter

spacingHalfPositive : 0ℚ < spacingHalf
spacingHalfPositive = ℚP.positive⁻¹ spacingHalf

spacingQuarterPositive : 0ℚ < spacingQuarter
spacingQuarterPositive = ℚP.positive⁻¹ spacingQuarter

gapHalfPositive : 0ℚ < gapHalf
gapHalfPositive = ℚP.positive⁻¹ gapHalf

gapQuarterPositive : 0ℚ < gapQuarter
gapQuarterPositive = ℚP.positive⁻¹ gapQuarter

inverseHalfLaw : inverseHalf * spacingHalf ≡ (+ 1 / 1)
inverseHalfLaw = ℚRing.solve []

inverseQuarterLaw : inverseQuarter * spacingQuarter ≡ (+ 1 / 1)
inverseQuarterLaw = ℚRing.solve []

gapHalfExact : gapHalf ≡ (+ 1 / 4)
gapHalfExact = ℚRing.solve []

gapQuarterExact : gapQuarter ≡ (+ 1 / 16)
gapQuarterExact = ℚRing.solve []

physicalGapHalfExact :
  physicalRescaledGap inverseHalf spacingHalf ≡ (+ 1 / 2)
physicalGapHalfExact =
  trans
    (quadraticGapRescalesToSpacing inverseHalf spacingHalf inverseHalfLaw)
    refl

physicalGapQuarterExact :
  physicalRescaledGap inverseQuarter spacingQuarter ≡ (+ 1 / 4)
physicalGapQuarterExact =
  trans
    (quadraticGapRescalesToSpacing
      inverseQuarter spacingQuarter inverseQuarterLaw)
    refl

candidatePhysicalMass : ℚ
candidatePhysicalMass = + 1 / 2

quarterPhysicalGapIsHalfCandidate :
  (+ 2 / 1) * physicalRescaledGap inverseQuarter spacingQuarter
  ≡ candidatePhysicalMass
quarterPhysicalGapIsHalfCandidate = ℚRing.solve []

halfToQuarterPhysicalGapHalves :
  (+ 2 / 1) * physicalRescaledGap inverseQuarter spacingQuarter
  ≡ physicalRescaledGap inverseHalf spacingHalf
halfToQuarterPhysicalGapHalves = ℚRing.solve []

record PositiveFixedSpacingSamplesWithShrinkingPhysicalScale : Set where
  constructor positiveFixedSpacingSamples
  field
    coarseSpacingPositive : 0ℚ < spacingHalf
    fineSpacingPositive : 0ℚ < spacingQuarter
    coarseLatticeGapPositive : 0ℚ < gapHalf
    fineLatticeGapPositive : 0ℚ < gapQuarter
    exactCoarsePhysicalGap :
      physicalRescaledGap inverseHalf spacingHalf ≡ (+ 1 / 2)
    exactFinePhysicalGap :
      physicalRescaledGap inverseQuarter spacingQuarter ≡ (+ 1 / 4)
    exactRefinementLoss :
      (+ 2 / 1) * physicalRescaledGap inverseQuarter spacingQuarter
      ≡ physicalRescaledGap inverseHalf spacingHalf

quadraticGapCounterexample :
  PositiveFixedSpacingSamplesWithShrinkingPhysicalScale
quadraticGapCounterexample =
  positiveFixedSpacingSamples
    spacingHalfPositive
    spacingQuarterPositive
    gapHalfPositive
    gapQuarterPositive
    physicalGapHalfExact
    physicalGapQuarterExact
    halfToQuarterPhysicalGapHalves
