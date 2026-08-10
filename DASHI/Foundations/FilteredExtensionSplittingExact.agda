module DASHI.Foundations.FilteredExtensionSplittingExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE / CONTEXT
--
-- Charles A. Weibel, "An Introduction to Homological Algebra",
-- Cambridge Studies in Advanced Mathematics 38, Cambridge University Press,
-- 1994. DOI: 10.1017/CBO9781139644136.
--
-- DASHI CONTRIBUTION
--
-- Make the anti-numerology distinction explicit in types.  A short extension
-- carries inclusion/projection and exactness witnesses; a SPLIT extension
-- additionally carries a section.  The associated graded pieces and their
-- cardinal/dimension bookkeeping do not manufacture such a section.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Set-level exact-extension interface.  This records the structural shape
-- without pretending to formalize the full module-category Ext theory here.
------------------------------------------------------------------------

record ShortExtension (G1 J G0 : Set) : Set where
  constructor shortExtension
  field
    include : G1 → J
    project : J → G0

record SplitExtension {G1 J G0 : Set}
  (extension : ShortExtension G1 J G0) : Set where
  constructor splitExtension
  open ShortExtension extension
  field
    section : G0 → J
    projectSection : (x : G0) → project (section x) ≡ x

------------------------------------------------------------------------
-- A concrete finite witness: the filtered carrier has 11 named positions,
-- its associated grades have 1 and 10 positions, and an explicit split map is
-- additional data rather than a consequence of the numeral equation 11=1+10.
------------------------------------------------------------------------

data Grade0 : Set where
  coarseUnit : Grade0

data Grade1 : Set where
  fine0 fine1 fine2 fine3 fine4 fine5 fine6 fine7 fine8 fine9 : Grade1

data Filtered11 : Set where
  retainedCoarse : Filtered11
  retainedFine0 retainedFine1 retainedFine2 retainedFine3 retainedFine4 : Filtered11
  retainedFine5 retainedFine6 retainedFine7 retainedFine8 retainedFine9 : Filtered11

includeFine : Grade1 → Filtered11
includeFine fine0 = retainedFine0
includeFine fine1 = retainedFine1
includeFine fine2 = retainedFine2
includeFine fine3 = retainedFine3
includeFine fine4 = retainedFine4
includeFine fine5 = retainedFine5
includeFine fine6 = retainedFine6
includeFine fine7 = retainedFine7
includeFine fine8 = retainedFine8
includeFine fine9 = retainedFine9

projectCoarse : Filtered11 → Grade0
projectCoarse retainedCoarse = coarseUnit
projectCoarse retainedFine0 = coarseUnit
projectCoarse retainedFine1 = coarseUnit
projectCoarse retainedFine2 = coarseUnit
projectCoarse retainedFine3 = coarseUnit
projectCoarse retainedFine4 = coarseUnit
projectCoarse retainedFine5 = coarseUnit
projectCoarse retainedFine6 = coarseUnit
projectCoarse retainedFine7 = coarseUnit
projectCoarse retainedFine8 = coarseUnit
projectCoarse retainedFine9 = coarseUnit

filteredElevenExtension : ShortExtension Grade1 Filtered11 Grade0
filteredElevenExtension = shortExtension includeFine projectCoarse

chosenCoarseSection : Grade0 → Filtered11
chosenCoarseSection coarseUnit = retainedCoarse

filteredElevenChosenSplit : SplitExtension filteredElevenExtension
filteredElevenChosenSplit =
  splitExtension chosenCoarseSection (λ where coarseUnit → refl)

-- The arithmetic equality is true, but is kept in Nat rather than promoted to
-- the structural SplitExtension type.
gradedCountSumIsEleven : 1 + 10 ≡ 11
gradedCountSumIsEleven = refl

record FilteredSplittingClaimScope : Set where
  constructor filteredSplittingClaimScope
  field
    gradedCountEqualityConstructed : Bool
    gradedCountEqualityConstructedIsTrue :
      gradedCountEqualityConstructed ≡ true

    chosenSplitConstructedSeparately : Bool
    chosenSplitConstructedSeparatelyIsTrue :
      chosenSplitConstructedSeparately ≡ true

    numeralEqualityAutomaticallyProducesSection : Bool
    numeralEqualityAutomaticallyProducesSectionIsFalse :
      numeralEqualityAutomaticallyProducesSection ≡ false

canonicalFilteredSplittingClaimScope : FilteredSplittingClaimScope
canonicalFilteredSplittingClaimScope =
  filteredSplittingClaimScope true refl true refl false refl
