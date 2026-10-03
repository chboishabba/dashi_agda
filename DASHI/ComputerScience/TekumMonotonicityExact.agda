module DASHI.ComputerScience.TekumMonotonicityExact where

open import DASHI.ComputerScience.TekumFormalPropertiesExact public
  using (TekumOrderedCodeWitness)

open import DASHI.ComputerScience.TekumMonotoneMagnitudeExact public
  using
    ( exponentStrictForcesMagnitudeStrict
    ; sameExponentSignificandStrictForcesMagnitudeStrict
    )

open import DASHI.ComputerScience.TekumPositiveSourceSuccessorAnchorExact public
  using
    ( positiveSourceStepRaisesAnchorRank
    ; positiveSourceSuccessorAnchorsAreAdjacent
    )

open import DASHI.ComputerScience.TekumSourceOrderExact public
  using
    ( PositiveAdjacentOrder
    ; positiveAdjacentSourceCodeStrict
    ; hunholdProposition4PositiveAdjacent
    )

------------------------------------------------------------------------
-- Proposition 4 frontier
--
-- Paid here:
--   * adjacent positive source magnitudes -> adjacent corrected anchor ranks;
--   * given an anchor successor witness, the successor word is the next anchor;
--   * each of Hunhold's fraction/exponent/regime carry cases -> strict rational
--     magnitude order.
--
-- Remaining structural leaf: derive PositiveAdjacentOrder directly from two
-- successfully parsed adjacent positive source words.  Only after that leaf,
-- plus the sign/special cases, is the full source Prop. 4 flag allowed true.
------------------------------------------------------------------------
