module DASHI.ComputerScience.TekumMonotonicityExact where

open import DASHI.ComputerScience.TekumFormalPropertiesExact public
  using (TekumOrderedCodeWitness)

open import DASHI.ComputerScience.TekumMonotoneMagnitudeExact public
  using
    ( exponentStrictForcesMagnitudeStrict
    ; sameExponentSignificandStrictForcesMagnitudeStrict
    )

------------------------------------------------------------------------
-- Proposition 4 frontier
--
-- The rational/numerical side is now explicit: exponent increase and the
-- same-exponent significand increase both compile to strict magnitude order.
-- The outstanding theorem is solely the source-code successor/carry analysis
-- that produces one of those two witnesses for each adjacent positive code,
-- plus the sign/special branches.
------------------------------------------------------------------------
