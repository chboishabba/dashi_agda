module DASHI.Cognition.PNF.OrientedZeroCeilLog2Exact where

open import DASHI.Core.Prelude

import DASHI.Core.GeneralResidualFibreCardinalityExact as General

------------------------------------------------------------------------
-- EXACT NUMERICAL CAPACITY CERTIFICATE FOR FOUR ORIENTED WAVE STATES
------------------------------------------------------------------------

fourStateCeilLog2IsTwo : General.CeilLog2Certificate 4 2
fourStateCeilLog2IsTwo = General.ceilLog2Certificate
  capacity
  least
  where
    capacity : 4 ≤ General.pow2 2
    capacity = ≤-refl

    least : (candidateBits : Nat) → 4 ≤ General.pow2 candidateBits → 2 ≤ candidateBits
    least zero ()
    least (suc zero) ()
    least (suc (suc remaining)) capacityProof = s≤s (s≤s z≤n)

------------------------------------------------------------------------
-- Thus the full standalone Wave4 carrier has a certified least fixed binary
-- width of two bits.  This is distinct from the one-bit fibre-local residual
-- required when the scalar {-1,0,+1} projection is retained alongside it.
------------------------------------------------------------------------
