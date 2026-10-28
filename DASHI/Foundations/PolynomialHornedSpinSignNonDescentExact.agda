module DASHI.Foundations.PolynomialHornedSpinSignNonDescentExact where

------------------------------------------------------------------------
-- FINITE QUATERNION / POLYNOMIAL PERMUTATION / HORNED NON-DESCENT.
--
-- Original owner: DASHI.Algebra.FiniteQuaternionDoubleCover Q8 -> V4.
-- The binary icosahedral spin cover 2I -> A5 has analogous central-sign
-- forgetting, but is a DIFFERENT mathematical group and independent
-- PR #1244 source. Q8 is NOT 2I, and S5 is NOT 2I despite both having
-- 120 elements. This adapter constructs ONLY the owner-backed Q8 witness.
--
-- A projective quotient cannot recover the central sign, even if it
-- represents the rotation endpoint exactly. This parallels the root
-- label/coefficient and horned scalar/non-Abelian information cuts.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)

import DASHI.Algebra.FiniteQuaternionDoubleCover as Q8

sameProjectiveImageOfCentralSigns :
  Q8.rho Q8.plusOne ≡ Q8.rho Q8.minusOne
sameProjectiveImageOfCentralSigns = refl

centralSignsAreDistinct :
  Q8.plusOne ≡ Q8.minusOne → ⊥
centralSignsAreDistinct ()

-- Stronger than cardinality: NO section can recover every signed
-- quaternion from only its sign-forgetting rotation projection.
noUniversalReconstructionFromV4 :
  (recover : Q8.V4Rotation → Q8.Q8) →
  ((q : Q8.Q8) → recover (Q8.rho q) ≡ q) → ⊥
noUniversalReconstructionFromV4 recover exact =
  centralSignsAreDistinct
    (trans
      (sym (exact Q8.plusOne))
      (trans
        (cong recover sameProjectiveImageOfCentralSigns)
        (exact Q8.minusOne)))

-- The source's spin sign need not equal root permutation parity.
-- This cannot be inferred from two isomorphic *sets* of two elements.
data SpinSignIsRootPermutationParity : Set where

matchingTwoStateCarriersDoesNotIdentifySpinAndParity :
  SpinSignIsRootPermutationParity → ⊥
matchingTwoStateCarriersDoesNotIdentifySpinAndParity ()
