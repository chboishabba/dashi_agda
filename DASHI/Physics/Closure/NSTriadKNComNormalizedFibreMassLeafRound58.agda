module DASHI.Physics.Closure.NSTriadKNComNormalizedFibreMassLeafRound58 where

------------------------------------------------------------------------
-- Lightweight normalized B-leaf.
--
-- `pairProduct` is explicitly the normalized physical Gram/energy quantity,
-- not the raw velocity-linear collision kernel.  The three fields below are
-- the literal analytic estimates still required by the Com route.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using ([])
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _/_; _≤_)
import Data.Integer.Base as Int
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Physics.Closure.NSTriadKNComCommonHatSupportLeafRound58 as Hat

sameShellTarget adjacentShellTarget : ℚ
sameShellTarget = Int.+ 17 / 64
adjacentShellTarget = Int.+ 65 / 512

normalizedBandwidthOneEndpoint :
  sameShellTarget + adjacentShellTarget + adjacentShellTarget
  ≡ Int.+ 133 / 256
normalizedBandwidthOneEndpoint = solve []

record PhysicalNormalizedOddPQGramRealization
    (support : Hat.PhysicalOddPQCommonHatIdentification) : Set₁ where
  field
    pairProduct : Nat → Nat → ℚ
    pairProductNonnegative : ∀ q r → 0ℚ ≤ pairProduct q r

open PhysicalNormalizedOddPQGramRealization public

record SameAdjacentNormalizedFibreMassBounds
    {support : Hat.PhysicalOddPQCommonHatIdentification}
    (realization : PhysicalNormalizedOddPQGramRealization support) : Set where
  field
    sameShellBound : ∀ q →
      Hat.supportActive support q q ≡ true →
      pairProduct realization q q ≤ sameShellTarget

    forwardAdjacentBound : ∀ q →
      Hat.supportActive support q (suc q) ≡ true →
      pairProduct realization q (suc q) ≤ adjacentShellTarget

    reverseAdjacentBound : ∀ q →
      Hat.supportActive support (suc q) q ≡ true →
      pairProduct realization (suc q) q ≤ adjacentShellTarget

open SameAdjacentNormalizedFibreMassBounds public
