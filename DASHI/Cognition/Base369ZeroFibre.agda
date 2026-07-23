module DASHI.Cognition.Base369ZeroFibre where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.List using (length)

import Base369 as Base
import DASHI.Algebra.BalancedTernary as BT

------------------------------------------------------------------------
-- Concrete typed readings of the repository's 3, 6 and 9 carriers.
--
--   3 = one observable ternary valuation
--   6 = ternary valuation x binary orientation
--   9 = ternary valuation x ternary relation
--
-- The existing Base369 cyclic carriers are retained; the maps below expose
-- their product coordinates and their common ternary quotient.
------------------------------------------------------------------------

data Orientation : Set where
  forward reverse : Orientation

record SixCoordinates : Set where
  constructor sixCoordinates
  field
    polarity    : Base.TriTruth
    orientation : Orientation

open SixCoordinates public

record NineCoordinates : Set where
  constructor nineCoordinates
  field
    localValue      : Base.TriTruth
    relationalValue : Base.TriTruth

open NineCoordinates public

hexToCoordinates : Base.HexTruth → SixCoordinates
hexToCoordinates Base.hex-0 = sixCoordinates Base.tri-low forward
hexToCoordinates Base.hex-1 = sixCoordinates Base.tri-low reverse
hexToCoordinates Base.hex-2 = sixCoordinates Base.tri-mid forward
hexToCoordinates Base.hex-3 = sixCoordinates Base.tri-mid reverse
hexToCoordinates Base.hex-4 = sixCoordinates Base.tri-high forward
hexToCoordinates Base.hex-5 = sixCoordinates Base.tri-high reverse

coordinatesToHex : SixCoordinates → Base.HexTruth
coordinatesToHex (sixCoordinates Base.tri-low forward) = Base.hex-0
coordinatesToHex (sixCoordinates Base.tri-low reverse) = Base.hex-1
coordinatesToHex (sixCoordinates Base.tri-mid forward) = Base.hex-2
coordinatesToHex (sixCoordinates Base.tri-mid reverse) = Base.hex-3
coordinatesToHex (sixCoordinates Base.tri-high forward) = Base.hex-4
coordinatesToHex (sixCoordinates Base.tri-high reverse) = Base.hex-5

hexCoordinateRoundTrip : (hex : Base.HexTruth) →
  coordinatesToHex (hexToCoordinates hex) ≡ hex
hexCoordinateRoundTrip Base.hex-0 = refl
hexCoordinateRoundTrip Base.hex-1 = refl
hexCoordinateRoundTrip Base.hex-2 = refl
hexCoordinateRoundTrip Base.hex-3 = refl
hexCoordinateRoundTrip Base.hex-4 = refl
hexCoordinateRoundTrip Base.hex-5 = refl

nonaryToCoordinates : Base.NonaryTruth → NineCoordinates
nonaryToCoordinates Base.non-0 = nineCoordinates Base.tri-low Base.tri-low
nonaryToCoordinates Base.non-1 = nineCoordinates Base.tri-low Base.tri-mid
nonaryToCoordinates Base.non-2 = nineCoordinates Base.tri-low Base.tri-high
nonaryToCoordinates Base.non-3 = nineCoordinates Base.tri-mid Base.tri-low
nonaryToCoordinates Base.non-4 = nineCoordinates Base.tri-mid Base.tri-mid
nonaryToCoordinates Base.non-5 = nineCoordinates Base.tri-mid Base.tri-high
nonaryToCoordinates Base.non-6 = nineCoordinates Base.tri-high Base.tri-low
nonaryToCoordinates Base.non-7 = nineCoordinates Base.tri-high Base.tri-mid
nonaryToCoordinates Base.non-8 = nineCoordinates Base.tri-high Base.tri-high

coordinatesToNonary : NineCoordinates → Base.NonaryTruth
coordinatesToNonary (nineCoordinates Base.tri-low Base.tri-low) = Base.non-0
coordinatesToNonary (nineCoordinates Base.tri-low Base.tri-mid) = Base.non-1
coordinatesToNonary (nineCoordinates Base.tri-low Base.tri-high) = Base.non-2
coordinatesToNonary (nineCoordinates Base.tri-mid Base.tri-low) = Base.non-3
coordinatesToNonary (nineCoordinates Base.tri-mid Base.tri-mid) = Base.non-4
coordinatesToNonary (nineCoordinates Base.tri-mid Base.tri-high) = Base.non-5
coordinatesToNonary (nineCoordinates Base.tri-high Base.tri-low) = Base.non-6
coordinatesToNonary (nineCoordinates Base.tri-high Base.tri-mid) = Base.non-7
coordinatesToNonary (nineCoordinates Base.tri-high Base.tri-high) = Base.non-8

nonaryCoordinateRoundTrip : (value : Base.NonaryTruth) →
  coordinatesToNonary (nonaryToCoordinates value) ≡ value
nonaryCoordinateRoundTrip Base.non-0 = refl
nonaryCoordinateRoundTrip Base.non-1 = refl
nonaryCoordinateRoundTrip Base.non-2 = refl
nonaryCoordinateRoundTrip Base.non-3 = refl
nonaryCoordinateRoundTrip Base.non-4 = refl
nonaryCoordinateRoundTrip Base.non-5 = refl
nonaryCoordinateRoundTrip Base.non-6 = refl
nonaryCoordinateRoundTrip Base.non-7 = refl
nonaryCoordinateRoundTrip Base.non-8 = refl

q6 : Base.HexTruth → Base.TriTruth
q6 hex = polarity (hexToCoordinates hex)

q9 : Base.NonaryTruth → Base.TriTruth
q9 value = localValue (nonaryToCoordinates value)

triToBalanced : Base.TriTruth → BT.Trit
triToBalanced Base.tri-low = BT.neg
triToBalanced Base.tri-mid = BT.zero
triToBalanced Base.tri-high = BT.pos

------------------------------------------------------------------------
-- Exact zero fibres.  The public zero is Base.tri-mid / BT.zero; its six
-- carrier has two representatives and its nine carrier has three.
------------------------------------------------------------------------

data ZeroFibre6 : Set where
  zeroForward zeroReverse : ZeroFibre6

zeroHex : ZeroFibre6 → Base.HexTruth
zeroHex zeroForward = Base.hex-2
zeroHex zeroReverse = Base.hex-3

zeroHexProjectsToMid : (zero : ZeroFibre6) → q6 (zeroHex zero) ≡ Base.tri-mid
zeroHexProjectsToMid zeroForward = refl
zeroHexProjectsToMid zeroReverse = refl

data ZeroFibre9 : Set where
  zeroRelLow zeroRelMid zeroRelHigh : ZeroFibre9

zeroNonary : ZeroFibre9 → Base.NonaryTruth
zeroNonary zeroRelLow = Base.non-3
zeroNonary zeroRelMid = Base.non-4
zeroNonary zeroRelHigh = Base.non-5

zeroNonaryProjectsToMid : (zero : ZeroFibre9) →
  q9 (zeroNonary zero) ≡ Base.tri-mid
zeroNonaryProjectsToMid zeroRelLow = refl
zeroNonaryProjectsToMid zeroRelMid = refl
zeroNonaryProjectsToMid zeroRelHigh = refl

allZeroHex : List Base.HexTruth
allZeroHex = Base.hex-2 ∷ Base.hex-3 ∷ []

allZeroNonary : List Base.NonaryTruth
allZeroNonary = Base.non-3 ∷ Base.non-4 ∷ Base.non-5 ∷ []

zeroHexFibreHasTwoRepresentatives : length allZeroHex ≡ 2
zeroHexFibreHasTwoRepresentatives = refl

zeroNonaryFibreHasThreeRepresentatives : length allZeroNonary ≡ 3
zeroNonaryFibreHasThreeRepresentatives = refl

------------------------------------------------------------------------
-- The common-base pullback 6 x_3 9.  This is not the unrestricted product:
-- only pairs with equal observable ternary coordinates are retained.
------------------------------------------------------------------------

record SixNineFibreProduct : Set where
  constructor fibrePair
  field
    sixValue : Base.HexTruth
    nineValue : Base.NonaryTruth
    commonTrit : q6 sixValue ≡ q9 nineValue

open SixNineFibreProduct public

allSixNineFibreProduct : List SixNineFibreProduct
allSixNineFibreProduct =
  fibrePair Base.hex-0 Base.non-0 refl ∷
  fibrePair Base.hex-0 Base.non-1 refl ∷
  fibrePair Base.hex-0 Base.non-2 refl ∷
  fibrePair Base.hex-1 Base.non-0 refl ∷
  fibrePair Base.hex-1 Base.non-1 refl ∷
  fibrePair Base.hex-1 Base.non-2 refl ∷
  fibrePair Base.hex-2 Base.non-3 refl ∷
  fibrePair Base.hex-2 Base.non-4 refl ∷
  fibrePair Base.hex-2 Base.non-5 refl ∷
  fibrePair Base.hex-3 Base.non-3 refl ∷
  fibrePair Base.hex-3 Base.non-4 refl ∷
  fibrePair Base.hex-3 Base.non-5 refl ∷
  fibrePair Base.hex-4 Base.non-6 refl ∷
  fibrePair Base.hex-4 Base.non-7 refl ∷
  fibrePair Base.hex-4 Base.non-8 refl ∷
  fibrePair Base.hex-5 Base.non-6 refl ∷
  fibrePair Base.hex-5 Base.non-7 refl ∷
  fibrePair Base.hex-5 Base.non-8 refl ∷ []

sixNineFibreProductHasEighteenStates :
  length allSixNineFibreProduct ≡ 18
sixNineFibreProductHasEighteenStates = refl

zeroSixNineFibreProduct : List SixNineFibreProduct
zeroSixNineFibreProduct =
  fibrePair Base.hex-2 Base.non-3 refl ∷
  fibrePair Base.hex-2 Base.non-4 refl ∷
  fibrePair Base.hex-2 Base.non-5 refl ∷
  fibrePair Base.hex-3 Base.non-3 refl ∷
  fibrePair Base.hex-3 Base.non-4 refl ∷
  fibrePair Base.hex-3 Base.non-5 refl ∷ []

visibleZeroHidesSixInteractionStates :
  length zeroSixNineFibreProduct ≡ 6
visibleZeroHidesSixInteractionStates = refl
