module DASHI.Physics.YangMills.BalabanCMP109CenteredParityExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- PURPOSE
-- Equip the already-owned centred odd block {-r,...,r}^4 with its literal
-- coordinate-negation involution.  This is the exact finite symmetry required
-- before an odd block observable may be cancelled by pairing x with -x.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Carrier
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredOddBlockCarrierExact as Centered
import DASHI.Physics.YangMills.PhysicalInvolutionParityExact as Parity
open import DASHI.Physics.YangMills.CompactLieProofLevel

negateCenteredOffset :
  ∀ {radius} →
  Centered.CenteredOffset radius →
  Centered.CenteredOffset radius
negateCenteredOffset Centered.centre = Centered.centre
negateCenteredOffset (Centered.positive index) = Centered.negative index
negateCenteredOffset (Centered.negative index) = Centered.positive index

negateCenteredOffsetInvolutive :
  ∀ {radius} (offset : Centered.CenteredOffset radius) →
  negateCenteredOffset (negateCenteredOffset offset) ≡ offset
negateCenteredOffsetInvolutive Centered.centre = refl
negateCenteredOffsetInvolutive (Centered.positive index) = refl
negateCenteredOffsetInvolutive (Centered.negative index) = refl

centeredOffsetInvolution :
  ∀ radius → Parity.Involution (Centered.CenteredOffset radius)
centeredOffsetInvolution radius = record
  { reverse = negateCenteredOffset
  ; reverseInvolutive =
      negateCenteredOffsetInvolutive
  }

negateCenteredBlock4 :
  ∀ {radius} →
  Centered.CenteredBlockPoint4 radius →
  Centered.CenteredBlockPoint4 radius
negateCenteredBlock4
  (Carrier.pair
    (Carrier.pair x0 x1)
    (Carrier.pair x2 x3)) =
  Carrier.pair
    (Carrier.pair
      (negateCenteredOffset x0)
      (negateCenteredOffset x1))
    (Carrier.pair
      (negateCenteredOffset x2)
      (negateCenteredOffset x3))

negateCenteredBlock4Involutive :
  ∀ {radius} (point : Centered.CenteredBlockPoint4 radius) →
  negateCenteredBlock4 (negateCenteredBlock4 point) ≡ point
negateCenteredBlock4Involutive
  (Carrier.pair (Carrier.pair x0 x1) (Carrier.pair x2 x3))
  rewrite negateCenteredOffsetInvolutive x0
        | negateCenteredOffsetInvolutive x1
        | negateCenteredOffsetInvolutive x2
        | negateCenteredOffsetInvolutive x3 = refl

centeredBlockInvolution :
  ∀ radius → Parity.Involution (Centered.CenteredBlockPoint4 radius)
centeredBlockInvolution radius = record
  { reverse = negateCenteredBlock4
  ; reverseInvolutive =
      negateCenteredBlock4Involutive
  }

centeredOriginFixed :
  ∀ {radius} →
  negateCenteredBlock4 (Centered.centeredOrigin4 {radius})
  ≡ Centered.centeredOrigin4
centeredOriginFixed = refl

record OddCenteredObservable
    (radius : Nat)
    (Codomain : Set)
    (codomain : Parity.ParityCodomain Codomain) : Set₁ where
  field
    observable : Centered.CenteredBlockPoint4 radius → Codomain
    odd :
      Parity.OddUnder
        (centeredBlockInvolution radius)
        codomain
        observable

open OddCenteredObservable public

centeredOddPairCancels :
  ∀ {radius Codomain}
    {codomain : Parity.ParityCodomain Codomain} →
  (dataSet : OddCenteredObservable radius Codomain codomain) →
  ∀ point →
  Parity.Equivalent codomain
    (Parity.add codomain
      (observable dataSet point)
      (observable dataSet (negateCenteredBlock4 point)))
    (Parity.zero codomain)
centeredOddPairCancels dataSet =
  Parity.oddPairCancels (odd dataSet)

cmp109CenteredCoordinateInvolutionLevel : ProofLevel
cmp109CenteredCoordinateInvolutionLevel = machineChecked

cmp109CenteredOddPairCancellationLevel : ProofLevel
cmp109CenteredOddPairCancellationLevel = machineChecked

physicalCenteredObservableParityLevel : ProofLevel
physicalCenteredObservableParityLevel = conditional
