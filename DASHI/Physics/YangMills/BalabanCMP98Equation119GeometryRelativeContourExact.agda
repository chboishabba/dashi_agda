{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Equation119GeometryRelativeContourExact where

------------------------------------------------------------------------
-- CMP98 EQ. (119): GEOMETRY-ONLY RELATIVE CONTOUR
--
-- R155 constructs
--
--   U(Gamma_{c,x}) U(c)^-1
--
-- but its source record also carries perturbation, qSource and differential
-- data that are not read by this construction.  This owner isolates the exact
-- geometry/group fragment so the physical Path13 two-carrier lane can derive
-- its principal Y_x without reintroducing the historical one-carrier source.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (_++_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bond
import DASHI.Physics.YangMills.BalabanClayGate4CMP109PeriodicContourFamilyInstantiationExact as Periodic
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredPeriodicEmbeddingExact as Embed
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredOddBlockCarrierExact as Centered
import DASHI.Physics.YangMills.BalabanRootedPolymerWordEntropyExact as Word
import DASHI.Physics.YangMills.BalabanCMP98Equation119RelativeContourYRound155Exact as R155

record Equation119GeometrySource
    (n : Nat) (Value : Set) (group : Bond.ExactLinkGroup Value) : Set₁ where
  field
    realization : Nat → Bond.PeriodicBondGaugeRealization n Value group
    minusEmbedding : Nat → Embed.CenteredPeriodicNoWrapEmbedding n 6
    coarseSegment : Nat →
      DASHI.Physics.YangMills.BalabanClayGate4CMP109ShortestContourEnumerationExact.AxisSegment

open Equation119GeometrySource public

literalGammaWord :
  ∀ {n Value group} →
  Equation119GeometrySource n Value group →
  Nat → Centered.CenteredBlockPoint4 6 → List Word.SignedAxis4
literalGammaWord source step point =
  Embed.canonicalCenteredContourWord point
  ++ Periodic.segmentWord (coarseSegment source step)
  ++ R155.reverseWord (Embed.canonicalCenteredContourWord point)

coarseBackgroundHolonomy :
  ∀ {n Value group} →
  Equation119GeometrySource n Value group → Nat → Value
coarseBackgroundHolonomy source step =
  Bond.pathHolonomy
    (realization source step)
    (Embed.embeddingCentre (minusEmbedding source step))
    (Periodic.segmentWord (coarseSegment source step))

literalGammaHolonomy :
  ∀ {n Value group} →
  Equation119GeometrySource n Value group →
  Nat → Centered.CenteredBlockPoint4 6 → Value
literalGammaHolonomy source step point =
  Bond.pathHolonomy
    (realization source step)
    (Embed.embeddingCentre (minusEmbedding source step))
    (literalGammaWord source step point)

relativeContourElement :
  ∀ {n Value group} →
  Equation119GeometrySource n Value group →
  Nat → Centered.CenteredBlockPoint4 6 → Value
relativeContourElement {group = group} source step point =
  Bond.multiply group
    (literalGammaHolonomy source step point)
    (Bond.inverse group (coarseBackgroundHolonomy source step))

relativeContourElementIsCMP98Product :
  ∀ {n Value group}
    (source : Equation119GeometrySource n Value group)
    step point →
  relativeContourElement source step point
  ≡ Bond.multiply group
      (literalGammaHolonomy source step point)
      (Bond.inverse group (coarseBackgroundHolonomy source step))
relativeContourElementIsCMP98Product source step point = refl

cmp98Equation119GeometryOnlyRelativeContourLevel : ProofLevel
cmp98Equation119GeometryOnlyRelativeContourLevel = machineChecked
