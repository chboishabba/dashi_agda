module DASHI.Physics.YangMills.BalabanCanonicalBlockPathSamples where

------------------------------------------------------------------------
-- Canonical coordinate-order block paths for the linearized average.
--
-- CMP 95 (1.7)--(1.8) and CMP 98 (14), (124)--(125) use coordinate-order
-- paths from the coarse-bond source to every point in its L-block, followed by
-- an L-step segment parallel to the coarse bond.  This module constructs those
-- paths literally on `Cube4 N`:
--
--   root --F(root,x)--> x --[x,x']--> x',   x' = x + L e_mu.
--
-- The block is enumerated by `Cube4 L`; each coordinate is interpreted as the
-- corresponding number of positive fine-lattice steps.  On the periodic torus
-- the construction remains total even when a chosen patch wraps.
--
-- The resulting sample list directly instantiates the already proved
-- gauge-covariant finite block-path average.  The scalar normalization
-- L^{-(d+1)} remains an explicit scalar input until the real/matrix carrier is
-- concretized.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Fin.Base using (toℕ)
open import Data.List.Base using (List; map)
open import Data.Nat.Base using (NonZero)

open import DASHI.Physics.YangMills.P06FaceCubeTorusGeometry using
  ( Cube4
  ; cube4
  ; Axis4
  ; axis₀
  ; axis₁
  ; axis₂
  ; axis₃
  ; shiftForward
  )
open import DASHI.Physics.YangMills.BalabanPeriodicLatticeBonds using
  ( positiveBond )
open import DASHI.Physics.YangMills.BalabanPeriodicLatticePaths using
  ( LatticePath4
  ; empty
  ; _▷_
  ; append
  )
open import DASHI.Physics.YangMills.BalabanPeriodicLatticeEnumeration using
  ( allCube4 )
open import DASHI.Physics.YangMills.BalabanPeriodicGaugeTransport using
  ( GroupStructure )
open import DASHI.Physics.YangMills.BalabanGaugeTransformationCovariance using
  ( DirectedGaugeField4
  ; GaugeFunction4
  ; gaugeTransformBond
  )
open import DASHI.Physics.YangMills.BalabanLatticeAdjointCovariantDerivative using
  ( Vector
  ; action
  )
open import DASHI.Physics.YangMills.BalabanCovariantPathIntegral using
  ( additive
  ; DirectedAdjointBondField4
  ; transformAdjointBondField
  )
open import DASHI.Physics.YangMills.BalabanLinearBlockPathAverage using
  ( RootedSegmentSample
  ; rootedSegment
  ; ScalarAdjointLinearModule
  ; linear
  ; Scalar
  ; linearBlockPathAverage
  ; linearBlockPathAverageGaugeCovariant
  )

shiftForwardN :
  ∀ {N : Nat} {{_ : NonZero N}} →
  Nat → Axis4 → Cube4 N → Cube4 N
shiftForwardN zero axis x = x
shiftForwardN (suc count) axis x =
  shiftForwardN count axis (shiftForward axis x)

axisPath :
  ∀ {N : Nat} {{_ : NonZero N}}
  (count : Nat) (axis : Axis4) (x : Cube4 N) →
  LatticePath4 x (shiftForwardN count axis x)
axisPath zero axis x = empty
axisPath (suc count) axis x =
  positiveBond x axis ▷
  axisPath count axis (shiftForward axis x)

offsetPoint :
  ∀ {N L : Nat} {{_ : NonZero N}} →
  Cube4 L → Cube4 N → Cube4 N
offsetPoint (cube4 o₀ o₁ o₂ o₃) root =
  shiftForwardN (toℕ o₃) axis₃
    (shiftForwardN (toℕ o₂) axis₂
      (shiftForwardN (toℕ o₁) axis₁
        (shiftForwardN (toℕ o₀) axis₀ root)))

offsetPath :
  ∀ {N L : Nat} {{_ : NonZero N}}
  (offset : Cube4 L) (root : Cube4 N) →
  LatticePath4 root (offsetPoint offset root)
offsetPath (cube4 o₀ o₁ o₂ o₃) root =
  append
    (axisPath (toℕ o₀) axis₀ root)
    (append
      (axisPath (toℕ o₁) axis₁ after₀)
      (append
        (axisPath (toℕ o₂) axis₂ after₁)
        (axisPath (toℕ o₃) axis₃ after₂)))
  where
    after₀ : Cube4 _
    after₀ = shiftForwardN (toℕ o₀) axis₀ root

    after₁ : Cube4 _
    after₁ = shiftForwardN (toℕ o₁) axis₁ after₀

    after₂ : Cube4 _
    after₂ = shiftForwardN (toℕ o₂) axis₂ after₁

canonicalRootedSegment :
  ∀ {N L : Nat} {{_ : NonZero N}}
  (blockLength : Nat) →
  (coarseAxis : Axis4) →
  (root : Cube4 N) →
  Cube4 L →
  RootedSegmentSample root
canonicalRootedSegment blockLength coarseAxis root offset =
  rootedSegment
    (offsetPoint offset root)
    (shiftForwardN blockLength coarseAxis (offsetPoint offset root))
    (offsetPath offset root)
    (axisPath blockLength coarseAxis (offsetPoint offset root))

canonicalBlockSamples :
  ∀ {N : Nat} {{_ : NonZero N}}
  (blockLength : Nat) →
  (coarseAxis : Axis4) →
  (root : Cube4 N) →
  List (RootedSegmentSample root)
canonicalBlockSamples blockLength coarseAxis root =
  map
    (canonicalRootedSegment blockLength coarseAxis root)
    (allCube4 blockLength)

canonicalLinearBlockPathAverage :
  ∀ {N : Nat} {{_ : NonZero N}}
  (group : GroupStructure) →
  (scalarLinear : ScalarAdjointLinearModule group) →
  (weight : Scalar scalarLinear) →
  (U : DirectedGaugeField4 N group) →
  (A : DirectedAdjointBondField4 N group
    (linear scalarLinear)) →
  (blockLength : Nat) →
  (coarseAxis : Axis4) →
  (root : Cube4 N) →
  Vector (additive (linear scalarLinear))
canonicalLinearBlockPathAverage
  group scalarLinear weight U A blockLength coarseAxis root =
  linearBlockPathAverage
    group scalarLinear weight U A
    (canonicalBlockSamples blockLength coarseAxis root)

canonicalLinearBlockPathAverageGaugeCovariant :
  ∀ {N : Nat} {{_ : NonZero N}}
  (group : GroupStructure) →
  (scalarLinear : ScalarAdjointLinearModule group) →
  (weight : Scalar scalarLinear) →
  (gauge : GaugeFunction4 N group) →
  (U : DirectedGaugeField4 N group) →
  (A : DirectedAdjointBondField4 N group
    (linear scalarLinear)) →
  (blockLength : Nat) →
  (coarseAxis : Axis4) →
  (root : Cube4 N) →
  canonicalLinearBlockPathAverage
    group scalarLinear weight
    (gaugeTransformBond group gauge U)
    (transformAdjointBondField
      group (linear scalarLinear) gauge A)
    blockLength coarseAxis root
  ≡
  action (additive (linear scalarLinear)) (gauge root)
    (canonicalLinearBlockPathAverage
      group scalarLinear weight U A
      blockLength coarseAxis root)
canonicalLinearBlockPathAverageGaugeCovariant
  group scalarLinear weight gauge U A
  blockLength coarseAxis root =
  linearBlockPathAverageGaugeCovariant
    group scalarLinear weight gauge U A
    (canonicalBlockSamples blockLength coarseAxis root)
