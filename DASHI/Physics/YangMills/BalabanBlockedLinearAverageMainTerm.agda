module DASHI.Physics.YangMills.BalabanBlockedLinearAverageMainTerm where

------------------------------------------------------------------------
-- Literal one-step blocked linear average: source main term.
--
-- The fine torus has side M * L, decomposed exactly into an M-side coarse
-- torus and L^4 offsets.  A coarse vertex y is embedded at offset zero, and
-- the canonical coordinate-order samples traverse every x in B(y), followed
-- by the L-step segment parallel to the coarse bond.
--
-- Thus `blockedLinearAverageMainTerm` is the finite-lattice realization of
-- the leading term in CMP 98 (125):
--
--   sum_{x in B(c-)} L^{-(d+1)} (R_{0,c-} A)([x,x']).
--
-- The weight is explicit because the scalar carrier is not concrete yet.
-- Gauge covariance is proved from the previously established path laws.
-- The additional analytic-adjoint correction terms in CMP 98 (124) are not
-- silently included.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; suc; _*_)
open import Data.Fin.Base using () renaming (zero to fzero)
open import Data.Nat.Base using (NonZero)

open import DASHI.Physics.YangMills.P06FaceCubeTorusGeometry using
  ( Cube4
  ; cube4
  ; Axis4
  )
open import DASHI.Physics.YangMills.BalabanBlockedPeriodicLattice using
  ( blockedCube4
  ; finePoint
  )
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
  ( ScalarAdjointLinearModule
  ; linear
  ; Scalar
  )
open import DASHI.Physics.YangMills.BalabanCanonicalBlockPathSamples using
  ( canonicalLinearBlockPathAverage
  ; canonicalLinearBlockPathAverageGaugeCovariant
  )

zeroBlockOffset :
  ∀ {L : Nat} →
  Cube4 (suc L)
zeroBlockOffset = cube4 fzero fzero fzero fzero

blockOrigin :
  ∀ {M L : Nat} →
  Cube4 M →
  Cube4 (M * suc L)
blockOrigin {M = M} {L = L} coarse =
  finePoint {M = M} {L = suc L}
    (blockedCube4 coarse zeroBlockOffset)

restrictedCoarseGauge :
  ∀ {M L : Nat}
  (group : GroupStructure) →
  GaugeFunction4 (M * suc L) group →
  Cube4 M →
  DASHI.Physics.YangMills.BalabanPeriodicGaugeTransport.Carrier group
restrictedCoarseGauge group gauge coarse =
  gauge (blockOrigin coarse)

BlockedAdjointBondField4 :
  (M L : Nat) →
  (group : GroupStructure) →
  ScalarAdjointLinearModule group →
  Set
BlockedAdjointBondField4 M L group scalarLinear =
  Cube4 M → Axis4 →
  Vector (additive (linear scalarLinear))

blockedLinearAverageMainTerm :
  ∀ {M L : Nat} {{_ : NonZero (M * suc L)}}
  (group : GroupStructure) →
  (scalarLinear : ScalarAdjointLinearModule group) →
  (weight : Scalar scalarLinear) →
  (U : DirectedGaugeField4 (M * suc L) group) →
  (A : DirectedAdjointBondField4 (M * suc L) group
    (linear scalarLinear)) →
  BlockedAdjointBondField4 M L group scalarLinear
blockedLinearAverageMainTerm
  {L = L} group scalarLinear weight U A coarse coarseAxis =
  canonicalLinearBlockPathAverage
    group scalarLinear weight U A
    (suc L) coarseAxis (blockOrigin coarse)

blockedLinearAverageMainTermGaugeCovariant :
  ∀ {M L : Nat} {{_ : NonZero (M * suc L)}}
  (group : GroupStructure) →
  (scalarLinear : ScalarAdjointLinearModule group) →
  (weight : Scalar scalarLinear) →
  (gauge : GaugeFunction4 (M * suc L) group) →
  (U : DirectedGaugeField4 (M * suc L) group) →
  (A : DirectedAdjointBondField4 (M * suc L) group
    (linear scalarLinear)) →
  (coarse : Cube4 M) →
  (coarseAxis : Axis4) →
  blockedLinearAverageMainTerm
    group scalarLinear weight
    (gaugeTransformBond group gauge U)
    (transformAdjointBondField
      group (linear scalarLinear) gauge A)
    coarse coarseAxis
  ≡
  action (additive (linear scalarLinear))
    (restrictedCoarseGauge group gauge coarse)
    (blockedLinearAverageMainTerm
      group scalarLinear weight U A coarse coarseAxis)
blockedLinearAverageMainTermGaugeCovariant
  {L = L} group scalarLinear weight gauge U A coarse coarseAxis =
  canonicalLinearBlockPathAverageGaugeCovariant
    group scalarLinear weight gauge U A
    (suc L) coarseAxis (blockOrigin coarse)
