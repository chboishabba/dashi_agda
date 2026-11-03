module DASHI.Physics.YangMills.YMClayNativeBlockedPositiveHolonomyGaugeExact where

------------------------------------------------------------------------
-- R445.P01/P02: ACTUAL native positive-link path on the original
-- 4D SU(N) bond carrier, welded to the already-constructed Bałaban
-- coarse (M) × block-offset (L) site decomposition.
--
-- Reuses (without rebuilding):
-- * BalabanPeriodicTorus4Carrier: original positive bonds/sites/axes;
-- * BalabanClayGate4PeriodicBondPathBianchiExact:
--     selected gauge transformation, associative group,
--     path composition/cancellation;
-- * BalabanBlockedPeriodicLattice and
--     YMClayNativeBlockedPeriodicBondWeldExact: exact coarse × offset iso.
--
-- Key genuine construction:
--   blocked U(y,axis) = ordered product of L ORIGINAL positive links
--   along the fine positive axis, beginning at fine(M*y,zero-offset).
-- This is a GROUP-VALUED field, not a set of bond labels.
--
-- The long positive path gauge law is PROVED from original link group
-- associativity and inverses, with NO separately assumed path covariance.
-- It agrees with the existing selected signed-path holonomy for positive
-- directions, rather than changing the Wilson-action semantics.
--
-- One precisely identified geometric equation is still a named input:
-- L repeated fine positive steps from the block origin land at the
-- next coarse block origin (including periodic wrap). Supplying that
-- arithmetic theorem gives the ACTUAL coarse gauge transformation law.
--
-- Not established here: non-Abelian Wilson-action blocking identity,
-- Gibbs pushforward/disintegration, reflection-compatible half-space
-- paths, a(n), CMP116 mixed-J decay, continuum limits, or OS mass gap.
-- This module cannot be promoted to Clay from finite gauge algebra.
-- Original attribution: Wilson, Bałaban, and existing DASHI proofs.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
import Data.Fin.Base as Fin
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Torus
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bond
import DASHI.Physics.YangMills.P06FaceCubeTorusGeometry as Cube
import DASHI.Physics.YangMills.BalabanBlockedPeriodicLattice as Block
import DASHI.Physics.YangMills.YMClayNativeBlockedPeriodicBondWeldExact as Weld

-- Signed directions use the SAME original axis and positive orientation as
-- Bond.walkStep / Bond.pathHolonomy, not a reconstructed arrow type.
positiveDirections : Nat → Torus.Axis4 → List (Torus.Product Torus.Axis4 Agda.Builtin.Bool.Bool)
positiveDirections zero axis = []
positiveDirections (suc k) axis =
  Torus.pair axis true ∷ positiveDirections k axis

-- Exact selected positive-step endpoint, same original periodic geometry.
positiveSteps :
  ∀ {n} →
  Torus.periodicTorus4Definition (suc n) →
  Torus.Axis4 → Nat →
  Torus.periodicTorus4Definition (suc n)
positiveSteps site axis zero = site
positiveSteps site axis (suc k) =
  positiveSteps (Bond.positiveStep site axis) axis k

module _ {Value : Set} (group : Bond.ExactLinkGroup Value) where

  -- This is a literal ordered product on the ORIGINAL positive-bond field.
  positiveHolonomy :
    ∀ {n} →
    Bond.PeriodicBondField n Value →
    Torus.periodicTorus4Definition (suc n) →
    Torus.Axis4 → Nat → Value
  positiveHolonomy field site axis zero = Bond.identity group
  positiveHolonomy field site axis (suc k) =
    Bond.multiply group (field (Torus.pair site axis))
      (positiveHolonomy field (Bond.positiveStep site axis) axis k)

  -- Prove native gauge covariance for ANY positive path by induction.
  -- No signed-negative inverse covariance record is required here.
  positiveHolonomyGaugeCovariant :
    ∀ {n}
      (field : Bond.PeriodicBondField n Value)
      (gamma : Bond.PeriodicSiteGauge n Value)
      site axis k →
    positiveHolonomy
      (Bond.transformedBondBase group field gamma) site axis k
    ≡
    Bond.multiply group
      (Bond.multiply group
        (gamma site) (positiveHolonomy field site axis k))
      (Bond.inverse group (gamma (positiveSteps site axis k)))
  positiveHolonomyGaugeCovariant field gamma site axis zero =
    Bond.conjugateIdentity group (gamma site)
  positiveHolonomyGaugeCovariant field gamma site axis (suc k) =
    trans
      (cong
        (Bond.multiply group
          (Bond.transformedBondBase group field gamma
            (Torus.pair site axis)))
        (positiveHolonomyGaugeCovariant field gamma
          (Bond.positiveStep site axis) axis k))
      (Bond.composeGaugeSegments group
        (gamma site)
        (gamma (Bond.positiveStep site axis))
        (gamma (positiveSteps site axis (suc k)))
        (field (Torus.pair site axis))
        (positiveHolonomy field
          (Bond.positiveStep site axis) axis k))

  -- Explicit same-object agreement with the existing old signed-path
  -- source on its positive-axis sublanguage.
  positiveHolonomyIsSelectedPath :
    ∀ {n}
      (realization : Bond.PeriodicBondGaugeRealization n Value group)
      site axis k →
    positiveHolonomy (Bond.bondField realization) site axis k
    ≡
    Bond.pathHolonomy realization site (positiveDirections k axis)
  positiveHolonomyIsSelectedPath realization site axis zero = refl
  positiveHolonomyIsSelectedPath realization site axis (suc k) =
    cong
      (Bond.multiply group
        (Bond.bondField realization (Torus.pair site axis)))
      (positiveHolonomyIsSelectedPath realization
        (Bond.positiveStep site axis) axis k)

-- Concrete ORIGINAL blocked field from the proven M×L carrier.
module _
    {m l : Nat}
    {Value : Set}
    (group : Bond.ExactLinkGroup Value)
  where

  Coarse : Set
  Coarse = Torus.periodicTorus4Definition (suc m)

  -- Definitional natural-number identity:
  -- (suc m)*(suc l) = suc (l + m*(suc l)).
  FineTail : Nat
  FineTail = l + m * suc l

  Fine : Set
  Fine = Torus.periodicTorus4Definition (suc FineTail)

  zeroOffset : Cube.Cube4 (suc l)
  zeroOffset = Cube.cube4 Fin.zero Fin.zero Fin.zero Fin.zero

  fineBlockOrigin : Coarse → Fine
  fineBlockOrigin site =
    Weld.unblockNativeSite (suc m) (suc l)
      (Block.blockedCube4 (Weld.siteToCube site) zeroOffset)

  positiveBlockDirections : Torus.Axis4 →
    List (Torus.Product Torus.Axis4 Agda.Builtin.Bool.Bool)
  positiveBlockDirections axis = positiveDirections (suc l) axis

  -- Source-defined selected directed coarse link on *actual* original
  -- source bonds, rather than an independent R445 coarse-field oracle.
  nativeBlockedPositiveLinks :
    Bond.PeriodicBondField FineTail Value →
    Bond.PeriodicBondField m Value
  nativeBlockedPositiveLinks fineField (Torus.pair site axis) =
    positiveHolonomy group fineField
      (fineBlockOrigin site) axis (suc l)

  nativeBlockedCoarseGauge :
    Bond.PeriodicSiteGauge FineTail Value →
    Bond.PeriodicSiteGauge m Value
  nativeBlockedCoarseGauge fineGauge site =
    fineGauge (fineBlockOrigin site)

  -- Exact group-valued coarse field transformation, leaving the endpoint
  -- recorded as the ACTUAL L-step fine-walk rather than simply assuming
  -- it is the coarse successor.
  nativeBlockedGaugeLawAtFineEndpoint :
    ∀
      (fineField : Bond.PeriodicBondField FineTail Value)
      (fineGauge : Bond.PeriodicSiteGauge FineTail Value)
      site axis →
    nativeBlockedPositiveLinks
      (Bond.transformedBondBase group fineField fineGauge)
      (Torus.pair site axis)
    ≡
    Bond.multiply group
      (Bond.multiply group
        (nativeBlockedCoarseGauge fineGauge site)
        (nativeBlockedPositiveLinks fineField
          (Torus.pair site axis)))
      (Bond.inverse group
        (fineGauge
          (positiveSteps (fineBlockOrigin site) axis (suc l))))
  nativeBlockedGaugeLawAtFineEndpoint fineField fineGauge site axis =
    positiveHolonomyGaugeCovariant group
      fineField fineGauge (fineBlockOrigin site) axis (suc l)

  -- SINGLE explicit remaining GEOMETRIC endpoint theorem. Its type
  -- speaks about original sites and original positive steps only.
  BlockEndpointCompatibility : Set
  BlockEndpointCompatibility =
    ∀ site axis →
      positiveSteps (fineBlockOrigin site) axis (suc l)
      ≡ fineBlockOrigin (Bond.positiveStep site axis)

  -- Once endpoint compatibility is proved, the link transform is the
  -- SAME original Bond.transformedBondBase on the coarser torus.
  nativeBlockedGaugeLawOnCoarse :
    BlockEndpointCompatibility →
    ∀
      (fineField : Bond.PeriodicBondField FineTail Value)
      (fineGauge : Bond.PeriodicSiteGauge FineTail Value)
      (coarseBond : Torus.PositiveBond (suc m)) →
    nativeBlockedPositiveLinks
      (Bond.transformedBondBase group fineField fineGauge)
      coarseBond
    ≡
    Bond.transformedBondBase group
      (nativeBlockedPositiveLinks fineField)
      (nativeBlockedCoarseGauge fineGauge)
      coarseBond
  nativeBlockedGaugeLawOnCoarse compatible
      fineField fineGauge (Torus.pair site axis) =
    trans
      (nativeBlockedGaugeLawAtFineEndpoint
        fineField fineGauge site axis)
      (cong
        (λ endpoint →
          Bond.multiply group
            (Bond.multiply group
              (nativeBlockedCoarseGauge fineGauge site)
              (nativeBlockedPositiveLinks fineField
                (Torus.pair site axis)))
            (Bond.inverse group (fineGauge endpoint)))
        (compatible site axis))
