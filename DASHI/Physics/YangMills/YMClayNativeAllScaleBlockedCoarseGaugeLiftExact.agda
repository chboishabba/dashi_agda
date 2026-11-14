module DASHI.Physics.YangMills.YMClayNativeAllScaleBlockedCoarseGaugeLiftExact where

------------------------------------------------------------------------
-- R445.F09: all-M,L actual original four-torus coarse gauge LIFT.
--
-- For every M=suc m, L=suc l, the existing native block origin is
-- the zero-offset inverse of Bałaban's original M*L block decomposition.
-- Every coarse site gauge gamma therefore has a concrete fine lift
-- gamma_fine(x)=gamma(coarseOfFine(x)) which restricts to gamma at
-- ALL original coarse block origins, without a gauge-extension axiom.
--
-- The true all-scale group-valued blocked-link gauge theorem is obtained
-- from exactly one visible remaining geometric hypothesis:
-- Block.BlockEndpointCompatibility. This does NOT prove that latter
-- modular-repeated-successor arithmetic statement.
--
-- No group-specific assumptions beyond original ExactLinkGroup; no
-- finite-sum or continuous Haar, Wilson-measure disintegration, RP,
-- scaling estimates, continuum limit, OS spectral gap, or Clay theorem.
-- Mathematical provenance: Wilson and Bałaban. DASHI term ownership
-- reuses original native torus/block/path theorem sources.
-- SOURCE-WRITTEN; exact-head Agda kernel acceptance is not claimed.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc; _+_; _*_)
import Data.Fin.Base as Fin
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)

import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Torus
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bond
import DASHI.Physics.YangMills.P06FaceCubeTorusGeometry as Cube
import DASHI.Physics.YangMills.BalabanBlockedPeriodicLattice as Blocked
import DASHI.Physics.YangMills.YMClayNativeBlockedPeriodicBondWeldExact as Weld
import DASHI.Physics.YangMills.YMClayNativeBlockedPositiveHolonomyGaugeExact as Block

module _ {m l : Nat} where

  FineTail : Nat
  FineTail = l + m * suc l

  CoarseSite : Set
  CoarseSite = Torus.periodicTorus4Definition (suc m)

  FineSite : Set
  FineSite = Torus.periodicTorus4Definition (suc FineTail)

  zeroOffset : Cube.Cube4 (suc l)
  zeroOffset = Cube.cube4 Fin.zero Fin.zero Fin.zero Fin.zero

  geometricFineBlockOrigin : CoarseSite → FineSite
  geometricFineBlockOrigin site =
    Weld.unblockNativeSite (suc m) (suc l)
      (Blocked.blockedCube4 (Weld.siteToCube site) zeroOffset)

  geometricCoarseSiteOfFine : FineSite → CoarseSite
  geometricCoarseSiteOfFine fine =
    Weld.cubeToSite
      (Blocked.coarseCube
        (Weld.blockNativeSite (suc m) (suc l) fine))

  -- Proven for ALL M,L by the already-owned four-coordinate block iso.
  geometricCoarseAtFineOrigin :
    ∀ site →
    geometricCoarseSiteOfFine (geometricFineBlockOrigin site) ≡ site
  geometricCoarseAtFineOrigin site =
    trans
      (cong
        (λ blocked → Weld.cubeToSite (Blocked.coarseCube blocked))
        (Weld.blockNativeSiteAfterUnblock (suc m) (suc l)
          (Blocked.blockedCube4 (Weld.siteToCube site) zeroOffset)))
      (Weld.siteCubeRoundtrip site)

  -- One original coarse site gauge -> one original fine site gauge.
  liftCoarseSiteGauge :
    ∀ {Value : Set} →
    Bond.PeriodicSiteGauge m Value →
    Bond.PeriodicSiteGauge FineTail Value
  liftCoarseSiteGauge gamma fineSite =
    gamma (geometricCoarseSiteOfFine fineSite)

  originalBlockOriginIsGeometric :
    ∀ {Value : Set} (group : Bond.ExactLinkGroup Value) site →
    Block.fineBlockOrigin group site ≡ geometricFineBlockOrigin site
  originalBlockOriginIsGeometric group site = refl

  -- The ORIGINAL Block.nativeBlockedCoarseGauge has no loss of coarse
  -- site gauge freedom: the constructed lift restricts to gamma.
  originalBlockedGaugeLiftAt :
    ∀ {Value : Set}
      (group : Bond.ExactLinkGroup Value)
      (gamma : Bond.PeriodicSiteGauge m Value) site →
    Block.nativeBlockedCoarseGauge group
      (liftCoarseSiteGauge gamma) site ≡ gamma site
  originalBlockedGaugeLiftAt group gamma site =
    cong gamma (geometricCoarseAtFineOrigin site)

  originalCoarseGaugeTransformPointwise :
    ∀ {Value : Set}
      (group : Bond.ExactLinkGroup Value)
      (links : Bond.PeriodicBondField m Value)
      (left right : Bond.PeriodicSiteGauge m Value) →
    (∀ site → left site ≡ right site) →
    ∀ (bond : Torus.PositiveBond (suc m)) →
    Bond.transformedBondBase group links left bond
    ≡ Bond.transformedBondBase group links right bond
  originalCoarseGaugeTransformPointwise group links left right same
      (Torus.pair site axis) =
    cong₂
      (λ start finish →
        Bond.multiply group
          (Bond.multiply group start (links (Torus.pair site axis)))
          (Bond.inverse group finish))
      (same site)
      (same (Bond.positiveStep site axis))

  -- All-M,L pointwise gauge equivariance is now conditional ONLY on
  -- the outstanding actual original cyclic-step endpoint arithmetic.
  allCoarseGaugeEquivarianceFromEndpoint :
    ∀ {Value : Set}
      (group : Bond.ExactLinkGroup Value) →
    Block.BlockEndpointCompatibility group →
    (fine : Bond.PeriodicBondField FineTail Value)
    (gamma : Bond.PeriodicSiteGauge m Value)
    (coarseBond : Torus.PositiveBond (suc m)) →
    Block.nativeBlockedPositiveLinks group
      (Bond.transformedBondBase group fine
        (liftCoarseSiteGauge gamma))
      coarseBond
    ≡
    Bond.transformedBondBase group
      (Block.nativeBlockedPositiveLinks group fine)
      gamma coarseBond
  allCoarseGaugeEquivarianceFromEndpoint
      group endpoint fine gamma coarseBond =
    trans
      (Block.nativeBlockedGaugeLawOnCoarse group endpoint
        fine (liftCoarseSiteGauge gamma) coarseBond)
      (originalCoarseGaugeTransformPointwise group
        (Block.nativeBlockedPositiveLinks group fine)
        (Block.nativeBlockedCoarseGauge group
          (liftCoarseSiteGauge gamma))
        gamma
        (originalBlockedGaugeLiftAt group gamma)
        coarseBond)
