module DASHI.Physics.YangMills.YMClayNativeBlockedSU2PathHolonomyGaugeExact where

-- R445.P01/P02: *ORIGINAL* native finite gauge links -> true L-step
-- ordered path holonomy -> blocked periodic four-torus coordinates ->
-- gauge-covariant blocked link. Not an independent link-label surrogate.
--
-- Reuse: native cyclic/Fin and blocked-bond codecs (#1444);
-- BalabanClayGate4PeriodicBondPathBianchiExact.pathHolonomy and
-- pathSiteGaugeCancellation (existing original owners);
-- BalabanClayGate4PeriodicCoordinateClosureExact.periodicStepInverseLaws,
-- BalabanClayGate4PeriodicOrientedLinkCovarianceExact, and the
-- constructed Rational SU(2) exact group laws.
--
-- This has no local postulates and no fabricated physical integration.
-- Transitive old source imports lack verified --safe closure, so this
-- file deliberately DOES NOT CLAIM golden/kernel acceptance.
--
-- Still open: geometric identification of this walked endpoint with the
-- chosen nearest-neighbour coarse axis; physical lattice Wilson action
-- refinement, reflection positivity, measure disintegration, CMP119,
-- uniform estimates, continuum/infinite-volume OS and Clay mass gap.

open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Torus
import DASHI.Physics.YangMills.BalabanRootedPolymerWordEntropyExact as Word
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Path
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicCoordinateClosureExact as Coordinate
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicOrientedLinkCovarianceExact as Oriented
import DASHI.Physics.YangMills.BalabanClayGate4RationalSU2ExactGroupLaws as SU2Law
import DASHI.Physics.YangMills.BalabanSU2RationalWilsonLargeFieldGapExact as SU2
import DASHI.Physics.YangMills.YMClayNativeBlockedPeriodicBondWeldExact as Block

-- Literal ordered L-edge axial path. This is a NONCOMMUTATIVE ordered
-- holonomy, not a direct multiplication of averaged link coordinates.
repeatPositive : Nat → Torus.Axis4 → List Word.SignedAxis4
repeatPositive zero axis = []
repeatPositive (suc L) axis =
  Path.positiveDirection axis ∷ repeatPositive L axis

-- The equality of side-lengths is a genuine lattice-size constraint:
-- path calculus labels side (suc n), Bałaban blocks label side M*L.
-- We transport actual original torus sites between THESE EXACT types.
transportThere :
  ∀ {a b} (eq : a ≡ b) →
  Torus.periodicTorus4Definition a →
  Torus.periodicTorus4Definition b
transportThere eq =
  subst Torus.periodicTorus4Definition eq

transportBack :
  ∀ {a b} (eq : a ≡ b) →
  Torus.periodicTorus4Definition b →
  Torus.periodicTorus4Definition a
transportBack eq =
  subst Torus.periodicTorus4Definition (sym eq)

transportBackThere :
  ∀ {a b} (eq : a ≡ b)
    (site : Torus.periodicTorus4Definition a) →
  transportBack eq (transportThere eq site) ≡ site
transportBackThere refl site = refl

nativeStart :
  (M L n : Nat) (sameSide : suc n ≡ M * L) →
  Block.BlockedCube4 M L → Path.Periodic.PeriodicBlock n
nativeStart M L n sameSide blocked =
  transportBack sameSide (Block.unblockNativeSite M L blocked)

nativeBlock :
  (M L n : Nat) (sameSide : suc n ≡ M * L) →
  Path.Periodic.PeriodicBlock n → Block.BlockedCube4 M L
nativeBlock M L n sameSide site =
  Block.blockNativeSite M L (transportThere sameSide site)

nativeStartNativeBlock :
  ∀ M L n (sameSide : suc n ≡ M * L)
    (site : Path.Periodic.PeriodicBlock n) →
  nativeStart M L n sameSide
    (nativeBlock M L n sameSide site) ≡ site
nativeStartNativeBlock M L n sameSide site =
  trans
    (cong (transportBack sameSide)
      (Block.unblockNativeSiteAfterBlock M L
        (transportThere sameSide site)))
    (transportBackThere sameSide site)

-- True original rational SU(2) group and constructed oriented-link
-- covariance. No independent input of negative-link gauge laws.
rationalSU2NativeRealization :
  (n : Nat)
  (links : Path.PeriodicBondField n SU2.RationalUnitQuaternion)
  (gauge : Path.PeriodicSiteGauge n SU2.RationalUnitQuaternion) →
  Path.PeriodicBondGaugeRealization
    n SU2.RationalUnitQuaternion SU2Law.rationalSU2ExactLinkGroup
rationalSU2NativeRealization n links gauge =
  Oriented.literalPeriodicBondGaugeRealization
    SU2Law.rationalSU2ExactLinkGroup
    (Coordinate.periodicStepInverseLaws n) links gauge

module _
  (M L n : Nat) (sameSide : suc n ≡ M * L)
  {Value : Set}
  (group : Path.ExactLinkGroup Value)
  (realization : Path.PeriodicBondGaugeRealization n Value group)
  where

  BlockedSite : Set
  BlockedSite = Block.BlockedCube4 M L

  BlockedBond : Set
  BlockedBond = Block.BlockedPositiveBond M L

  nativeGaugeAtBlock : BlockedSite → Value
  nativeGaugeAtBlock blocked =
    Path.gauge realization (nativeStart M L n sameSide blocked)

  -- This is the original positive-bond field evaluated along a literal
  -- ordered L-step path, with original group multiplication.
  nativeBlockedPathLink : BlockedBond → Value
  nativeBlockedPathLink (Torus.pair blocked axis) =
    Path.pathHolonomy realization
      (nativeStart M L n sameSide blocked)
      (repeatPositive L axis)

  -- Actual gauge-transformed original link field, no new action.
  nativeTransformedBlockedPathLink : BlockedBond → Value
  nativeTransformedBlockedPathLink (Torus.pair blocked axis) =
    Path.transformedPathHolonomy realization
      (nativeStart M L n sameSide blocked)
      (repeatPositive L axis)

  -- The end point is computed from the selected path and immediately
  -- re-encoded into the ORIGINAL Bałaban blocked coordinates.
  nativeBlockedPathDestination : BlockedBond → BlockedSite
  nativeBlockedPathDestination (Torus.pair blocked axis) =
    nativeBlock M L n sameSide
      (Path.walk (nativeStart M L n sameSide blocked)
        (repeatPositive L axis))

  destinationGaugeMatchesOriginalPath :
    (bond : BlockedBond) →
    nativeGaugeAtBlock (nativeBlockedPathDestination bond)
    ≡
    Path.gauge realization
      (Path.walk
        (nativeStart M L n sameSide (Torus.first bond))
        (repeatPositive L (Torus.second bond)))
  destinationGaugeMatchesOriginalPath (Torus.pair blocked axis) =
    cong (Path.gauge realization)
      (nativeStartNativeBlock M L n sameSide
        (Path.walk (nativeStart M L n sameSide blocked)
          (repeatPositive L axis)))

  -- Constructed from original n-link path gauge-cancellation theorem:
  -- no assumed blocked-equivariance interface.
  nativeBlockedPathGaugeCovariant :
    (bond : BlockedBond) →
    nativeTransformedBlockedPathLink bond
    ≡
    Path.multiply group
      (Path.multiply group
        (nativeGaugeAtBlock (Torus.first bond))
        (nativeBlockedPathLink bond))
      (Path.inverse group
        (nativeGaugeAtBlock (nativeBlockedPathDestination bond)))
  nativeBlockedPathGaugeCovariant (Torus.pair blocked axis) =
    trans
      (Path.pathSiteGaugeCancellation realization
        (nativeStart M L n sameSide blocked)
        (repeatPositive L axis))
      (cong
        (λ endGauge →
          Path.multiply group
            (Path.multiply group
              (nativeGaugeAtBlock blocked)
              (nativeBlockedPathLink (Torus.pair blocked axis)))
            (Path.inverse group endGauge))
        (sym
          (destinationGaugeMatchesOriginalPath
            (Torus.pair blocked axis))))

  -- One-step check: the coarse holonomy for L=1 is literally the
  -- ORIGINAL native positive bond, not an unrelated endpoint proxy.
  -- General L retains the same path multiplication and orientation.

-- Chosen original Rational SU(2) witness: all group laws, oriented
-- negative links and endpoint cancellation are constructed in prior owners.
-- Only the user's actual fine link field and gauge function remain inputs.
rationalSU2BlockedPathGaugeCovariant :
  ∀ M L n (sameSide : suc n ≡ M * L)
    (links : Path.PeriodicBondField n SU2.RationalUnitQuaternion)
    (gauge : Path.PeriodicSiteGauge n SU2.RationalUnitQuaternion)
    (bond : Block.BlockedPositiveBond M L) →
    nativeTransformedBlockedPathLink M L n sameSide
      SU2Law.rationalSU2ExactLinkGroup
      (rationalSU2NativeRealization n links gauge) bond
    ≡
    Path.multiply SU2Law.rationalSU2ExactLinkGroup
      (Path.multiply SU2Law.rationalSU2ExactLinkGroup
        (nativeGaugeAtBlock M L n sameSide
          SU2Law.rationalSU2ExactLinkGroup
          (rationalSU2NativeRealization n links gauge)
          (Torus.first bond))
        (nativeBlockedPathLink M L n sameSide
          SU2Law.rationalSU2ExactLinkGroup
          (rationalSU2NativeRealization n links gauge) bond))
      (Path.inverse SU2Law.rationalSU2ExactLinkGroup
        (nativeGaugeAtBlock M L n sameSide
          SU2Law.rationalSU2ExactLinkGroup
          (rationalSU2NativeRealization n links gauge)
          (nativeBlockedPathDestination M L n sameSide
            SU2Law.rationalSU2ExactLinkGroup
            (rationalSU2NativeRealization n links gauge) bond)))
rationalSU2BlockedPathGaugeCovariant M L n sameSide links gauge bond =
  nativeBlockedPathGaugeCovariant M L n sameSide
    SU2Law.rationalSU2ExactLinkGroup
    (rationalSU2NativeRealization n links gauge) bond

-- Source status: SOURCE-WRITTEN, exact-head Agda NOT RUN. This theorem
-- does not claim the walked endpoint equals a physically selected
-- coarse nearest-neighbour step, that Haar disintegrates along this
-- blocking, or that any lattice gap survives the a->0 limit.
