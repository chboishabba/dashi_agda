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
open import Data.Rational.Base using (ℚ)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Torus
import DASHI.Physics.YangMills.BalabanClayT2PeriodicBlockPolymerCarrierExact as Periodic
import DASHI.Physics.YangMills.BalabanBlockedPeriodicLattice as Blocked
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
  Blocked.BlockedCube4 M L → Periodic.PeriodicBlock n
nativeStart M L n sameSide blocked =
  transportBack sameSide (Block.unblockNativeSite M L blocked)

nativeBlock :
  (M L n : Nat) (sameSide : suc n ≡ M * L) →
  Periodic.PeriodicBlock n → Blocked.BlockedCube4 M L
nativeBlock M L n sameSide site =
  Block.blockNativeSite M L (transportThere sameSide site)

nativeStartNativeBlock :
  ∀ M L n (sameSide : suc n ≡ M * L)
    (site : Periodic.PeriodicBlock n) →
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
  BlockedSite = Blocked.BlockedCube4 M L

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

  ----------------------------------------------------------------------
  -- P06.L02 strengthened: FULL COMPOSABLE BLOCKED PATHS.
  --
  -- Crucially, intermediate sites are the ACTUAL computed reblocked
  -- endpoints. The type checker rejects an invalid naive concatenation.
  ----------------------------------------------------------------------

  data NativeBlockedWalk : BlockedSite → BlockedSite → Set where
    emptyNativeBlockedWalk :
      ∀ {site} → NativeBlockedWalk site site
    prependNativeBlockedLink :
      ∀ {finish} (bond : BlockedBond) →
      NativeBlockedWalk (nativeBlockedPathDestination bond) finish →
      NativeBlockedWalk (Torus.first bond) finish

  nativeWalkHolonomy :
    ∀ {start finish} → NativeBlockedWalk start finish → Value
  nativeWalkHolonomy emptyNativeBlockedWalk = Path.identity group
  nativeWalkHolonomy (prependNativeBlockedLink bond rest) =
    Path.multiply group
      (nativeBlockedPathLink bond)
      (nativeWalkHolonomy rest)

  nativeTransformedWalkHolonomy :
    ∀ {start finish} → NativeBlockedWalk start finish → Value
  nativeTransformedWalkHolonomy emptyNativeBlockedWalk =
    Path.identity group
  nativeTransformedWalkHolonomy (prependNativeBlockedLink bond rest) =
    Path.multiply group
      (nativeTransformedBlockedPathLink bond)
      (nativeTransformedWalkHolonomy rest)

  -- Derive endpoint gauge covariance for ALL typed composite blocked
  -- paths, with actual cancellation at every source-native intermediate
  -- site. This is NOT an assumed source-invariance field.
  nativeWalkGaugeCovariant :
    ∀ {start finish} (walk : NativeBlockedWalk start finish) →
    nativeTransformedWalkHolonomy walk
    ≡ Path.multiply group
        (Path.multiply group
          (nativeGaugeAtBlock start)
          (nativeWalkHolonomy walk))
        (Path.inverse group (nativeGaugeAtBlock finish))
  nativeWalkGaugeCovariant {start = start} emptyNativeBlockedWalk =
    Path.conjugateIdentity group (nativeGaugeAtBlock start)
  nativeWalkGaugeCovariant {finish = finish}
      (prependNativeBlockedLink bond rest) =
    let
      startGauge = nativeGaugeAtBlock (Torus.first bond)
      middleGauge = nativeGaugeAtBlock (nativeBlockedPathDestination bond)
      finishGauge = nativeGaugeAtBlock finish
      firstLink = nativeBlockedPathLink bond
      suffixLink = nativeWalkHolonomy rest
      transformedFirst = nativeTransformedBlockedPathLink bond
    in
    trans
      (cong
        (λ head → Path.multiply group head
          (nativeTransformedWalkHolonomy rest))
        (nativeBlockedPathGaugeCovariant bond))
      (trans
        (cong
          (λ tail →
            Path.multiply group
              (Path.multiply group
                (Path.multiply group startGauge firstLink)
                (Path.inverse group middleGauge))
              tail)
          (nativeWalkGaugeCovariant rest))
        (Path.composeGaugeSegments group
          startGauge middleGauge finishGauge firstLink suffixLink))

  -- A genuine closed blocked path has identical physical endpoint,
  -- so its holonomy transforms by one conjugation.
  nativeClosedWalkTransformsByConjugation :
    ∀ {site} (loop : NativeBlockedWalk site site) →
    nativeTransformedWalkHolonomy loop
    ≡ Path.multiply group
        (Path.multiply group
          (nativeGaugeAtBlock site) (nativeWalkHolonomy loop))
        (Path.inverse group (nativeGaugeAtBlock site))
  nativeClosedWalkTransformsByConjugation =
    nativeWalkGaugeCovariant

  -- Exactly the ORIGINAL Wilson class-function contract: a trace or
  -- other scalar observable must justify conjugation invariance.
  -- This input is not a Haar/continuum/source assumption.
  record NativeBlockedClassObservable (Scalar : Set) : Set₁ where
    field
      evaluate : Value → Scalar
      conjugationInvariant :
        ∀ gaugeAtBase loopValue →
        evaluate
          (Path.multiply group
            (Path.multiply group gaugeAtBase loopValue)
            (Path.inverse group gaugeAtBase))
        ≡ evaluate loopValue

  open NativeBlockedClassObservable public

  nativeClosedWilsonObservableGaugeInvariant :
    ∀ {Scalar : Set} {site}
      (observable : NativeBlockedClassObservable Scalar)
      (loop : NativeBlockedWalk site site) →
      evaluate observable (nativeTransformedWalkHolonomy loop)
      ≡ evaluate observable (nativeWalkHolonomy loop)
  nativeClosedWilsonObservableGaugeInvariant
      {site = site} observable loop =
    trans
      (cong (evaluate observable)
        (nativeClosedWalkTransformsByConjugation loop))
      (conjugationInvariant observable
        (nativeGaugeAtBlock site) (nativeWalkHolonomy loop))

  -- One-step check: the coarse holonomy for L=1 is literally the
  -- ORIGINAL native positive bond, not an unrelated endpoint proxy.
  -- General L retains the same path multiplication and orientation.

-- A true L=1 regression: the chosen blocked path is the original
-- positive bond itself, with the original field's SAME group value.
nativeBlockedOneStepExactlyOriginal :
  ∀ M n (sameSide : suc n ≡ M * 1)
    {Value : Set} (group : Path.ExactLinkGroup Value)
    (realization : Path.PeriodicBondGaugeRealization n Value group)
    (bond : Block.BlockedPositiveBond M 1) →
  nativeBlockedPathLink M 1 n sameSide group realization bond
  ≡ Path.bondField realization
      (Torus.pair
        (nativeStart M 1 n sameSide (Torus.first bond))
        (Torus.second bond))
nativeBlockedOneStepExactlyOriginal
    M n sameSide group realization (Torus.pair blocked axis) =
  Path.identityRight group
    (Path.bondField realization
      (Torus.pair (nativeStart M 1 n sameSide blocked) axis))

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

------------------------------------------------------------------------
-- R445 genuine ORIGINAL rational SU(2) *real Wilson trace* on closed
-- blocked paths, not merely an abstract supplied class-function witness.
-- Scalar is exactly the rational real component of the existing unit
-- quaternion owner. Trace cyclicity is proved by the rational ring solver.
------------------------------------------------------------------------

rationalSU2RealTraceCyclic :
  (a b : SU2.RationalUnitQuaternion) →
  SU2.realPart (SU2Law.multiplyRationalSU2 a b)
  ≡ SU2.realPart (SU2Law.multiplyRationalSU2 b a)
rationalSU2RealTraceCyclic a b =
  solve
    (SU2.realPart a ∷ SU2.imagI a ∷ SU2.imagJ a ∷ SU2.imagK a
      ∷ SU2.realPart b ∷ SU2.imagI b ∷ SU2.imagJ b ∷ SU2.imagK b ∷ [])

rationalSU2RealTraceConjugationInvariant :
  (g x : SU2.RationalUnitQuaternion) →
  SU2.realPart
    (SU2Law.multiplyRationalSU2
      (SU2Law.multiplyRationalSU2 g x)
      (SU2Law.inverseRationalSU2 g))
  ≡ SU2.realPart x
rationalSU2RealTraceConjugationInvariant g x =
  let group = SU2Law.rationalSU2ExactLinkGroup in
  trans
    (rationalSU2RealTraceCyclic
      (Path.multiply group g x) (Path.inverse group g))
    (trans
      (cong SU2.realPart
        (sym (Path.multiplyAssociative group
          (Path.inverse group g) g x)))
      (trans
        (cong
          (λ intermediate →
            SU2.realPart (Path.multiply group intermediate x))
          (Path.inverseLeft group g))
        (cong SU2.realPart (Path.identityLeft group x))))

module _
  (M L n : Nat) (sameSide : suc n ≡ M * L)
  (links : Path.PeriodicBondField n SU2.RationalUnitQuaternion)
  (gauge : Path.PeriodicSiteGauge n SU2.RationalUnitQuaternion)
  where

  private
    exactSU2 = SU2Law.rationalSU2ExactLinkGroup
    selected = rationalSU2NativeRealization n links gauge

  -- Constructed real part, no generic SU(N) trace authority assumed here.
  rationalSU2BlockedRealTraceObservable :
    NativeBlockedClassObservable M L n sameSide exactSU2 selected ℚ
  rationalSU2BlockedRealTraceObservable = record
    { evaluate = SU2.realPart
    ; conjugationInvariant = rationalSU2RealTraceConjugationInvariant
    }

  -- This is literal original rational SU(2) WILSON-LOOP gauge invariance
  -- for any properly endpoint-indexed closed blocked path.
  rationalSU2BlockedClosedWilsonRealTraceInvariant :
    ∀ {site}
      (loop : NativeBlockedWalk M L n sameSide exactSU2
                selected site site) →
    SU2.realPart
      (nativeTransformedWalkHolonomy M L n sameSide
        exactSU2 selected loop)
    ≡
    SU2.realPart
      (nativeWalkHolonomy M L n sameSide exactSU2 selected loop)
  rationalSU2BlockedClosedWilsonRealTraceInvariant loop =
    nativeClosedWilsonObservableGaugeInvariant M L n sameSide
      exactSU2 selected rationalSU2BlockedRealTraceObservable loop

-- Source status: SOURCE-WRITTEN, exact-head Agda NOT RUN. This theorem
-- does not claim the walked endpoint equals a physically selected
-- coarse nearest-neighbour step, that Haar disintegrates along this
-- blocking, or that any lattice gap survives the a->0 limit.
