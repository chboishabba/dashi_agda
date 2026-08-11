module DASHI.Physics.YangMills.BalabanBasedPathGaugeSectionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Spaces of Regular Gauge Field Configurations on a Lattice and Gauge
-- Fixing Conditions", Communications in Mathematical Physics 99 (1985),
-- 75--102. DOI: 10.1007/BF01466594.
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer, 2015.
-- DOI: 10.1007/978-3-319-13467-3.
--
-- DASHI CONTRIBUTION
--
-- Construct an actual finite based/path gauge section, with the gauge-group
-- arrow retained as provenance.  A rooted path system chooses one path from a
-- base site to every site.  For a field U define
--
--       g_U(x) = transport_U(base -> x).
--
-- Gauge covariance then gives unit transport along every selected rooted path
-- after transforming U by g_U.  The gauge is identity at the root.
--
-- A second theorem proves uniqueness inside this rooted-path slice: if two
-- rooted representatives are related by a based gauge arrow, covariance forces
-- that gauge function to be the identity at every site, and hence the fields
-- agree on every bond.
--
-- This is a genuine quotient/section theorem for the finite gauge action.  It
-- deliberately does NOT claim that this particular rooted-path section
-- preserves Bałaban's nonlinear block-average restriction.  That separate
-- physical compatibility theorem remains the condition needed before this
-- section can be identified with the selected variational orbit.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat.Base using (NonZero)
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.P06FaceCubeTorusGeometry using (Cube4)
open import DASHI.Physics.YangMills.BalabanPeriodicLatticeBonds using
  (DirectedBond4; source; target)
open import DASHI.Physics.YangMills.BalabanPeriodicLatticePaths using
  (LatticePath4; empty; _▷_)
import DASHI.Physics.YangMills.BalabanPeriodicGaugeTransport as Transport
import DASHI.Physics.YangMills.BalabanGaugeTransformationCovariance as Covariance
import DASHI.Physics.YangMills.BalabanBasedGaugeActionFreeExact as Free

record RootedPathSystem
    {N : Nat} {{_ : NonZero N}}
    (base : Cube4 N) : Set₁ where
  field
    pathTo : ∀ site → LatticePath4 {N} base site
    pathAtBase : pathTo base ≡ empty

open RootedPathSystem public

RadialGaugeField :
  ∀ {N : Nat} {{_ : NonZero N}}
    (group : Transport.GroupStructure)
    {base : Cube4 N} →
  RootedPathSystem base →
  Covariance.DirectedGaugeField4 N group → Set
RadialGaugeField group paths field =
  ∀ site →
  Covariance.directedPathTransport group field (pathTo paths site)
  ≡ Transport.unit group

rootedGaugeFunction :
  ∀ {N : Nat} {{_ : NonZero N}}
    (group : Transport.GroupStructure)
    {base : Cube4 N}
    (paths : RootedPathSystem base) →
  Covariance.DirectedGaugeField4 N group →
  Covariance.GaugeFunction4 N group
rootedGaugeFunction group paths field site =
  Covariance.directedPathTransport group field (pathTo paths site)

rootedGaugeFunctionBased :
  ∀ {N : Nat} {{_ : NonZero N}}
    (group : Transport.GroupStructure)
    {base : Cube4 N}
    (paths : RootedPathSystem base)
    (field : Covariance.DirectedGaugeField4 N group) →
  Free.BasedGaugeFunction group base (rootedGaugeFunction group paths field)
rootedGaugeFunctionBased group paths field =
  subst
    (λ path →
      Covariance.directedPathTransport group field path
      ≡ Transport.unit group)
    (sym (pathAtBase paths))
    refl

rootedGaugeRepresentative :
  ∀ {N : Nat} {{_ : NonZero N}}
    (group : Transport.GroupStructure)
    {base : Cube4 N}
    (paths : RootedPathSystem base) →
  Covariance.DirectedGaugeField4 N group →
  Covariance.DirectedGaugeField4 N group
rootedGaugeRepresentative group paths field =
  Covariance.gaugeTransformBond group
    (rootedGaugeFunction group paths field) field

rootedGaugeRepresentativeRadial :
  ∀ {N : Nat} {{_ : NonZero N}}
    (group : Transport.GroupStructure)
    {base : Cube4 N}
    (paths : RootedPathSystem base)
    (field : Covariance.DirectedGaugeField4 N group) →
  RadialGaugeField group paths
    (rootedGaugeRepresentative group paths field)
rootedGaugeRepresentativeRadial group {base = base} paths field site =
  let
    gauge = rootedGaugeFunction group paths field
    transport = Covariance.directedPathTransport group field (pathTo paths site)

    covariance = Covariance.pathTransportGaugeCovariant
      group gauge field (pathTo paths site)

    baseIsUnit : gauge base ≡ Transport.unit group
    baseIsUnit = rootedGaugeFunctionBased group paths field

    simplify :
      Transport.multiply group
        (gauge base)
        (Transport.multiply group transport
          (Transport.inverse group (gauge site)))
      ≡ Transport.unit group
    simplify =
      trans
        (cong
          (λ rootValue →
            Transport.multiply group rootValue
              (Transport.multiply group transport
                (Transport.inverse group (gauge site))))
          baseIsUnit)
        (trans
          (Transport.unitLeft group
            (Transport.multiply group transport
              (Transport.inverse group (gauge site))))
          (Transport.inverseRight group transport))
  in
  trans covariance simplify

record BasedGaugeOrbitLift
    {N : Nat} {{_ : NonZero N}}
    (group : Transport.GroupStructure)
    {base : Cube4 N}
    (paths : RootedPathSystem base)
    (sourceField : Covariance.DirectedGaugeField4 N group) : Set₁ where
  field
    representative : Covariance.DirectedGaugeField4 N group
    gaugeArrow : Free.GaugeActionArrow group sourceField representative
    arrowIsBased : Free.BasedGaugeFunction group base (Free.gauge gaugeArrow)
    representativeInRootedSlice : RadialGaugeField group paths representative

open BasedGaugeOrbitLift public

rootedGaugeOrbitLift :
  ∀ {N : Nat} {{_ : NonZero N}}
    (group : Transport.GroupStructure)
    {base : Cube4 N}
    (paths : RootedPathSystem base)
    (field : Covariance.DirectedGaugeField4 N group) →
  BasedGaugeOrbitLift group paths field
rootedGaugeOrbitLift group paths field = record
  { representative = rootedGaugeRepresentative group paths field
  ; gaugeArrow = record
      { Free.GaugeActionArrow.gauge = rootedGaugeFunction group paths field
      ; Free.GaugeActionArrow.actionExact = λ bond → refl
      }
  ; arrowIsBased = rootedGaugeFunctionBased group paths field
  ; representativeInRootedSlice =
      rootedGaugeRepresentativeRadial group paths field
  }

pathTransportRespectsField :
  ∀ {N : Nat} {{_ : NonZero N}}
    (group : Transport.GroupStructure)
    (left right : Covariance.DirectedGaugeField4 N group) →
  (∀ bond → left bond ≡ right bond) →
  ∀ {x y} (path : LatticePath4 {N} x y) →
  Covariance.directedPathTransport group left path
  ≡ Covariance.directedPathTransport group right path
pathTransportRespectsField group left right pointwise empty = refl
pathTransportRespectsField group left right pointwise (bond ▷ path) =
  cong₂ (Transport.multiply group)
    (pointwise bond)
    (pathTransportRespectsField group left right pointwise path)

basedArrowBetweenRadialFieldsIsIdentity :
  ∀ {N : Nat} {{_ : NonZero N}}
    (group : Transport.GroupStructure)
    {base : Cube4 N}
    (paths : RootedPathSystem base)
    (left right : Covariance.DirectedGaugeField4 N group) →
  RadialGaugeField group paths left →
  RadialGaugeField group paths right →
  (arrow : Free.GaugeActionArrow group left right) →
  Free.BasedGaugeFunction group base (Free.gauge arrow) →
  ∀ site → Free.gauge arrow site ≡ Transport.unit group
basedArrowBetweenRadialFieldsIsIdentity
    group {base = base} paths left right
    leftRadial rightRadial arrow based site =
  let
    gauge = Free.gauge arrow
    path = pathTo paths site
    leftTransport = Covariance.directedPathTransport group left path
    rightTransport = Covariance.directedPathTransport group right path

    transformedMatchesRight :
      Covariance.directedPathTransport group
        (Covariance.gaugeTransformBond group gauge left) path
      ≡ rightTransport
    transformedMatchesRight =
      pathTransportRespectsField group
        (Covariance.gaugeTransformBond group gauge left)
        right (Free.actionExact arrow) path

    covariance =
      Covariance.pathTransportGaugeCovariant group gauge left path

    rightToCovariant :
      rightTransport
      ≡ Transport.multiply group
          (gauge base)
          (Transport.multiply group leftTransport
            (Transport.inverse group (gauge site)))
    rightToCovariant = trans (sym transformedMatchesRight) covariance

    rhsToInverse :
      Transport.multiply group
        (gauge base)
        (Transport.multiply group leftTransport
          (Transport.inverse group (gauge site)))
      ≡ Transport.inverse group (gauge site)
    rhsToInverse =
      trans
        (cong
          (λ baseValue →
            Transport.multiply group baseValue
              (Transport.multiply group leftTransport
                (Transport.inverse group (gauge site))))
          based)
        (trans
          (Transport.unitLeft group
            (Transport.multiply group leftTransport
              (Transport.inverse group (gauge site))))
          (trans
            (cong
              (λ leftValue →
                Transport.multiply group leftValue
                  (Transport.inverse group (gauge site)))
              (leftRadial site))
            (Transport.unitLeft group
              (Transport.inverse group (gauge site)))))

    unitToInverse :
      Transport.unit group ≡ Transport.inverse group (gauge site)
    unitToInverse =
      trans
        (sym (rightRadial site))
        (trans rightToCovariant rhsToInverse)
  in
  Free.inverseFactorUnitImpliesUnit group (gauge site) (sym unitToInverse)

identityGaugeTransformExact :
  ∀ {N : Nat} {{_ : NonZero N}}
    (group : Transport.GroupStructure)
    (gauge : Covariance.GaugeFunction4 N group)
    (field : Covariance.DirectedGaugeField4 N group) →
  (∀ site → gauge site ≡ Transport.unit group) →
  ∀ bond →
  Covariance.gaugeTransformBond group gauge field bond ≡ field bond
identityGaugeTransformExact group gauge field gaugeUnit bond =
  trans
    (cong₂ (Transport.multiply group)
      (gaugeUnit (source bond))
      (cong₂ (Transport.multiply group)
        refl
        (cong (Transport.inverse group) (gaugeUnit (target bond)))))
    (trans
      (cong
        (Transport.multiply group (Transport.unit group))
        (cong
          (Transport.multiply group (field bond))
          (Free.inverseUnitExact group)))
      (trans
        (Transport.unitLeft group
          (Transport.multiply group (field bond) (Transport.unit group)))
        (Transport.unitRight group (field bond))))

rootedGaugeRepresentativeUniqueInBasedOrbit :
  ∀ {N : Nat} {{_ : NonZero N}}
    (group : Transport.GroupStructure)
    {base : Cube4 N}
    (paths : RootedPathSystem base)
    (left right : Covariance.DirectedGaugeField4 N group) →
  RadialGaugeField group paths left →
  RadialGaugeField group paths right →
  (arrow : Free.GaugeActionArrow group left right) →
  Free.BasedGaugeFunction group base (Free.gauge arrow) →
  ∀ bond → left bond ≡ right bond
rootedGaugeRepresentativeUniqueInBasedOrbit
    group paths left right leftRadial rightRadial arrow based bond =
  let
    gaugeUnit = basedArrowBetweenRadialFieldsIsIdentity
      group paths left right leftRadial rightRadial arrow based
  in
  trans
    (sym (identityGaugeTransformExact
      group (Free.gauge arrow) left gaugeUnit bond))
    (Free.actionExact arrow bond)

basedPathGaugeSectionExistenceLevel : ProofLevel
basedPathGaugeSectionExistenceLevel = machineChecked

basedPathGaugeSectionUniquenessLevel : ProofLevel
basedPathGaugeSectionUniquenessLevel = machineChecked

selectedBlockAverageCompatibilityStillRequiredLevel : ProofLevel
selectedBlockAverageCompatibilityStillRequiredLevel = conditional
