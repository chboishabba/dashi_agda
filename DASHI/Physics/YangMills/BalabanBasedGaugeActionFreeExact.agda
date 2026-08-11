module DASHI.Physics.YangMills.BalabanBasedGaugeActionFreeExact where

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
-- Introduction", second edition, Springer (2015).
-- DOI: 10.1007/978-3-319-13467-3.
--
-- DASHI CONTRIBUTION
--
-- The unbased gauge quotient can have background-dependent isotropy, as the
-- selected holonomy witness already proves.  This module establishes the
-- complementary computational fact without deleting or identifying those
-- physical stabilizers: on a connected lattice, a gauge transformation which
-- fixes every link and is the identity at one base site is the identity at
-- every site.
--
-- The proof is group-theoretic and pathwise.  Gauge covariance says that
-- transport from base to x transforms as
--
--   T(p) -> g(base) T(p) g(x)^-1.
--
-- If every link is stabilized, the transformed path transport is T(p); if the
-- gauge is based, g(base)=1.  Left cancellation then forces g(x)^-1=1 and
-- hence g(x)=1.  Thus the based action is free whenever a path from the base
-- to every site is supplied.
--
-- This is the precise sense in which a based presentation can remove global
-- isotropy from the computational carrier while the unbased physical quotient
-- remains orbit-type stratified.  It does NOT construct a nonlinear gauge
-- slice or prove that a selected variational orbit meets such a slice.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat.Base using (NonZero)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.P06FaceCubeTorusGeometry using (Cube4)
open import DASHI.Physics.YangMills.BalabanPeriodicLatticeBonds using (DirectedBond4)
open import DASHI.Physics.YangMills.BalabanPeriodicLatticePaths using
  (LatticePath4; empty; _▷_)
import DASHI.Physics.YangMills.BalabanPeriodicGaugeTransport as Transport
import DASHI.Physics.YangMills.BalabanGaugeTransformationCovariance as Covariance

GaugeStabilizes :
  ∀ {N : Nat} {{_ : NonZero N}}
    (group : Transport.GroupStructure) →
    Covariance.GaugeFunction4 N group →
    Covariance.DirectedGaugeField4 N group → Set
GaugeStabilizes group gauge U =
  ∀ bond → Covariance.gaugeTransformBond group gauge U bond ≡ U bond

BasedGaugeFunction :
  ∀ {N : Nat}
    (group : Transport.GroupStructure) →
    Cube4 N → Covariance.GaugeFunction4 N group → Set
BasedGaugeFunction group base gauge =
  gauge base ≡ Transport.unit group

ConnectedFromBase :
  ∀ {N : Nat} {{_ : NonZero N}} → Cube4 N → Set
ConnectedFromBase {N} base =
  ∀ site → LatticePath4 {N} base site

stabilizedPathTransport :
  ∀ {N : Nat} {{_ : NonZero N}}
    (group : Transport.GroupStructure)
    (gauge : Covariance.GaugeFunction4 N group)
    (U : Covariance.DirectedGaugeField4 N group) →
  GaugeStabilizes group gauge U →
  ∀ {x y} (path : LatticePath4 {N} x y) →
  Covariance.directedPathTransport group
      (Covariance.gaugeTransformBond group gauge U) path
  ≡ Covariance.directedPathTransport group U path
stabilizedPathTransport group gauge U stabilizes empty = refl
stabilizedPathTransport group gauge U stabilizes (bond ▷ path) =
  cong₂ (Transport.multiply group)
    (stabilizes bond)
    (stabilizedPathTransport group gauge U stabilizes path)

inverseUnitExact :
  (group : Transport.GroupStructure) →
  Transport.inverse group (Transport.unit group) ≡ Transport.unit group
inverseUnitExact group =
  trans
    (sym
      (Transport.unitRight group
        (Transport.inverse group (Transport.unit group))))
    (Transport.inverseLeft group (Transport.unit group))

rightFactorForcedUnit :
  (group : Transport.GroupStructure) →
  ∀ left factor →
  left ≡ Transport.multiply group left factor →
  factor ≡ Transport.unit group
rightFactorForcedUnit group left factor equation =
  trans
    (sym (Transport.unitLeft group factor))
    (trans
      (cong
        (λ value → Transport.multiply group value factor)
        (sym (Transport.inverseLeft group left)))
      (trans
        (Transport.multiplyAssoc group
          (Transport.inverse group left) left factor)
        (trans
          (cong
            (Transport.multiply group (Transport.inverse group left))
            (sym equation))
          (Transport.inverseLeft group left))))

inverseFactorUnitImpliesUnit :
  (group : Transport.GroupStructure) →
  ∀ value →
  Transport.inverse group value ≡ Transport.unit group →
  value ≡ Transport.unit group
inverseFactorUnitImpliesUnit group value inverseIsUnit =
  trans
    (sym (Transport.inverseInvolutive group value))
    (trans
      (cong (Transport.inverse group) inverseIsUnit)
      (inverseUnitExact group))

basedStabilizerTrivialAlongPath :
  ∀ {N : Nat} {{_ : NonZero N}}
    (group : Transport.GroupStructure)
    (base : Cube4 N)
    (gauge : Covariance.GaugeFunction4 N group)
    (U : Covariance.DirectedGaugeField4 N group) →
  BasedGaugeFunction group base gauge →
  GaugeStabilizes group gauge U →
  ∀ {site} → LatticePath4 {N} base site →
  gauge site ≡ Transport.unit group
basedStabilizerTrivialAlongPath
    group base gauge U based stabilizes {site} path =
  let
    transport = Covariance.directedPathTransport group U path

    stabilized = stabilizedPathTransport group gauge U stabilizes path
    covariant = Covariance.pathTransportGaugeCovariant group gauge U path

    removeBase :
      Transport.multiply group
        (gauge base)
        (Transport.multiply group transport
          (Transport.inverse group (gauge site)))
      ≡ Transport.multiply group transport
          (Transport.inverse group (gauge site))
    removeBase =
      trans
        (cong
          (λ baseValue →
            Transport.multiply group baseValue
              (Transport.multiply group transport
                (Transport.inverse group (gauge site))))
          based)
        (Transport.unitLeft group
          (Transport.multiply group transport
            (Transport.inverse group (gauge site))))

    transportFixed :
      transport
      ≡ Transport.multiply group transport
          (Transport.inverse group (gauge site))
    transportFixed =
      trans (sym stabilized)
        (trans covariant removeBase)

    inverseIsUnit :
      Transport.inverse group (gauge site) ≡ Transport.unit group
    inverseIsUnit =
      rightFactorForcedUnit group transport
        (Transport.inverse group (gauge site)) transportFixed
  in
  inverseFactorUnitImpliesUnit group (gauge site) inverseIsUnit

selectedBasedGaugeStabilizerTrivial :
  ∀ {N : Nat} {{_ : NonZero N}}
    (group : Transport.GroupStructure)
    (base : Cube4 N)
    (gauge : Covariance.GaugeFunction4 N group)
    (U : Covariance.DirectedGaugeField4 N group) →
  ConnectedFromBase base →
  BasedGaugeFunction group base gauge →
  GaugeStabilizes group gauge U →
  ∀ site → gauge site ≡ Transport.unit group
selectedBasedGaugeStabilizerTrivial
    group base gauge U connected based stabilizes site =
  basedStabilizerTrivialAlongPath
    group base gauge U based stabilizes (connected site)

record GaugeActionArrow
    {N : Nat} {{_ : NonZero N}}
    (group : Transport.GroupStructure)
    (sourceField targetField : Covariance.DirectedGaugeField4 N group) : Set where
  field
    gauge : Covariance.GaugeFunction4 N group
    actionExact : ∀ bond →
      Covariance.gaugeTransformBond group gauge sourceField bond
      ≡ targetField bond

open GaugeActionArrow public

GaugeActionIsotropy :
  ∀ {N : Nat} {{_ : NonZero N}}
    (group : Transport.GroupStructure) →
    Covariance.DirectedGaugeField4 N group → Set
GaugeActionIsotropy group gaugeField = GaugeActionArrow group gaugeField gaugeField

basedGaugeActionIsotropyTrivial :
  ∀ {N : Nat} {{_ : NonZero N}}
    (group : Transport.GroupStructure)
    (base : Cube4 N)
    (gaugeField : Covariance.DirectedGaugeField4 N group) →
  ConnectedFromBase base →
  ∀ (isotropy : GaugeActionIsotropy group gaugeField) →
  BasedGaugeFunction group base (gauge isotropy) →
  ∀ site → gauge isotropy site ≡ Transport.unit group
basedGaugeActionIsotropyTrivial group base gaugeField connected isotropy based =
  selectedBasedGaugeStabilizerTrivial
    group base (gauge isotropy) gaugeField connected based (actionExact isotropy)

selectedBasedGaugePathFreenessLevel : ProofLevel
selectedBasedGaugePathFreenessLevel = machineChecked

selectedBasedGaugeActionFreeLevel : ProofLevel
selectedBasedGaugeActionFreeLevel = machineChecked

unbasedOrbitTypeStratificationStillRequiredLevel : ProofLevel
unbasedOrbitTypeStratificationStillRequiredLevel = conditional
