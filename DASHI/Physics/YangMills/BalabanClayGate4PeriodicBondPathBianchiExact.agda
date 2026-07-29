module DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; suc)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
  using (Axis4; BondField; pair; first; second)
open import DASHI.Physics.YangMills.BalabanRootedPolymerWordEntropyExact
  using (SignedAxis4)

import DASHI.Physics.YangMills.BalabanClayT2PeriodicBlockPolymerCarrierExact as Periodic
import DASHI.Physics.YangMills.BalabanClayT2PeriodicAdjacencyBFSExact as Adjacency
import DASHI.Physics.YangMills.BalabanClayGate4LiteralPeriodicPlaquetteWitnessExact as Plaquette

------------------------------------------------------------------------
-- Primary provenance.
--
-- Tadeusz Bałaban,
-- "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
--
-- Tadeusz Bałaban,
-- "Spaces of Regular Gauge Field Configurations on a Lattice and Gauge Fixing
-- Conditions", Communications in Mathematical Physics 99 (1985), 75--102.
-- DOI: 10.1007/BF01466594.
--
-- Michael Creutz,
-- "Quarks, Gluons and Lattices", Cambridge University Press, first published
-- 1983; open-access reissue 2022. DOI: 10.1017/9781009290395.
------------------------------------------------------------------------

PeriodicBondField : Nat → Set → Set
PeriodicBondField n Value = BondField (suc n) Value

PeriodicSiteGauge : Nat → Set → Set
PeriodicSiteGauge n Value = Periodic.PeriodicBlock n → Value

positiveStep : ∀ {n} → Periodic.PeriodicBlock n → Axis4 → Periodic.PeriodicBlock n
positiveStep site axis = Adjacency.signedStep site (pair axis true)

negativeStep : ∀ {n} → Periodic.PeriodicBlock n → Axis4 → Periodic.PeriodicBlock n
negativeStep site axis = Adjacency.signedStep site (pair axis false)

walkStep : ∀ {n} → Periodic.PeriodicBlock n → SignedAxis4 → Periodic.PeriodicBlock n
walkStep = Adjacency.signedStep

walk : ∀ {n} → Periodic.PeriodicBlock n → List SignedAxis4 → Periodic.PeriodicBlock n
walk site [] = site
walk site (direction ∷ directions) = walk (walkStep site direction) directions

record ExactLinkGroup (Value : Set) : Set₁ where
  field
    identity : Value
    multiply : Value → Value → Value
    inverse : Value → Value

    multiplyAssociative : ∀ left middle right →
      multiply (multiply left middle) right
      ≡ multiply left (multiply middle right)
    identityLeft : ∀ value → multiply identity value ≡ value
    identityRight : ∀ value → multiply value identity ≡ value
    inverseLeft : ∀ value → multiply (inverse value) value ≡ identity
    inverseRight : ∀ value → multiply value (inverse value) ≡ identity
    inverseProduct : ∀ left right →
      inverse (multiply left right) ≡ multiply (inverse right) (inverse left)
    inverseInverse : ∀ value → inverse (inverse value) ≡ value

open ExactLinkGroup public

conjugateIdentity :
  ∀ {Value} (group : ExactLinkGroup Value) gauge →
  identity group
  ≡ multiply group
      (multiply group gauge (identity group))
      (inverse group gauge)
conjugateIdentity group gauge =
  sym (trans
    (cong (λ left → multiply group left (inverse group gauge))
      (identityRight group gauge))
    (inverseRight group gauge))

cancelMiddleGauge :
  ∀ {Value} (group : ExactLinkGroup Value)
    middle secondSegment finish →
  multiply group (inverse group middle)
    (multiply group
      (multiply group middle secondSegment)
      (inverse group finish))
  ≡ multiply group secondSegment (inverse group finish)
cancelMiddleGauge group middle secondSegment finish =
  trans
    (sym (multiplyAssociative group
      (inverse group middle)
      (multiply group middle secondSegment)
      (inverse group finish)))
    (cong (λ left → multiply group left (inverse group finish))
      (trans
        (sym (multiplyAssociative group
          (inverse group middle) middle secondSegment))
        (trans
          (cong (λ left → multiply group left secondSegment)
            (inverseLeft group middle))
          (identityLeft group secondSegment))))

composeGaugeSegments :
  ∀ {Value} (group : ExactLinkGroup Value)
    start middle finish firstSegment secondSegment →
  multiply group
    (multiply group (multiply group start firstSegment) (inverse group middle))
    (multiply group (multiply group middle secondSegment) (inverse group finish))
  ≡ multiply group
      (multiply group start (multiply group firstSegment secondSegment))
      (inverse group finish)
composeGaugeSegments group start middle finish firstSegment secondSegment =
  trans
    (multiplyAssociative group
      (multiply group start firstSegment)
      (inverse group middle)
      (multiply group (multiply group middle secondSegment)
        (inverse group finish)))
    (trans
      (cong (multiply group (multiply group start firstSegment))
        (cancelMiddleGauge group middle secondSegment finish))
      (trans
        (sym (multiplyAssociative group
          (multiply group start firstSegment)
          secondSegment
          (inverse group finish)))
        (cong (λ left → multiply group left (inverse group finish))
          (multiplyAssociative group start firstSegment secondSegment))))

record PeriodicBondGaugeRealization
    (n : Nat) (Value : Set) (group : ExactLinkGroup Value) : Set₁ where
  field
    bondField : PeriodicBondField n Value
    gauge : PeriodicSiteGauge n Value

  transformedBond : PeriodicBondField n Value
  transformedBond (pair site axis) =
    multiply group
      (multiply group (gauge site) (bondField (pair site axis)))
      (inverse group (gauge (positiveStep site axis)))

  orientedLink : Periodic.PeriodicBlock n → SignedAxis4 → Value
  orientedLink site (pair axis true) = bondField (pair site axis)
  orientedLink site (pair axis false) =
    inverse group (bondField (pair (negativeStep site axis) axis))

  transformedOrientedLink : Periodic.PeriodicBlock n → SignedAxis4 → Value
  transformedOrientedLink site (pair axis true) = transformedBond (pair site axis)
  transformedOrientedLink site (pair axis false) =
    inverse group (transformedBond (pair (negativeStep site axis) axis))

  field
    orientedLinkGaugeCovariant : ∀ site direction →
      transformedOrientedLink site direction
      ≡ multiply group
          (multiply group (gauge site) (orientedLink site direction))
          (inverse group (gauge (walkStep site direction)))

open PeriodicBondGaugeRealization public

pathHolonomy :
  ∀ {n Value} {group : ExactLinkGroup Value} →
  PeriodicBondGaugeRealization n Value group →
  Periodic.PeriodicBlock n → List SignedAxis4 → Value
pathHolonomy {group = group} realization site [] = identity group
pathHolonomy {group = group} realization site (direction ∷ directions) =
  multiply group
    (orientedLink realization site direction)
    (pathHolonomy realization (walkStep site direction) directions)

transformedPathHolonomy :
  ∀ {n Value} {group : ExactLinkGroup Value} →
  PeriodicBondGaugeRealization n Value group →
  Periodic.PeriodicBlock n → List SignedAxis4 → Value
transformedPathHolonomy {group = group} realization site [] = identity group
transformedPathHolonomy {group = group} realization site (direction ∷ directions) =
  multiply group
    (transformedOrientedLink realization site direction)
    (transformedPathHolonomy realization (walkStep site direction) directions)

pathSiteGaugeCancellation :
  ∀ {n Value} {group : ExactLinkGroup Value}
    (realization : PeriodicBondGaugeRealization n Value group)
    site directions →
  transformedPathHolonomy realization site directions
  ≡ multiply group
      (multiply group
        (gauge realization site)
        (pathHolonomy realization site directions))
      (inverse group (gauge realization (walk site directions)))
pathSiteGaugeCancellation {group = group} realization site [] =
  conjugateIdentity group (gauge realization site)
pathSiteGaugeCancellation {group = group} realization site
  (direction ∷ directions) =
  trans
    (cong
      (λ firstValue → multiply group firstValue
        (transformedPathHolonomy realization
          (walkStep site direction) directions))
      (orientedLinkGaugeCovariant realization site direction))
    (trans
      (cong
        (multiply group
          (multiply group
            (gauge realization site)
            (orientedLink realization site direction))
          (inverse group (gauge realization (walkStep site direction))))
        (pathSiteGaugeCancellation realization
          (walkStep site direction) directions))
      (composeGaugeSegments group
        (gauge realization site)
        (gauge realization (walkStep site direction))
        (gauge realization (walk site (direction ∷ directions)))
        (orientedLink realization site direction)
        (pathHolonomy realization (walkStep site direction) directions)))

positiveDirection negativeDirection : Axis4 → SignedAxis4
positiveDirection axis = pair axis true
negativeDirection axis = pair axis false

plaquetteBoundaryDirections : Plaquette.PositivePlane4 → List SignedAxis4
plaquetteBoundaryDirections plane =
  positiveDirection (first (Plaquette.planeAxes plane)) ∷
  positiveDirection (second (Plaquette.planeAxes plane)) ∷
  negativeDirection (first (Plaquette.planeAxes plane)) ∷
  negativeDirection (second (Plaquette.planeAxes plane)) ∷ []

record PeriodicPlaquetteClosure (n : Nat) : Set₁ where
  field
    plaquetteCloses : ∀ site plane →
      walk site (plaquetteBoundaryDirections plane) ≡ site

open PeriodicPlaquetteClosure public

plaquetteHolonomyFromBonds :
  ∀ {n Value} {group : ExactLinkGroup Value} →
  PeriodicBondGaugeRealization n Value group →
  Plaquette.PeriodicPlaquette n → Value
plaquetteHolonomyFromBonds realization plaquette =
  pathHolonomy realization (first plaquette)
    (plaquetteBoundaryDirections (second plaquette))

plaquetteGaugeCancellation :
  ∀ {n Value} {group : ExactLinkGroup Value}
    (closure : PeriodicPlaquetteClosure n)
    (realization : PeriodicBondGaugeRealization n Value group)
    (plaquette : Plaquette.PeriodicPlaquette n) →
  transformedPathHolonomy realization (first plaquette)
    (plaquetteBoundaryDirections (second plaquette))
  ≡ multiply group
      (multiply group
        (gauge realization (first plaquette))
        (plaquetteHolonomyFromBonds realization plaquette))
      (inverse group (gauge realization (first plaquette)))
plaquetteGaugeCancellation {group = group} closure realization plaquette =
  subst
    (λ endpoint →
      transformedPathHolonomy realization (first plaquette)
        (plaquetteBoundaryDirections (second plaquette))
      ≡ multiply group
          (multiply group
            (gauge realization (first plaquette))
            (plaquetteHolonomyFromBonds realization plaquette))
          (inverse group (gauge realization endpoint)))
    (plaquetteCloses closure (first plaquette) (second plaquette))
    (pathSiteGaugeCancellation realization (first plaquette)
      (plaquetteBoundaryDirections (second plaquette)))

record TransportedCubeBoundaryCertificate
    (n : Nat) (Value : Set) (group : ExactLinkGroup Value)
    (realization : PeriodicBondGaugeRealization n Value group) : Set₁ where
  field
    cubeBase : Periodic.PeriodicBlock n
    transportedSixFaceBoundary : List SignedAxis4
    boundaryWalkCloses : walk cubeBase transportedSixFaceBoundary ≡ cubeBase
    boundaryHolonomyIsIdentity :
      pathHolonomy realization cubeBase transportedSixFaceBoundary
      ≡ identity group

open TransportedCubeBoundaryCertificate public

latticeBianchiFromTransportedBoundary :
  ∀ {n Value} {group : ExactLinkGroup Value}
    {realization : PeriodicBondGaugeRealization n Value group} →
  (certificate : TransportedCubeBoundaryCertificate n Value group realization) →
  pathHolonomy realization
    (cubeBase certificate)
    (transportedSixFaceBoundary certificate)
  ≡ identity group
latticeBianchiFromTransportedBoundary = boundaryHolonomyIsIdentity

fundamentalGroupCancellationAlgebraLevel : ProofLevel
fundamentalGroupCancellationAlgebraLevel = machineChecked

periodicBondFieldDefinitionLevel : ProofLevel
periodicBondFieldDefinitionLevel = machineChecked

pathSiteGaugeCancellationLevel : ProofLevel
pathSiteGaugeCancellationLevel = machineChecked

plaquetteBondHolonomyBridgeLevel : ProofLevel
plaquetteBondHolonomyBridgeLevel = machineChecked

transportedCubeBianchiBridgeLevel : ProofLevel
transportedCubeBianchiBridgeLevel = machineChecked

rationalQuaternionExactGroupInputsLevel : ProofLevel
rationalQuaternionExactGroupInputsLevel = conditional

periodicOrientedLinkCovarianceInputsLevel : ProofLevel
periodicOrientedLinkCovarianceInputsLevel = conditional

periodicPlaquetteClosureInputsLevel : ProofLevel
periodicPlaquetteClosureInputsLevel = conditional

literalTransportedCubeBoundaryCertificateLevel : ProofLevel
literalTransportedCubeBoundaryCertificateLevel = conditional
