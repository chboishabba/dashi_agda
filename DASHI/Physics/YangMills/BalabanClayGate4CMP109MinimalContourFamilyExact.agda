module DASHI.Physics.YangMills.BalabanClayGate4CMP109MinimalContourFamilyExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (suc)
open import Relation.Binary.PropositionalEquality using (cong; subst; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bond
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredOddBlockCarrierExact as Centered
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredPeriodicEmbeddingExact as Embedding
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredExecutableGeometryExact as Executable
import DASHI.Physics.YangMills.BalabanClayGate4CMP109ShortestContourEnumerationExact as Contours
import DASHI.Physics.YangMills.BalabanClayGate4CMP109PeriodicContourFamilyInstantiationExact as Periodic
import DASHI.Physics.YangMills.BalabanClayGate4CMP109ContourMultiplicityExact as Multiplicity
import DASHI.Physics.YangMills.BalabanClayGate4CMP109MinimalAdmissibleRepositoryScaleExact as Minimal

------------------------------------------------------------------------
-- Literal equation-(0.11) contour family at the minimal admissible scale.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- For every centred point in the L=13 block, this module uses exactly the
-- repository's executable family of all orderings of its nonzero coordinate
-- segments. Every member reaches the direct embedded point, and the family has
-- cardinality s!, where s is the number of active coordinate directions.
------------------------------------------------------------------------

minimalContourStart :
  Executable.CenteredExecutableGeometry Minimal.radius →
  Minimal.RepositoryFineSite
minimalContourStart geometry =
  Embedding.embeddingCentre (Executable.embedding geometry)

minimalContourFamily :
  (geometry : Executable.CenteredExecutableGeometry Minimal.radius) →
  Centered.CenteredBlockPoint4 Minimal.radius →
  List
    (Periodic.ExecutablePeriodicContour
      (Embedding.centeredTorusParameter Minimal.radius)
      (minimalContourStart geometry))
minimalContourFamily geometry point =
  Periodic.allPeriodicContours
    (minimalContourStart geometry)
    (Embedding.centeredDisplacement4 point)

listLengthAgreement : ∀ {A : Set} (values : List A) →
  Periodic.listLength values ≡ Contours.listLength values
listLengthAgreement [] = refl
listLengthAgreement (_ ∷ values) =
  cong suc (listLengthAgreement values)

minimalContourFamilyCardinality :
  (geometry : Executable.CenteredExecutableGeometry Minimal.radius) →
  (point : Centered.CenteredBlockPoint4 Minimal.radius) →
  Periodic.listLength (minimalContourFamily geometry point)
  ≡ Multiplicity.factorial
      (Multiplicity.activeDirectionCount
        (Embedding.centeredDisplacement4 point))
minimalContourFamilyCardinality geometry point =
  trans
    (Periodic.allPeriodicContourCountEqualsOrderCount
      (minimalContourStart geometry)
      (Embedding.centeredDisplacement4 point))
    (trans
      (listLengthAgreement
        (Contours.cmp109ShortestContourOrders
          (Embedding.centeredDisplacement4 point)))
      (Multiplicity.cmp109ContourFamilyCardinality
        (Embedding.centeredDisplacement4 point)))

minimalContourMembershipOrder :
  (geometry : Executable.CenteredExecutableGeometry Minimal.radius) →
  (point : Centered.CenteredBlockPoint4 Minimal.radius) →
  (contour : Periodic.ExecutablePeriodicContour
    (Embedding.centeredTorusParameter Minimal.radius)
    (minimalContourStart geometry)) →
  Contours._∈_ contour (minimalContourFamily geometry point) →
  Contours.MapPreimage
    (Periodic.makeExecutableContour (minimalContourStart geometry))
    (Contours.cmp109ShortestContourOrders
      (Embedding.centeredDisplacement4 point))
    contour
minimalContourMembershipOrder geometry point contour membership =
  Periodic.allPeriodicContourMembershipPreimage
    (minimalContourStart geometry)
    (Embedding.centeredDisplacement4 point)
    contour membership

minimalContourEndpointExact :
  (geometry : Executable.CenteredExecutableGeometry Minimal.radius) →
  (point : Centered.CenteredBlockPoint4 Minimal.radius) →
  (contour : Periodic.ExecutablePeriodicContour
    (Embedding.centeredTorusParameter Minimal.radius)
    (minimalContourStart geometry)) →
  Contours._∈_ contour (minimalContourFamily geometry point) →
  Periodic.computedEndpoint contour
  ≡ Embedding.embed (Executable.embedding geometry) point
minimalContourEndpointExact geometry point contour membership
  with minimalContourMembershipOrder geometry point contour membership
... | Contours.mapWitness order orderIn imageExact =
  subst
    (λ selectedContour →
      Periodic.computedEndpoint selectedContour
      ≡ Embedding.embed (Executable.embedding geometry) point)
    imageExact
    (Executable.executableCenteredGeometryEndpointExact
      geometry point order orderIn)

minimalContourWalkEndpointExact :
  (geometry : Executable.CenteredExecutableGeometry Minimal.radius) →
  (point : Centered.CenteredBlockPoint4 Minimal.radius) →
  (contour : Periodic.ExecutablePeriodicContour
    (Embedding.centeredTorusParameter Minimal.radius)
    (minimalContourStart geometry)) →
  Contours._∈_ contour (minimalContourFamily geometry point) →
  Bond.walk
    (minimalContourStart geometry)
    (Periodic.directions contour)
  ≡ Embedding.embed (Executable.embedding geometry) point
minimalContourWalkEndpointExact = minimalContourEndpointExact

cmp109MinimalContourFamilyEnumerationLevel : ProofLevel
cmp109MinimalContourFamilyEnumerationLevel = machineChecked

cmp109MinimalContourFamilyCardinalityLevel : ProofLevel
cmp109MinimalContourFamilyCardinalityLevel = machineChecked

cmp109MinimalContourFamilyEndpointLevel : ProofLevel
cmp109MinimalContourFamilyEndpointLevel = machineChecked
