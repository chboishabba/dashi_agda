module DASHI.Physics.YangMills.BalabanClayGate4CMP109PhysicalScaleGeometryExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (length)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Carrier
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredOddBlockCarrierExact as Centered
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredExecutableGeometryExact as Executable
open import DASHI.Physics.YangMills.BalabanFourDimensionalHaloOverlapExact using
  (lengthMap)

------------------------------------------------------------------------
-- Literal scale-k site/block identification for CMP109 equations (0.3)--(0.12).
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- The finite centred carrier is already executable.  This module states the
-- remaining repository-specific identification without collapsing it into a
-- cardinality assertion: for each coarse site y, the map
--
--   iota_y : {-r,...,r}^4 -> fine sites
--
-- is a bijection onto the literal projection fibre pi^{-1}(y).  The block list
-- is then definitionally the image of the complete centred enumeration, and its
-- length is proved to be L^4 with L = 2r+1.
------------------------------------------------------------------------

record CenteredPreimage
    {radius : Nat} {FineSite : Set}
    (embed : Centered.CenteredBlockPoint4 radius → FineSite)
    (site : FineSite) : Set where
  constructor centredPreimage
  field
    point : Centered.CenteredBlockPoint4 radius
    pointMeaning : embed point ≡ site

open CenteredPreimage public

record CMP109PhysicalScaleGeometry
    (radius : Nat) (FineSite CoarseSite Spacing : Set) : Set where
  field
    executableGeometry : Executable.CenteredExecutableGeometry radius

    projectSite : FineSite → CoarseSite
    embedAt : CoarseSite →
      Centered.CenteredBlockPoint4 radius → FineSite

    embedProjectsToCentre : ∀ coarse point →
      projectSite (embedAt coarse point) ≡ coarse

    projectionFibreComplete : ∀ coarse site →
      projectSite site ≡ coarse →
      CenteredPreimage (embedAt coarse) site

    embedAtInjective : ∀ coarse {left right} →
      embedAt coarse left ≡ embedAt coarse right → left ≡ right

    fineSpacing coarseSpacing : Spacing
    scaleSpacing : Nat → Spacing → Spacing
    coarseSpacingMeaning :
      coarseSpacing
      ≡ scaleSpacing (Centered.oddSide radius) fineSpacing

open CMP109PhysicalScaleGeometry public

physicalBlockElements :
  ∀ {radius FineSite CoarseSite Spacing} →
  CMP109PhysicalScaleGeometry radius FineSite CoarseSite Spacing →
  CoarseSite → List FineSite
physicalBlockElements {radius} geometry coarse =
  Carrier.map (embedAt geometry coarse)
    (Carrier.elements (Centered.centeredBlockFinite radius))

physicalBlockMembership :
  ∀ {radius FineSite CoarseSite Spacing} →
  CMP109PhysicalScaleGeometry radius FineSite CoarseSite Spacing →
  CoarseSite → FineSite → Set
physicalBlockMembership geometry coarse site =
  projectSite geometry site ≡ coarse

embeddedPointInPhysicalBlock :
  ∀ {radius FineSite CoarseSite Spacing}
    (geometry : CMP109PhysicalScaleGeometry
      radius FineSite CoarseSite Spacing)
    coarse point →
  physicalBlockMembership geometry coarse (embedAt geometry coarse point)
embeddedPointInPhysicalBlock geometry coarse point =
  embedProjectsToCentre geometry coarse point

physicalBlockMembershipHasCenteredCoordinate :
  ∀ {radius FineSite CoarseSite Spacing}
    (geometry : CMP109PhysicalScaleGeometry
      radius FineSite CoarseSite Spacing)
    coarse site →
  physicalBlockMembership geometry coarse site →
  CenteredPreimage (embedAt geometry coarse) site
physicalBlockMembershipHasCenteredCoordinate geometry coarse site =
  projectionFibreComplete geometry coarse site

centeredCoordinateUnique :
  ∀ {radius FineSite CoarseSite Spacing}
    (geometry : CMP109PhysicalScaleGeometry
      radius FineSite CoarseSite Spacing)
    coarse site
    (left right : CenteredPreimage (embedAt geometry coarse) site) →
  point left ≡ point right
centeredCoordinateUnique geometry coarse site left right =
  embedAtInjective geometry coarse
    (trans (pointMeaning left) (sym (pointMeaning right)))

physicalBlockEnumerationLength :
  ∀ {radius FineSite CoarseSite Spacing}
    (geometry : CMP109PhysicalScaleGeometry
      radius FineSite CoarseSite Spacing)
    coarse →
  length (physicalBlockElements geometry coarse)
  ≡ Centered.fourthPower (Centered.oddSide radius)
physicalBlockEnumerationLength {radius} geometry coarse =
  trans
    (lengthMap (embedAt geometry coarse)
      (Carrier.elements (Centered.centeredBlockFinite radius)))
    (Centered.centeredBlockEnumerationLength radius)

record CMP109EndpointBlockIdentification
    {radius : Nat} {FineSite CoarseSite Spacing FineBond CoarseBond : Set}
    (geometry : CMP109PhysicalScaleGeometry
      radius FineSite CoarseSite Spacing) : Set₁ where
  field
    source target : CoarseBond → CoarseSite
    fineSource fineTarget : FineBond → FineSite

    CrossingFineBond : CoarseBond → FineBond → Set

    crossingSourceProjects : ∀ coarse fine →
      CrossingFineBond coarse fine →
      projectSite geometry (fineSource fine) ≡ source coarse

    crossingTargetProjects : ∀ coarse fine →
      CrossingFineBond coarse fine →
      projectSite geometry (fineTarget fine) ≡ target coarse

open CMP109EndpointBlockIdentification public

crossingSourceHasCenteredCoordinate :
  ∀ {radius FineSite CoarseSite Spacing FineBond CoarseBond}
    {geometry : CMP109PhysicalScaleGeometry
      radius FineSite CoarseSite Spacing}
    (endpoints : CMP109EndpointBlockIdentification
      {FineBond = FineBond} {CoarseBond = CoarseBond} geometry)
    coarse fine →
  CrossingFineBond endpoints coarse fine →
  CenteredPreimage
    (embedAt geometry (source endpoints coarse))
    (fineSource endpoints fine)
crossingSourceHasCenteredCoordinate {geometry = geometry}
    endpoints coarse fine crossing =
  projectionFibreComplete geometry
    (source endpoints coarse)
    (fineSource endpoints fine)
    (crossingSourceProjects endpoints coarse fine crossing)

crossingTargetHasCenteredCoordinate :
  ∀ {radius FineSite CoarseSite Spacing FineBond CoarseBond}
    {geometry : CMP109PhysicalScaleGeometry
      radius FineSite CoarseSite Spacing}
    (endpoints : CMP109EndpointBlockIdentification
      {FineBond = FineBond} {CoarseBond = CoarseBond} geometry)
    coarse fine →
  CrossingFineBond endpoints coarse fine →
  CenteredPreimage
    (embedAt geometry (target endpoints coarse))
    (fineTarget endpoints fine)
crossingTargetHasCenteredCoordinate {geometry = geometry}
    endpoints coarse fine crossing =
  projectionFibreComplete geometry
    (target endpoints coarse)
    (fineTarget endpoints fine)
    (crossingTargetProjects endpoints coarse fine crossing)

cmp109PhysicalProjectionFibreLevel : ProofLevel
cmp109PhysicalProjectionFibreLevel = machineChecked

cmp109PhysicalBlockCardinalityLevel : ProofLevel
cmp109PhysicalBlockCardinalityLevel = machineChecked

cmp109EndpointCenteredCoordinateLevel : ProofLevel
cmp109EndpointCenteredCoordinateLevel = machineChecked

physicalCMP109ProjectionIdentificationInputsLevel : ProofLevel
physicalCMP109ProjectionIdentificationInputsLevel = conditional

physicalCMP109EndpointCrossingInputsLevel : ProofLevel
physicalCMP109EndpointCrossingInputsLevel = conditional
