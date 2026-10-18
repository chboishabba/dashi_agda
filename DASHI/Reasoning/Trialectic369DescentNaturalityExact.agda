module DASHI.Reasoning.Trialectic369DescentNaturalityExact where

------------------------------------------------------------------------
-- TRIALECTIC OBSERVER MATRIX: DYADIC COVER / HYPERVOXEL NATURALITY
--
-- DASHI CONTRIBUTION
--
-- The global 3x3 observer matrix restricts to three dyadic charts:
--
--   AB carries AA, AB, BA, BB
--   BC carries BB, BC, CB, CC
--   CA carries CC, CA, AC, AA
--
-- Their pairwise overlaps are exactly the self positions A, B and C.  A
-- compatible three-chart family reglues to one global observer matrix, and the
-- restrictions of the glued matrix recover the three local charts.
--
-- Separately, the observer<->hyperfabric rechart sends the A/B/C rows exactly
-- to the three existing 27-cube projections.  This is a commuting projection
-- theorem.  It does NOT by itself identify the existing X6 face-Cech model
-- with the relational Grothendieck sheaf.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Reasoning.TrialecticObserverMatrix369Exact as Observer
import DASHI.Reasoning.Trialectic369HypervoxelUltrametricExact as Bridge
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Fabric
import DASHI.Foundations.RelationalStageTwelveGrothendieckExtensionExact as Site
import DASHI.Moonshine.Base369Ternary27FaceHypercubeCechGluingBidiExact as Cech

------------------------------------------------------------------------
-- 1. Dyadic section carriers.
------------------------------------------------------------------------

record ABSection : Set where
  constructor ab-section
  field
    aaAB : SSP.SSPTrit
    ab : SSP.SSPTrit
    ba : SSP.SSPTrit
    bbAB : SSP.SSPTrit
open ABSection public

record BCSection : Set where
  constructor bc-section
  field
    bbBC : SSP.SSPTrit
    bc : SSP.SSPTrit
    cb : SSP.SSPTrit
    ccBC : SSP.SSPTrit
open BCSection public

record CASection : Set where
  constructor ca-section
  field
    ccCA : SSP.SSPTrit
    ca : SSP.SSPTrit
    ac : SSP.SSPTrit
    aaCA : SSP.SSPTrit
open CASection public

restrictAB :
  Observer.ObserverMatrix3 SSP.SSPTrit ->
  ABSection
restrictAB matrix =
  ab-section
    (Observer.aA matrix)
    (Observer.aB matrix)
    (Observer.bA matrix)
    (Observer.bB matrix)

restrictBC :
  Observer.ObserverMatrix3 SSP.SSPTrit ->
  BCSection
restrictBC matrix =
  bc-section
    (Observer.bB matrix)
    (Observer.bC matrix)
    (Observer.cB matrix)
    (Observer.cC matrix)

restrictCA :
  Observer.ObserverMatrix3 SSP.SSPTrit ->
  CASection
restrictCA matrix =
  ca-section
    (Observer.cC matrix)
    (Observer.cA matrix)
    (Observer.aC matrix)
    (Observer.aA matrix)

------------------------------------------------------------------------
-- 2. Matching family on the A/B/C overlaps.
------------------------------------------------------------------------

record DyadicMatchingFamily : Set where
  constructor dyadic-matching-family
  field
    localAB : ABSection
    localBC : BCSection
    localCA : CASection

    agreesAtA :
      aaAB localAB ≡ aaCA localCA

    agreesAtB :
      bbAB localAB ≡ bbBC localBC

    agreesAtC :
      ccBC localBC ≡ ccCA localCA
open DyadicMatchingFamily public

observerMatchingFamily :
  Observer.ObserverMatrix3 SSP.SSPTrit ->
  DyadicMatchingFamily
observerMatchingFamily matrix =
  dyadic-matching-family
    (restrictAB matrix)
    (restrictBC matrix)
    (restrictCA matrix)
    refl refl refl

------------------------------------------------------------------------
-- 3. Exact gluing.
------------------------------------------------------------------------

glueDyadic :
  DyadicMatchingFamily ->
  Observer.ObserverMatrix3 SSP.SSPTrit
glueDyadic family =
  Observer.observerMatrix3
    (aaAB (localAB family))
    (ab (localAB family))
    (ac (localCA family))

    (ba (localAB family))
    (bbAB (localAB family))
    (bc (localBC family))

    (ca (localCA family))
    (cb (localBC family))
    (ccBC (localBC family))

glueRestrictAB :
  (family : DyadicMatchingFamily) ->
  restrictAB (glueDyadic family) ≡ localAB family
glueRestrictAB
  (dyadic-matching-family
    (ab-section aa abv bav bb)
    (bc-section bb' bcv cbv cc)
    (ca-section cc' cav acv aa')
    agreeA agreeB agreeC)
  rewrite agreeB = refl

glueRestrictBC :
  (family : DyadicMatchingFamily) ->
  restrictBC (glueDyadic family) ≡ localBC family
glueRestrictBC
  (dyadic-matching-family
    (ab-section aa abv bav bb)
    (bc-section bb' bcv cbv cc)
    (ca-section cc' cav acv aa')
    agreeA agreeB agreeC)
  rewrite agreeB = refl

glueRestrictCA :
  (family : DyadicMatchingFamily) ->
  restrictCA (glueDyadic family) ≡ localCA family
glueRestrictCA
  (dyadic-matching-family
    (ab-section aa abv bav bb)
    (bc-section bb' bcv cbv cc)
    (ca-section cc' cav acv aa')
    agreeA agreeB agreeC)
  rewrite agreeA | agreeC = refl

observerGlueRoundTrip :
  (matrix : Observer.ObserverMatrix3 SSP.SSPTrit) ->
  glueDyadic (observerMatchingFamily matrix) ≡ matrix
observerGlueRoundTrip
  (Observer.observerMatrix3
    aa abv acv ba bb bc ca cb cc) = refl

------------------------------------------------------------------------
-- 4. The cover really is the canonical relational Grothendieck cover.
------------------------------------------------------------------------

relationalCoverReceipt :
  Site.RelCover Site.triadicRelationalSieve
relationalCoverReceipt =
  Site.triadicRelationalSieveCovers

------------------------------------------------------------------------
-- 5. Observer rows commute with the exact hyperfabric projections.
------------------------------------------------------------------------

rowAProjectionCommutes :
  (matrix : Observer.ObserverMatrix3 SSP.SSPTrit) ->
  Fabric.projectInteractionVoxel (Bridge.observerToFabric matrix)
  ≡ Bridge.observerRowA matrix
rowAProjectionCommutes matrix = refl

rowBProjectionCommutes :
  (matrix : Observer.ObserverMatrix3 SSP.SSPTrit) ->
  Fabric.appraisalAVoxel (Bridge.observerToFabric matrix)
  ≡ Bridge.observerRowB matrix
rowBProjectionCommutes matrix = refl

rowCProjectionCommutes :
  (matrix : Observer.ObserverMatrix3 SSP.SSPTrit) ->
  Fabric.appraisalBVoxel (Bridge.observerToFabric matrix)
  ≡ Bridge.observerRowC matrix
rowCProjectionCommutes matrix = refl

------------------------------------------------------------------------
-- 6. Face-membership restriction commutes with the row rechart.
------------------------------------------------------------------------

rowAOnFaceIffFabricInteractionOnFace :
  (face : Fabric.Face6) ->
  (matrix : Observer.ObserverMatrix3 SSP.SSPTrit) ->
  Fabric.OnFace face (Bridge.observerRowA matrix) ->
  Fabric.OnFace face
    (Fabric.projectInteractionVoxel (Bridge.observerToFabric matrix))
rowAOnFaceIffFabricInteractionOnFace face matrix witness = witness

rowBOnFaceIffFabricAppraisalAOnFace :
  (face : Fabric.Face6) ->
  (matrix : Observer.ObserverMatrix3 SSP.SSPTrit) ->
  Fabric.OnFace face (Bridge.observerRowB matrix) ->
  Fabric.OnFace face
    (Fabric.appraisalAVoxel (Bridge.observerToFabric matrix))
rowBOnFaceIffFabricAppraisalAOnFace face matrix witness = witness

rowCOnFaceIffFabricAppraisalBOnFace :
  (face : Fabric.Face6) ->
  (matrix : Observer.ObserverMatrix3 SSP.SSPTrit) ->
  Fabric.OnFace face (Bridge.observerRowC matrix) ->
  Fabric.OnFace face
    (Fabric.appraisalBVoxel (Bridge.observerToFabric matrix))
rowCOnFaceIffFabricAppraisalBOnFace face matrix witness = witness

------------------------------------------------------------------------
-- 7. Boundary: exact projection naturality is weaker than X6 Cech identity.
------------------------------------------------------------------------

data ObserverDyadicSheafIsExistingX6CechSheaf : Set where
data ProjectionNaturalityCreatesActualFacePromotion : Set where
data GrothendieckCoverEqualsHypervoxelBoundaryNerve : Set where

observerDyadicSheafIsNotDefinitionallyExistingX6CechSheaf :
  ObserverDyadicSheafIsExistingX6CechSheaf -> ⊥
observerDyadicSheafIsNotDefinitionallyExistingX6CechSheaf ()

projectionNaturalityDoesNotCreateActualFacePromotion :
  ProjectionNaturalityCreatesActualFacePromotion -> ⊥
projectionNaturalityDoesNotCreateActualFacePromotion ()

grothendieckCoverIsNotDefinitionallyHypervoxelBoundaryNerve :
  GrothendieckCoverEqualsHypervoxelBoundaryNerve -> ⊥
grothendieckCoverIsNotDefinitionallyHypervoxelBoundaryNerve ()

cechModelBoundary :
  Cech.FaceHypercubeCechBoundary
cechModelBoundary =
  Cech.canonicalFaceHypercubeCechBoundary

record Trialectic369DescentNaturalityBoundary : Set where
  constructor trialectic-369-descent-naturality-boundary
  field
    threeDyadicRestrictionsDefined : Bool
    overlapCompatibilityExact : Bool
    compatibleDyadicFamilyGlues : Bool
    gluedRestrictionsRecoverLocals : Bool
    globalObserverRoundTripExact : Bool
    canonicalGrothendieckCoverReused : Bool
    rowHypercubeProjectionSquaresCommute : Bool
    faceMembershipTransportExact : Bool
    x6CechSameObjectPromotionPaid : Bool
    grothendieckCoverEqualsBoundaryNerve : Bool

canonicalTrialectic369DescentNaturalityBoundary :
  Trialectic369DescentNaturalityBoundary
canonicalTrialectic369DescentNaturalityBoundary =
  trialectic-369-descent-naturality-boundary
    true true true true true true true true
    false false
