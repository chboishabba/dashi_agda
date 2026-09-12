module DASHI.Wikimedia.IbrahimMonster3BActualLinearMultiplicityAcquisitionExact where

open import DASHI.Core.Prelude
open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Moonshine.GradedVertexOperatorAlgebraBoundary as GVOA
import DASHI.Moonshine.MonsterGradedVOABridgeExact as Legacy
import DASHI.Moonshine.VertexOperatorAlgebraCore as Core
import DASHI.Moonshine.MonsterGradedVOALiteralActionSameObjectBidiExact as LiteralWeld
import DASHI.Moonshine.VertexOperatorAlgebraLinearActionReceiptExact as LiteralVOA
import DASHI.Moonshine.GradedVOAHomogeneousLinearRealisationExact as Homogeneous
import DASHI.Moonshine.MonsterWeightTwoLinearActionBridgeExact as WeightTwo
import DASHI.Wikimedia.IbrahimMonster3BModernRestrictionTwelveSeventyEightOccurrenceSnowballExact as Occurrence
import DASHI.Wikimedia.IbrahimMonster3BLinearZetaSectorRestrictionExact as LinearZeta
import DASHI.Wikimedia.IbrahimMonster3BLinearMultiplicityHomSpaceExact as Hom
import DASHI.Wikimedia.IbrahimMonster3BMultiplicityBasisLinearWrongTypeCorrectionExact as WrongType

------------------------------------------------------------------------
-- HIGHEST-ALPHA ACQUISITION BOUNDARY: DEGREE OCCURRENCE -> ACTUAL LINEAR ACTION
--
-- Source snowballing has already paid occurrence of the 17496 and 113724
-- constituents in the actual Monster N(3B) restriction.  Independently, the
-- linear audit has named the canonical multiplicity object
--
--   S_zeta = Hom_E(H_zeta , W_zeta).
--
-- The repository also already owns a same-object weld joining exact graded
-- character authority to the LITERAL VOA state action on the same Monster
-- element type.  This owner therefore makes the next payment typed rather than
-- verbal: an acquisition must carry that exact weld AND a linearity receipt on
-- that exact literal VOA group action before it can descend through grade two,
-- the 196883 constituent, the selected 3B action and the literal zeta sector.
--
-- Nothing here manufactures the missing inhabitant, matrices, inertia action
-- or intertwiner from dimensions, degree occurrence, Fin 90 labels, or source
-- identifiers.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- 1. Attribution remains source-role precise.
------------------------------------------------------------------------

barracloughWilson : Attribution.AttributedSource
barracloughWilson = Attribution.mkDOISource
  "R. W. Barraclough; R. A. Wilson"
  "The Character Table of a Maximal Subgroup of the Monster"
  "LMS Journal of Computation and Mathematics 10, 161-175"
  "2007"
  "10.1112/S1461157000001352"
  "https://doi.org/10.1112/S1461157000001352"
  Attribution.academicArticleSource
  "primary source for the inertia-group character construction and 12+78 multiplicity character; it does not by itself supply the same-object matrices or intertwiner"
  Attribution.publicAttribution

anWilson : Attribution.AttributedSource
anWilson = Attribution.mkDOISource
  "Jianbei An; R. A. Wilson"
  "The Alperin weight conjecture and Uno's conjecture for the Monster M, p odd"
  "LMS Journal of Computation and Mathematics 13, 320-356"
  "2010"
  "10.1112/S1461157009000059"
  "https://doi.org/10.1112/S1461157009000059"
  Attribution.academicArticleSource
  "published irreducible-degree inventory used in the actual Monster restriction occurrence argument; not authority for a chosen linear realization"
  Attribution.publicAttribution

barracloughWilsonAttribution = Snowball.canonicalSourceRoleSnowballReceipt barracloughWilson
anWilsonAttribution = Snowball.canonicalSourceRoleSnowballReceipt anWilson

------------------------------------------------------------------------
-- 2. Proof-bearing acquisition contract.
------------------------------------------------------------------------

record ActualLinearMultiplicityAcquisition {Monster K : Set} : Setω where
  field
    -- Existing SAME-object character/action weld.
    literalSameObjectWeld :
      LiteralWeld.MonsterGradedVOALiteralActionWeld Monster K

    -- The standard VOA-linearity receipt must be attached to that exact
    -- literal VOA and that exact Monster action, not to a parallel carrier.
    literalVOALinearityReceipt :
      LiteralVOA.VOAGroupActionLinearReceipt
        (GVOA.group
          (Legacy.voaAction
            (LiteralWeld.gradedAuthority literalSameObjectWeld)))
        (LiteralWeld.LiteralVOA literalSameObjectWeld)
        (Core.monsterAction
          (LiteralWeld.literalVOA literalSameObjectWeld))

    -- Existing canonical linear multiplicity surfaces.
    linearZetaProducer : LinearZeta.LinearSingleActionProducer
    multiplicityHomSpace : Hom.ActualLinearMultiplicityHomSpace

    -- Same-object receipts still requiring an actual producer/acquisition.
    homogeneousGradeTwoIsSameLiteralVOAModule : Set
    weightTwo196883ActionIsSameMonsterAction : Set
    sameLiteralZetaSector : Set
    degree17496SameObject : Set
    degree113724SameObject : Set
    sourcePaidCharacterOnSameAction : Set
    actualMultiplicityActionIsSourceNativeInertiaAction : Set
    twelveSeventyEightLinearIntertwiner : Set

open ActualLinearMultiplicityAcquisition public

------------------------------------------------------------------------
-- 3. WrongType / non-promotion firewalls.
------------------------------------------------------------------------

data DegreeOccurrenceCreatesAction : Set where
data PermutationBasisCreatesLinearAction : Set where
data CharacterEqualityCreatesIntertwiner : Set where
data WeightTwoDimensionCreatesMultiplicityAction : Set where
data SameObjectWeldCreatesLinearity : Set where
data QidCreatesAction : Set where
data DeweyCreatesAction : Set where
data OeisCreatesAction : Set where

degreeOccurrenceDoesNotCreateAction : DegreeOccurrenceCreatesAction → ⊥
degreeOccurrenceDoesNotCreateAction ()

permutationBasisDoesNotCreateLinearAction : PermutationBasisCreatesLinearAction → ⊥
permutationBasisDoesNotCreateLinearAction ()

characterEqualityDoesNotCreateIntertwiner : CharacterEqualityCreatesIntertwiner → ⊥
characterEqualityDoesNotCreateIntertwiner ()

weightTwoDimensionDoesNotCreateMultiplicityAction :
  WeightTwoDimensionCreatesMultiplicityAction → ⊥
weightTwoDimensionDoesNotCreateMultiplicityAction ()

sameObjectWeldDoesNotCreateLinearity : SameObjectWeldCreatesLinearity → ⊥
sameObjectWeldDoesNotCreateLinearity ()

qidDoesNotCreateAction : QidCreatesAction → ⊥
qidDoesNotCreateAction ()

deweyDoesNotCreateAction : DeweyCreatesAction → ⊥
deweyDoesNotCreateAction ()

oeisDoesNotCreateAction : OeisCreatesAction → ⊥
oeisDoesNotCreateAction ()

------------------------------------------------------------------------
-- 4. DOI / QID / Dewey / OEIS coordinates remain descriptive only.
------------------------------------------------------------------------

record ActualLinearMultiplicityExternalCoordinates : Set where
  constructor actual-linear-multiplicity-external-coordinates
  field
    groupRepresentationQid : String
    representationCharacterQid : String
    finiteGroupQid : String
    groupRepresentationDewey : String
    finiteGroupDewey : String
    oeisCoordinate : String
    oeisHasActionAuthority : Bool
open ActualLinearMultiplicityExternalCoordinates public

canonicalActualLinearMultiplicityExternalCoordinates :
  ActualLinearMultiplicityExternalCoordinates
canonicalActualLinearMultiplicityExternalCoordinates =
  actual-linear-multiplicity-external-coordinates
    "Q1055807"
    "Q600043"
    "Q1057968"
    "512.22"
    "512.23"
    "A005052 remains numerical provenance for 90 = 10*3^2 only; it has no matrix, action, same-object or intertwiner authority"
    false

------------------------------------------------------------------------
-- 5. Pareto frontier.
------------------------------------------------------------------------

record ActualLinearMultiplicityAcquisitionFrontier : Set where
  constructor actual-linear-multiplicity-acquisition-frontier
  field
    degree17496OccurrencePaid : Bool
    degree113724OccurrencePaid : Bool
    twelveFactorOccurrencePaid : Bool
    seventyEightFactorOccurrencePaid : Bool
    canonicalLinearHomTargetNamed : Bool
    literalActionSameObjectWeldAvailable : Bool
    literalVOALinearityReceiptInterfaceAvailable : Bool
    homogeneousGradeLinearisationInterfaceAvailable : Bool
    weightTwoLinearActionBridgeInterfaceAvailable : Bool
    actualMonsterVOALinearityReceiptPaid : Bool
    finiteNinetyPermutationRouteIsCanonical : Bool
    actualLinearActionPaid : Bool
    sourceNativeInertiaSameActionPaid : Bool
    actualTwelveSeventyEightIntertwinerPaid : Bool
    nextResidual : String
open ActualLinearMultiplicityAcquisitionFrontier public

currentActualLinearMultiplicityAcquisitionFrontier :
  ActualLinearMultiplicityAcquisitionFrontier
currentActualLinearMultiplicityAcquisitionFrontier =
  actual-linear-multiplicity-acquisition-frontier
    true true true true true
    true true true true
    false false false false false
    "supply literalVOALinearityReceipt for the exact literalSameObjectWeld, then carry that same carrier/action through the existing homogeneous grade-2 and 196883 linear bridges and identify it with the State/action used by the selected 3B single-action producer. Only then restrict linearly to literal W_zeta, construct S_zeta = Hom_E(H_zeta,W_zeta) with the source-native inertia action, and weld the paid 17496 and 113724 constituents to 12 and 78 by an actual same-action character/intertwiner receipt. Degree occurrence, Fin90 basis labels, character equality, DOI/QID/Dewey/OEIS coordinates, and generic interfaces do not pay the inhabitant."

------------------------------------------------------------------------
-- 6. Imported status snapshots are routing information, not promotion.
------------------------------------------------------------------------

occurrenceFrontier : Occurrence.RestrictionOccurrenceFrontier
occurrenceFrontier = Occurrence.currentRestrictionOccurrenceFrontier

linearZetaFrontier : LinearZeta.LinearZetaSectorFrontier
linearZetaFrontier = LinearZeta.currentLinearZetaSectorFrontier

homFrontier : Hom.LinearMultiplicityHomFrontier
homFrontier = Hom.currentLinearMultiplicityHomFrontier

wrongTypeFrontier : WrongType.MultiplicityWrongTypeFrontier
wrongTypeFrontier = WrongType.currentMultiplicityWrongTypeFrontier

literalSameObjectBoundary : LiteralWeld.SameObjectWeldBoundary
literalSameObjectBoundary = LiteralWeld.canonicalSameObjectWeldBoundary

literalVOABoundary : LiteralVOA.VOAActionLinearReceiptBoundary
literalVOABoundary = LiteralVOA.canonicalVOAActionLinearReceiptBoundary

homogeneousGradeBoundary : Homogeneous.HomogeneousGradeLinearBoundary
homogeneousGradeBoundary = Homogeneous.canonicalHomogeneousGradeLinearBoundary

weightTwoBoundary : WeightTwo.WeightTwoLinearActionBoundary
weightTwoBoundary = WeightTwo.canonicalWeightTwoLinearActionBoundary
