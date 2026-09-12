module DASHI.Wikimedia.IbrahimMonster3BActualLinearMultiplicityAcquisitionExact where

open import DASHI.Core.Prelude
open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Moonshine.GradedRepresentation as GR
import DASHI.Moonshine.GradedVertexOperatorAlgebraBoundary as GVOA
import DASHI.Moonshine.GradedRepresentationLinearRealisationExact as LinearRep
import DASHI.Moonshine.MonsterGradedVOABridgeExact as Legacy
import DASHI.Moonshine.VertexOperatorAlgebraCore as Core
import DASHI.Moonshine.MonsterGradedVOALiteralActionSameObjectBidiExact as LiteralWeld
import DASHI.Moonshine.VertexOperatorAlgebraLinearActionReceiptExact as LiteralVOA
import DASHI.Moonshine.MonsterWeightTwoLinearActionBridgeExact as WeightTwo
import DASHI.Wikimedia.IbrahimMonster3BModernRestrictionTwelveSeventyEightOccurrenceSnowballExact as Occurrence
import DASHI.Wikimedia.IbrahimMonster3BLinearZetaSectorRestrictionExact as LinearZeta
import DASHI.Wikimedia.IbrahimMonster3BLinearMultiplicityHomSpaceExact as Hom
import DASHI.Wikimedia.IbrahimMonster3BMultiplicityBasisLinearWrongTypeCorrectionExact as WrongType

------------------------------------------------------------------------
-- HIGHEST-ALPHA ACQUISITION BOUNDARY: DEGREE OCCURRENCE -> ACTUAL LINEAR ACTION
--
-- Source snowballing has already paid occurrence of the 17496 and 113724
-- constituents in the actual Monster N(3B) restriction. Independently, the
-- linear audit has named the canonical multiplicity object
--
--   S_zeta = Hom_E(H_zeta , W_zeta).
--
-- The repository already owns a same-object weld joining exact graded
-- character authority to the LITERAL VOA state action on the same Monster
-- element type. It also owns a generic linear realisation compiler for an exact
-- graded representation and a weight-two bridge carrying the linear 196883
-- constituent. The shortest route therefore meets those owners on the exact
-- grade-2 representation instead of inventing an equality between the two
-- different total-VOA APIs.
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

    -- Meet the legacy/linear route at the exact grade-2 representation. This
    -- avoids asserting an artificial equality between distinct total-VOA APIs.
    gradeTwoLinearRealisation :
      LinearRep.LinearEndomorphismRealisation
        (GVOA.group
          (Legacy.voaAction
            (LiteralWeld.gradedAuthority literalSameObjectWeld)))
        (GR.grade
          (GVOA.gradedRepresentation
            (Legacy.voaAction
              (LiteralWeld.gradedAuthority literalSameObjectWeld)))
          2)

    -- Existing 196883 linear constituent bridge on the SAME graded authority.
    weightTwoLinearBridge :
      WeightTwo.WeightTwoLinearActionBridge
        (LiteralWeld.gradedAuthority literalSameObjectWeld)

    -- The bridge must use this exact grade-2 realisation, not merely one with
    -- the same dimension/character.
    gradeTwoRealisationIsWeightTwoRealisation :
      gradeTwoLinearRealisation
      ≡ WeightTwo.fullWeightTwoLinearRealisation weightTwoLinearBridge

    -- Existing canonical linear multiplicity surfaces.
    linearZetaProducer : LinearZeta.LinearSingleActionProducer
    multiplicityHomSpace : Hom.ActualLinearMultiplicityHomSpace

    -- Same-object receipts still requiring the selected-3B / multiplicity
    -- producer. The first two previously loose grade-2/196883 seams are now
    -- discharged structurally by the typed fields above.
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
data GradeTwoDimensionCreatesRealisationEquality : Set where
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

gradeTwoDimensionDoesNotCreateRealisationEquality :
  GradeTwoDimensionCreatesRealisationEquality → ⊥
gradeTwoDimensionDoesNotCreateRealisationEquality ()

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
    gradeTwoLinearRealisationTyped : Bool
    weightTwoLinearBridgeTyped : Bool
    gradeTwoWeightTwoSameObjectRequired : Bool
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
    true true true true true
    false false false false false
    "inhabit literalVOALinearityReceipt and the exact gradeTwoLinearRealisation/weightTwoLinearBridge equality on the existing literalSameObjectWeld; then identify the WeightTwo 196883 constituent action with the State/action used by the selected 3B single-action producer. From that SAME action restrict linearly to literal W_zeta, construct S_zeta = Hom_E(H_zeta,W_zeta) with the source-native inertia action, and weld the paid 17496 and 113724 constituents to 12 and 78 by an actual same-action character/intertwiner receipt. Degree occurrence, Fin90 basis labels, character equality, DOI/QID/Dewey/OEIS coordinates, and generic interfaces do not pay the inhabitant."

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

weightTwoBoundary : WeightTwo.WeightTwoLinearActionBoundary
weightTwoBoundary = WeightTwo.canonicalWeightTwoLinearActionBoundary
