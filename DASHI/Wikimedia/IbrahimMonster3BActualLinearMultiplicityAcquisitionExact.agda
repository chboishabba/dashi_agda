module DASHI.Wikimedia.IbrahimMonster3BActualLinearMultiplicityAcquisitionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
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
--   S_zeta = Hom_E(H_zeta , W_zeta)
--
-- and the Moonshine lane now has a typed bridge for a linear 196883 Monster
-- constituent in weight two.  The remaining theorem-bearing payment is not a
-- new dimension coincidence: it is the SAME-OBJECT weld from that actual
-- Monster linear action, through the literal zeta eigensector, to the actual
-- multiplicity action whose character is the already-paid 12+78 family.
--
-- This owner records that acquisition contract.  It deliberately does not
-- inhabit it and therefore does not manufacture matrices, an inertia action or
-- an intertwiner from degree occurrence, Fin 90 basis labels, or identifiers.
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

record ActualLinearMultiplicityAcquisition : Set₁ where
  field
    -- Existing canonical linear surfaces.  These are not replaced by a new
    -- representation ontology.
    linearZetaProducer : LinearZeta.LinearSingleActionProducer
    multiplicityHomSpace : Hom.ActualLinearMultiplicityHomSpace

    -- Same-object receipts still requiring an actual producer/acquisition.
    sameLiteralZetaSector : Set
    weightTwo196883ActionIsSameMonsterAction : Set
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
    weightTwoLinearActionBridgeInterfaceAvailable : Bool
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
    true true true true true true false
    false false false
    "instantiate the existing weight-two linear Monster bridge on the SAME 196883 action used by the selected 3B single-action producer; restrict that action linearly to the literal W_zeta eigensector; construct S_zeta = Hom_E(H_zeta,W_zeta) with the source-native inertia action; then weld the paid 17496 and 113724 restriction constituents to the 12 and 78 factors by an actual same-action character/intertwiner receipt. Degree occurrence, Fin90 basis labels, character equality, DOI/QID/Dewey/OEIS coordinates, and the generic Hom-space type do not pay this receipt."

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

weightTwoBoundary : WeightTwo.WeightTwoLinearActionBoundary
weightTwoBoundary = WeightTwo.canonicalWeightTwoLinearActionBoundary
