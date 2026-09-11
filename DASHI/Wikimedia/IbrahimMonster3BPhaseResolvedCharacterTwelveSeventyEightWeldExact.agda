module DASHI.Wikimedia.IbrahimMonster3BPhaseResolvedCharacterTwelveSeventyEightWeldExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Wikimedia.IbrahimMonster3BSuzukiMultiplicityCharacterSnowballExact as Suzuki
import DASHI.Wikimedia.IbrahimMonster3BSuzukiQuotientDescentCorrectionExact as Descent
import DASHI.Wikimedia.IbrahimMonster3BModernRestrictionTwelveSeventyEightOccurrenceSnowballExact as Occurrence
import DASHI.Wikimedia.IbrahimMonster3BDiagonalKernelPaidSignGaugeCorrectionExact as Gauge

------------------------------------------------------------------------
-- PHASE-RESOLVED CHARACTER WELD: ACTUAL OUTER OCCURRENCE -> INERTIA HALVES
--
-- Barraclough--Wilson's source-native construction says:
--
--   * the two degree-729 irreducibles of the extraspecial 3^(1+12) extend to
--       I = 3^(1+12):6.Suz;
--   * the two nontrivial central phases are exchanged by the outer involution;
--   * the two extensions fuse to a degree-1458 character in the outer group;
--   * tensoring an extension psi_zeta with a 6.Suz character eta and inducing
--       outward is the source-native route to the nontrivial-central-character
--       irreducibles of the main table / N(3B) quotient.
--
-- The independent modern restriction + An--Wilson degree inventory now pays
-- the ACTUAL Monster occurrence of the unique paired outer degrees
--
--       17496  and  113724.
--
-- Hence, at CHARACTER/CLIFFORD level, one selected central phase has halves
--
--       17496 / 2 = 8748  = 729 * 12,
--       113724 / 2 = 56862 = 729 * 78,
--
-- and the selected-phase degree is 65610.
--
-- This is deliberately weaker than an actual representation/action theorem.
-- It does not construct matrices, a basis, W_zeta as a concrete carrier,
-- X6 x Fin 90, the multiplicity inertia action, or a 12+78 intertwiner.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- 1. Primary attribution remains source-native.
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
  "primary source for extension of the degree-729 extraspecial characters to 3^(1+12):6.Suz and the inertia-group tensor/induction construction"
  Attribution.publicAttribution

barracloughWilsonAttribution =
  Snowball.canonicalSourceRoleSnowballReceipt barracloughWilson

primaryDOI : String
primaryDOI = "10.1112/S1461157000001352"

------------------------------------------------------------------------
-- 2. Exact degree weld.
------------------------------------------------------------------------

outerTwelvePairedDegree : Nat
outerTwelvePairedDegree = 17496

outerSeventyEightPairedDegree : Nat
outerSeventyEightPairedDegree = 113724

selectedTwelvePhaseDegree : Nat
selectedTwelvePhaseDegree = 8748

selectedSeventyEightPhaseDegree : Nat
selectedSeventyEightPhaseDegree = 56862

selectedPhaseDegree : Nat
selectedPhaseDegree = selectedTwelvePhaseDegree + selectedSeventyEightPhaseDegree

outerTwelveIsTwoPhases : 2 * selectedTwelvePhaseDegree ≡ outerTwelvePairedDegree
outerTwelveIsTwoPhases = refl

outerSeventyEightIsTwoPhases : 2 * selectedSeventyEightPhaseDegree ≡ outerSeventyEightPairedDegree
outerSeventyEightIsTwoPhases = refl

selectedTwelveIs729Times12 : 729 * 12 ≡ selectedTwelvePhaseDegree
selectedTwelveIs729Times12 = refl

selectedSeventyEightIs729Times78 : 729 * 78 ≡ selectedSeventyEightPhaseDegree
selectedSeventyEightIs729Times78 = refl

selectedPhaseIs65610 : selectedPhaseDegree ≡ 65610
selectedPhaseIs65610 = refl

selectedMultiplicityIsNinety : 12 + 78 ≡ 90
selectedMultiplicityIsNinety = refl

------------------------------------------------------------------------
-- 3. Character-level receipt.  Conjugate orientation is intentionally not
--    chosen: zeta and zeta^2 exchange the two members of each family.
------------------------------------------------------------------------

record PhaseResolvedCharacterOccurrence : Set where
  constructor phase-resolved-character-occurrence
  field
    inertiaActor : String
    extraspecialDegree : Nat
    selectedTwelveDegree : Nat
    selectedSeventyEightDegree : Nat
    selectedTotalDegree : Nat
    outerTwelvePairedDegreePaid : Nat
    outerSeventyEightPairedDegreePaid : Nat
    degree729ExtensionSourcePaid : Bool
    outerInvolutionFusesCentralPhasesSourcePaid : Bool
    tensorInductionConstructionSourcePaid : Bool
    actualOuterTwelveOccurrencePaid : Bool
    actualOuterSeventyEightOccurrencePaid : Bool
    characterFamilyTwelveIdentified : Bool
    characterFamilySeventyEightIdentified : Bool
    absoluteZetaVsZetaSquaredOrientationPaid : Bool
    concreteRepresentationMatricesPaid : Bool
    actualFin90MultiplicityActionPaid : Bool
    actualTwelveSeventyEightIntertwinerPaid : Bool
open PhaseResolvedCharacterOccurrence public

canonicalPhaseResolvedCharacterOccurrence : PhaseResolvedCharacterOccurrence
canonicalPhaseResolvedCharacterOccurrence = phase-resolved-character-occurrence
  "3^(1+12):6.Suz"
  729
  8748
  56862
  65610
  17496
  113724
  true true true true true true true
  false false false false

------------------------------------------------------------------------
-- 4. Attribution coordinates: classification/navigation never create the weld.
------------------------------------------------------------------------

record PhaseCharacterExternalCoordinates : Set where
  constructor phase-character-external-coordinates
  field
    groupRepresentationQid : String
    representationCharacterQid : String
    finiteGroupQid : String
    groupRepresentationDewey : String
    finiteGroupDewey : String
    exactPrimaryArticleQid : String
    oeisCoordinate : String
    oeisHasCharacterWeldAuthority : Bool
open PhaseCharacterExternalCoordinates public

canonicalPhaseCharacterExternalCoordinates : PhaseCharacterExternalCoordinates
canonicalPhaseCharacterExternalCoordinates = phase-character-external-coordinates
  "Q1055807"
  "Q600043"
  "Q1057968"
  "512.22"
  "512.23"
  "unresolved rather than guessed for the exact Barraclough-Wilson article"
  "A005052 is numerical provenance for 90 = 10*3^2 only; it does not identify the inertia character or Monster occurrence"
  false

------------------------------------------------------------------------
-- 5. WrongType / non-promotion boundaries.
------------------------------------------------------------------------

data CharacterOccurrenceCreatesMatrices : Set where
data CharacterOccurrenceCreatesFin90Action : Set where
data CharacterOccurrenceCreatesIntertwiner : Set where
data CharacterOccurrenceCreatesActualZetaCarrier : Set where
data DegreeHalvingCreatesAbsolutePhaseOrientation : Set where
data OeisCreatesPhaseCharacter : Set where

characterOccurrenceDoesNotCreateMatrices : CharacterOccurrenceCreatesMatrices → ⊥
characterOccurrenceDoesNotCreateMatrices ()

characterOccurrenceDoesNotCreateFin90Action : CharacterOccurrenceCreatesFin90Action → ⊥
characterOccurrenceDoesNotCreateFin90Action ()

characterOccurrenceDoesNotCreateIntertwiner : CharacterOccurrenceCreatesIntertwiner → ⊥
characterOccurrenceDoesNotCreateIntertwiner ()

characterOccurrenceDoesNotCreateActualZetaCarrier : CharacterOccurrenceCreatesActualZetaCarrier → ⊥
characterOccurrenceDoesNotCreateActualZetaCarrier ()

degreeHalvingDoesNotOrientPhase : DegreeHalvingCreatesAbsolutePhaseOrientation → ⊥
degreeHalvingDoesNotOrientPhase ()

oeisDoesNotCreatePhaseCharacter : OeisCreatesPhaseCharacter → ⊥
oeisDoesNotCreatePhaseCharacter ()

------------------------------------------------------------------------
-- 6. Corrected highest-alpha frontier.
------------------------------------------------------------------------

record PhaseCharacterWeldFrontier : Set where
  constructor phase-character-weld-frontier
  field
    primaryInertiaConstructionPaid : Bool
    actualPaired17496OccurrencePaid : Bool
    actualPaired113724OccurrencePaid : Bool
    selectedPhase8748CharacterFamilyPaid : Bool
    selectedPhase56862CharacterFamilyPaid : Bool
    selectedPhase65610DegreePaid : Bool
    twelveMultiplicityAtCharacterLevelPaid : Bool
    seventyEightMultiplicityAtCharacterLevelPaid : Bool
    absoluteABPhaseNamingRequired : Bool
    concretePhaseResolvedMatricesPaid : Bool
    actualZetaSectorRecognitionPaid : Bool
    actualMultiplicityInertiaActionPaid : Bool
    sameActionTwelveSeventyEightIntertwinerPaid : Bool
    e6ActionIdentificationPaid : Bool
    nextResidual : String
open PhaseCharacterWeldFrontier public

currentPhaseCharacterWeldFrontier : PhaseCharacterWeldFrontier
currentPhaseCharacterWeldFrontier = phase-character-weld-frontier
  true true true true true true true true
  false false false false false false
  "the 12 and 78 factors are now paid at the phase-resolved CHARACTER-FAMILY level: actual paired Monster-normalizer constituents 17496 and 113724 arise from the source-native inertia construction with selected-phase halves 8748=729*12 and 56862=729*78, totaling 65610. Do not schedule further dimension/occurrence discovery or absolute a/b orientation. The next theorem-bearing leaf is representation-level: recover or construct a concrete chosen W_zeta carrier and an intertwining recognition with the existing X6 x Fin90 model; then transport the SAME inertia action to Fin90 and instantiate the existing ActualMultiplicityTwelveSeventyEightAttachment. Character occurrence alone cannot inhabit those action/intertwiner records."

suzukiFrontier : Suzuki.SuzukiMultiplicityFrontier
suzukiFrontier = Suzuki.currentSuzukiMultiplicityFrontier

occurrenceFrontier : Occurrence.RestrictionOccurrenceFrontier
occurrenceFrontier = Occurrence.currentRestrictionOccurrenceFrontier

gaugeFrontier : Gauge.DiagonalKernelGaugeCorrectionFrontier
gaugeFrontier = Gauge.currentDiagonalKernelGaugeCorrectionFrontier
