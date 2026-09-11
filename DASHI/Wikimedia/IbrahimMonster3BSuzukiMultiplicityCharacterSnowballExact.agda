module DASHI.Wikimedia.IbrahimMonster3BSuzukiMultiplicityCharacterSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Moonshine.Monster3BWilsonPublishedRestrictionReconciliationExact as Wilson
import DASHI.Moonshine.Monster3BFiniteStoneVonNeumannUniquenessBidiExact as Stone
import DASHI.Wikimedia.IbrahimMonster3BInertiaPhaseResolutionProducerSnowballExact as Fallback

------------------------------------------------------------------------
-- SOURCE-NATIVE 3B MULTIPLICITY CHARACTER ROUTE
--
-- Barraclough--Wilson Section 5.1 gives a stronger object than the later
-- degree-only 12+78 normalizer observation:
--
--   * the two degree-729 irreducibles psi, psiBar of 3^(1+12) BOTH extend to
--       G = 3^(1+12):6.Suz;
--   * any etaHat in Irr(6.Suz) inflates to eta in Irr(G);
--   * psi*eta is induced to the outer index-two group G:2, with the splitting
--     and fusion cases handled explicitly by Clifford theory.
--
-- Therefore the canonical multiplicity fibre is a 6.Suz representation fibre,
-- not a bare Fin 90 and not an arbitrary partition 12+78.
------------------------------------------------------------------------

heisenbergDegree : Nat
heisenbergDegree = 729

twelveMultiplicityDegree : Nat
twelveMultiplicityDegree = 12

seventyEightMultiplicityDegree : Nat
seventyEightMultiplicityDegree = 78

multiplicityTotal : Nat
multiplicityTotal = twelveMultiplicityDegree + seventyEightMultiplicityDegree

multiplicityTotalIsNinety : multiplicityTotal ≡ 90
multiplicityTotalIsNinety = refl

firstTensorDegree : Nat
firstTensorDegree = heisenbergDegree * twelveMultiplicityDegree

secondTensorDegree : Nat
secondTensorDegree = heisenbergDegree * seventyEightMultiplicityDegree

firstTensorDegreeIs8748 : firstTensorDegree ≡ 8748
firstTensorDegreeIs8748 = refl

secondTensorDegreeIs56862 : secondTensorDegree ≡ 56862
secondTensorDegreeIs56862 = refl

selectedPhaseTotal : Nat
selectedPhaseTotal = firstTensorDegree + secondTensorDegree

selectedPhaseTotalIs65610 : selectedPhaseTotal ≡ 65610
selectedPhaseTotalIs65610 = refl

pairedOuterTotal : Nat
pairedOuterTotal = 2 * selectedPhaseTotal

pairedOuterTotalIs131220 : pairedOuterTotal ≡ 131220
pairedOuterTotalIs131220 = refl

------------------------------------------------------------------------
-- Typed source-native carrier interface.
------------------------------------------------------------------------

data SelectedCentralPhase : Set where
  zetaPhase zetaSquaredPhase : SelectedCentralPhase

record SuzukiMultiplicityCharacter : Set where
  constructor suzuki-multiplicity-character
  field
    characterTablePosition : Nat
    degree : Nat
    faithful : Set
    centralPhase : SelectedCentralPhase

open SuzukiMultiplicityCharacter public

record ExtendedHeisenbergCharacter : Set where
  constructor extended-heisenberg-character
  field
    degree : Nat
    degreeIs729 : degree ≡ 729
    selectedPhase : SelectedCentralPhase
    extendsExtraspecialCharacter : Set
    actorIsThreeOnePlusTwelveSemidirectSixSuz : Set

open ExtendedHeisenbergCharacter public

record SourceNativeMultiplicityFactorisation : Set₁ where
  constructor source-native-multiplicity-factorisation
  field
    heisenbergExtension : ExtendedHeisenbergCharacter
    twelveCharacter : SuzukiMultiplicityCharacter
    seventyEightCharacter : SuzukiMultiplicityCharacter

    twelveDegreeExact : degree twelveCharacter ≡ 12
    seventyEightDegreeExact : degree seventyEightCharacter ≡ 78
    twelvePhaseMatchesHeisenberg : centralPhase twelveCharacter ≡ selectedPhase heisenbergExtension
    seventyEightPhaseMatchesHeisenberg : centralPhase seventyEightCharacter ≡ selectedPhase heisenbergExtension

    tensorCharacterConstruction : Set
    inductionToOuterNormalizerConstruction : Set
    sameObjectWithMonsterRestriction : Set

open SourceNativeMultiplicityFactorisation public

------------------------------------------------------------------------
-- Primary/source attribution.
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
  "primary source for the 729-character extension to 3^(1+12):6.Suz, inflation of Irr(6.Suz), tensoring, and induction/Clifford split to the outer group"
  Attribution.publicAttribution

ctbllibSource : Attribution.AttributedSource
ctbllibSource = Attribution.mkNoDOISource
  "Thomas Breuer and CTblLib contributors"
  "The GAP Character Table Library: 6.Suz / 6.Suz.2 tables and stored fusion"
  "GAP package data and documentation"
  "current computational producer dependency"
  "https://www.gap-system.org/Packages/ctbllib.html"
  (Attribution.namedSourceKind "software character-table source")
  "computational source for faithful degree-12/78 candidate enumeration and central-phase orientation; not mathematical theorem authority"
  Attribution.publicAttribution

barracloughWilsonAttribution = Snowball.canonicalSourceRoleSnowballReceipt barracloughWilson
ctbllibAttribution = Snowball.canonicalSourceRoleSnowballReceipt ctbllibSource

record SuzukiMultiplicityExternalCoordinates : Set where
  constructor suzuki-multiplicity-external-coordinates
  field
    groupRepresentationQid : String
    representationCharacterQid : String
    finiteGroupQid : String
    groupRepresentationDewey : String
    finiteGroupDewey : String
    oeisCoordinate : String
    oeisCreatesSuzukiCharacter : Bool
open SuzukiMultiplicityExternalCoordinates public

canonicalSuzukiMultiplicityExternalCoordinates : SuzukiMultiplicityExternalCoordinates
canonicalSuzukiMultiplicityExternalCoordinates = suzuki-multiplicity-external-coordinates
  "Q1055807" "Q600043" "Q1057968"
  "512.22" "512.23"
  "A005052 is retained only for 90 = 10*3^2; it does not identify 6.Suz characters"
  false

------------------------------------------------------------------------
-- Existing normalizer arithmetic remains a downstream cross-check.
------------------------------------------------------------------------

wilsonBoundary : Wilson.WilsonRestrictionBoundary
wilsonBoundary = Wilson.canonicalWilsonRestrictionBoundary

stoneBoundary : Stone.StoneVonNeumannUniquenessBidiBoundary
stoneBoundary = Stone.canonicalStoneVonNeumannUniquenessBidiBoundary

fallbackInertiaBoundary : Fallback.InertiaPhaseResolutionFrontier
fallbackInertiaBoundary = Fallback.currentInertiaPhaseResolutionFrontier

------------------------------------------------------------------------
-- WrongType / non-promotion boundaries.
------------------------------------------------------------------------

data DegreeTwelveCreatesSuzukiCharacter : Set where
data DegreeSeventyEightCreatesSuzukiCharacter : Set where
data NinetyCreatesDirectSumRepresentation : Set where
data FaithfulSuzukiCharacterCreatesMonsterOccurrence : Set where
data SourceTensorFormulaCreatesSameObjectMonsterIntertwiner : Set where

degree12DoesNotCreateCharacter : DegreeTwelveCreatesSuzukiCharacter → ⊥
degree12DoesNotCreateCharacter ()

degree78DoesNotCreateCharacter : DegreeSeventyEightCreatesSuzukiCharacter → ⊥
degree78DoesNotCreateCharacter ()

ninetyDoesNotCreateDirectSum : NinetyCreatesDirectSumRepresentation → ⊥
ninetyDoesNotCreateDirectSum ()

faithfulnessDoesNotCreateMonsterOccurrence : FaithfulSuzukiCharacterCreatesMonsterOccurrence → ⊥
faithfulnessDoesNotCreateMonsterOccurrence ()

sourceFormulaDoesNotCreateSameObjectIntertwiner :
  SourceTensorFormulaCreatesSameObjectMonsterIntertwiner → ⊥
sourceFormulaDoesNotCreateSameObjectIntertwiner ()

------------------------------------------------------------------------
-- Highest-alpha frontier.
------------------------------------------------------------------------

record SuzukiMultiplicityFrontier : Set where
  constructor suzuki-multiplicity-frontier
  field
    primary729ExtensionSourcePaid : Bool
    primaryTensorInductionFormulaPaid : Bool
    sixSuzTableAvailableAsProducer : Bool
    faithfulTwelveSeventyEightCandidateProducerWritten : Bool
    candidateProducerExecuted : Bool
    exactTwelveCharacterPositionPaid : Bool
    exactSeventyEightCharacterPositionPaid : Bool
    selectedPhaseOrientationPaid : Bool
    sameObjectMonsterRestrictionMatchPaid : Bool
    centralizerTableReconstructionStillMandatory : Bool
    nextResidual : String
open SuzukiMultiplicityFrontier public

currentSuzukiMultiplicityFrontier : SuzukiMultiplicityFrontier
currentSuzukiMultiplicityFrontier = suzuki-multiplicity-frontier
  true true true true
  false false false false false
  false
  "execute scripts/monster_3b_suzuki_multiplicity_characters.g to enumerate faithful degree-12 and degree-78 6.Suz irreducibles and their central C3 phases. Then match the resulting exact table positions through the Barraclough-Wilson psi*eta induction formula to the two paired MN3B constituents already isolated by monster_3b_normalizer_restriction.g. Only that same-object match pays the actual 12+78 multiplicity representation. The standalone 3^(1+12).2.Suz centralizer-table reconstruction is an optional fallback, not a prerequisite."
