module DASHI.Wikimedia.IbrahimMonster3BSuzukiQuotientDescentCorrectionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Wikimedia.IbrahimMonster3BSuzukiMultiplicityCharacterSnowballExact as Suzuki

------------------------------------------------------------------------
-- QUOTIENT-DESCENT CORRECTION
--
-- Historical state:
--   IbrahimMonster3BSuzukiMultiplicityCharacterSnowballExact initially used
--   an equality between the Suzuki central phase and the selected Heisenberg
--   phase as a field in SourceNativeMultiplicityFactorisation.
--
-- Source archaeology does NOT pay that equality.  Barraclough--Wilson first
-- construct the main group
--
--   3^(1+12):6.Suz.2
--
-- and then obtain N(3B) as a quotient.  Their supplementary qGtoN3B class map
-- is therefore the correct decision object.  A tensor character descends when
-- it is compatible with the quotient kernel.  Whether this corresponds to
-- equal or inverse phase labels depends on the concrete central-product
-- convention and must be recovered from the character/quotient data rather
-- than guessed.
--
-- This owner is append-only correction metadata plus the canonical corrected
-- interface.  It does not rewrite or instantiate the historical over-strong
-- record.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- 1. Source roles.
------------------------------------------------------------------------

paperSource : Attribution.AttributedSource
paperSource = Suzuki.barracloughWilson

paperAttribution = Snowball.canonicalSourceRoleSnowballReceipt paperSource

supplementarySource : Attribution.AttributedSource
supplementarySource = Attribution.mkNoDOISource
  "R. W. Barraclough; R. A. Wilson"
  "N3BetcTables.tar.gz / N3BetcQuotientMaps.gap"
  "supplementary files for The Character Table of a Maximal Subgroup of the Monster"
  "2007"
  "https://www.rwb.me.uk/table/index.html"
  (Attribution.namedSourceKind "primary supplementary computational source")
  "primary attached source for qGtoN3B and the related class/fusion maps; archive artifact has no separate DOI asserted, while the associated paper DOI remains 10.1112/S1461157000001352"
  Attribution.publicAttribution

supplementaryAttribution = Snowball.canonicalSourceRoleSnowballReceipt supplementarySource

acquisitionMirrorSource : Attribution.AttributedSource
acquisitionMirrorSource = Attribution.mkNoDOISource
  "Mike DuPont mirror of Barraclough--Wilson supplementary files"
  "N3BetcFusionMaps.gap gist bundle"
  "public acquisition mirror"
  "2026-07-13 mirror snapshot"
  "https://gist.github.com/jmikedupont2/b6ed15f8acb36b4f9837b7e0b0e43890"
  (Attribution.namedSourceKind "acquisition mirror")
  "byte/text acquisition convenience only; mathematical and historical authority remains the Barraclough--Wilson primary paper and author-hosted supplement"
  Attribution.publicAttribution

acquisitionMirrorAttribution =
  Snowball.canonicalSourceRoleSnowballReceipt acquisitionMirrorSource

paperDOI : String
paperDOI = "10.1112/S1461157000001352"

record QuotientDescentExternalCoordinates : Set where
  constructor quotient-descent-external-coordinates
  field
    groupRepresentationQid : String
    representationCharacterQid : String
    finiteGroupQid : String
    groupRepresentationDewey : String
    finiteGroupDewey : String
    oeisCoordinate : String
    oeisHasDescentAuthority : Bool
open QuotientDescentExternalCoordinates public

canonicalQuotientDescentExternalCoordinates : QuotientDescentExternalCoordinates
canonicalQuotientDescentExternalCoordinates =
  quotient-descent-external-coordinates
    "Q1055807"
    "Q600043"
    "Q1057968"
    "512.22"
    "512.23"
    "not applicable: quotient descent is a character/fusion condition; A005052 remains numerical provenance for 90 only"
    false

------------------------------------------------------------------------
-- 2. Corrected source-native interface.
------------------------------------------------------------------------

record QuotientCompatibleMultiplicityCharacter : Set₁ where
  constructor quotient-compatible-multiplicity-character
  field
    heisenbergExtension : Suzuki.ExtendedHeisenbergCharacter
    suzukiCharacter : Suzuki.SuzukiMultiplicityCharacter

    tensorCharacterConstruction : Set
    quotientKernelCompatibility : Set
    descendsThroughMainToMN3B : Set

open QuotientCompatibleMultiplicityCharacter public

record CorrectedSourceNativeMultiplicityFactorisation : Set₁ where
  constructor corrected-source-native-multiplicity-factorisation
  field
    twelveFactor : QuotientCompatibleMultiplicityCharacter
    seventyEightFactor : QuotientCompatibleMultiplicityCharacter

    twelveDegreeExact :
      Suzuki.degree (suzukiCharacter twelveFactor) ≡ 12
    seventyEightDegreeExact :
      Suzuki.degree (suzukiCharacter seventyEightFactor) ≡ 78

    inductionToOuterMainTable : Set
    mainTableToMN3BQuotientMap : Set
    fullClassFunctionMatchToPairedMN3BConstituents : Set
    sameObjectWithMonsterRestriction : Set

open CorrectedSourceNativeMultiplicityFactorisation public

------------------------------------------------------------------------
-- 3. Exact acquisition/payment order.
------------------------------------------------------------------------

record QuotientDescentPaymentOrder : Set where
  constructor quotient-descent-payment-order
  field
    observeSuzukiCandidatePhaseFirst : Bool
    observeSuzukiCandidatePhaseFirstIsTrue :
      observeSuzukiCandidatePhaseFirst ≡ true
    retainEqualOrInversePhaseHypotheses : Bool
    retainEqualOrInversePhaseHypothesesIsTrue :
      retainEqualOrInversePhaseHypotheses ≡ true
    payDescentOnlyFromQuotientKernelCompatibility : Bool
    payDescentOnlyFromQuotientKernelCompatibilityIsTrue :
      payDescentOnlyFromQuotientKernelCompatibility ≡ true
    payMonsterOccurrenceOnlyFromFullClassMatch : Bool
    payMonsterOccurrenceOnlyFromFullClassMatchIsTrue :
      payMonsterOccurrenceOnlyFromFullClassMatch ≡ true
open QuotientDescentPaymentOrder public

canonicalQuotientDescentPaymentOrder : QuotientDescentPaymentOrder
canonicalQuotientDescentPaymentOrder =
  quotient-descent-payment-order
    true refl
    true refl
    true refl
    true refl

------------------------------------------------------------------------
-- 4. WrongType / supersession boundaries.
------------------------------------------------------------------------

data EqualPhaseLabelCreatesQuotientDescent : Set where
data InversePhaseLabelCreatesQuotientDescent : Set where
data QuotientMapCreatesMonsterOccurrence : Set where
data AcquisitionMirrorCreatesPrimaryAuthority : Set where

equalPhaseDoesNotCreateDescent : EqualPhaseLabelCreatesQuotientDescent → ⊥
equalPhaseDoesNotCreateDescent ()

inversePhaseDoesNotCreateDescent : InversePhaseLabelCreatesQuotientDescent → ⊥
inversePhaseDoesNotCreateDescent ()

quotientMapDoesNotCreateMonsterOccurrence : QuotientMapCreatesMonsterOccurrence → ⊥
quotientMapDoesNotCreateMonsterOccurrence ()

mirrorDoesNotCreatePrimaryAuthority : AcquisitionMirrorCreatesPrimaryAuthority → ⊥
mirrorDoesNotCreatePrimaryAuthority ()

------------------------------------------------------------------------
-- 5. Current correction/frontier status.
------------------------------------------------------------------------

record QuotientDescentCorrectionFrontier : Set where
  constructor quotient-descent-correction-frontier
  field
    historicalPhaseEqualityRecognisedOverStrong : Bool
    supplementaryQGtoN3BLocated : Bool
    primarySupplementRoleSeparatedFromMirror : Bool
    correctedQuotientCompatibilityInterfaceOwned : Bool
    equalVsInversePhaseConventionPaid : Bool
    exactCandidateLabelsPaid : Bool
    exactMainTableRowsPaid : Bool
    fullClassFunctionMatchPaid : Bool
    actualMonsterMultiplicityRepresentationPaid : Bool
    nextResidual : String
open QuotientDescentCorrectionFrontier public

currentQuotientDescentCorrectionFrontier : QuotientDescentCorrectionFrontier
currentQuotientDescentCorrectionFrontier =
  quotient-descent-correction-frontier
    true true true true
    false false false false false
    "execute the 6.Suz candidate producer, then use the Barraclough-Wilson main table plus qGtoN3B to identify the paired main-table rows that pull back the actual paired MN3B constituents. Compare their restrictions to the complementary 6.Suz with all source-native 729-extension x 12a/12b and 729-extension x 78a/78b constructions. Let the unique full class-function match determine the phase convention; do not assume equal or inverse labels in advance."
