module DASHI.Moonshine.OggSSP2BSourceIndexedDVRValuationIdentificationExact where

------------------------------------------------------------------------
-- 2B SOURCE-INDEXED DVR / CORRECTED-VALUATION IDENTIFICATION
--
-- ATTRIBUTION
--
-- Carnahan (SIGMA 15 (2019), 030, Corollary 3.25) owns the
-- Monster-stable integral Moonshine form and the 2B Tate trace identity.
-- Urano (SIGMA 17 (2021), 110) owns the finite-length DVR generalized
-- Brauer-character theory.  Urano (Tsukuba thesis, 2023) supplies the
-- 2B parity exclusions and T_4A representation-ring functional.
--
-- DASHI supplies the five-sector inertia geometry and the independent
-- isotropy-denominator depths (3,3,2,1,1).  None of those sources
-- identifies an integral 2B source piece with an inertia sector or
-- proves that its composition length is the denominator depth.
--
-- This owner (i) exhibits a CONCRETE non-identifiability obstruction
-- for attempted recovery of lengths from the sourced parity constraint,
-- and (ii) isolates the actual same-object source-to-localized-to-analytic
-- theorem needed for a corrected valuation, without manufacturing it.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Moonshine.OggSSP2BUranoIntegralModuleParityExact as Urano
import DASHI.Moonshine.OggSSPP2BinaryTetrahedralInertiaFiveOrbitExact as Inertia
import DASHI.Moonshine.OggSSPP2InertiaStackDenominatorValuationExact as Geometry
import DASHI.Moonshine.OggSSPSmallCharacteristicPreferredCorrectionPaymentExact as Preferred
import DASHI.Moonshine.OggSSPSmallPrimePBIntegralTateCohomologyBridgeExact as Tate
import DASHI.Moonshine.OggSSPSmallPrimeDVRLengthBrauerCutsetExact as DVR
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Five source slots follow the independently fixed inertia-sector site.
-- A slot is a *request for* a source piece, not itself a Tate summand.
------------------------------------------------------------------------

data TwoBSourceSlot : Set where
  identitySlot : TwoBSourceSlot
  minusOneSlot : TwoBSourceSlot
  orderFourSlot : TwoBSourceSlot
  orderThreeSlot : TwoBSourceSlot
  orderSixSlot : TwoBSourceSlot

slotSector : TwoBSourceSlot -> Inertia.BinaryTetrahedralInversionOrbit
slotSector identitySlot = Inertia.identityInertiaOrbit
slotSector minusOneSlot = Inertia.centralMinusOneInertiaOrbit
slotSector orderFourSlot = Inertia.orderFourInertiaOrbit
slotSector orderThreeSlot = Inertia.orderThreePairInertiaOrbit
slotSector orderSixSlot = Inertia.orderSixPairInertiaOrbit

sectorSlot : Inertia.BinaryTetrahedralInversionOrbit -> TwoBSourceSlot
sectorSlot Inertia.identityInertiaOrbit = identitySlot
sectorSlot Inertia.centralMinusOneInertiaOrbit = minusOneSlot
sectorSlot Inertia.orderFourInertiaOrbit = orderFourSlot
sectorSlot Inertia.orderThreePairInertiaOrbit = orderThreeSlot
sectorSlot Inertia.orderSixPairInertiaOrbit = orderSixSlot

slotSectorRoundTrip :
  (slot : TwoBSourceSlot) ->
  sectorSlot (slotSector slot) ≡ slot
slotSectorRoundTrip identitySlot = refl
slotSectorRoundTrip minusOneSlot = refl
slotSectorRoundTrip orderFourSlot = refl
slotSectorRoundTrip orderThreeSlot = refl
slotSectorRoundTrip orderSixSlot = refl

sectorSlotRoundTrip :
  (sector : Inertia.BinaryTetrahedralInversionOrbit) ->
  slotSector (sectorSlot sector) ≡ sector
sectorSlotRoundTrip Inertia.identityInertiaOrbit = refl
sectorSlotRoundTrip Inertia.centralMinusOneInertiaOrbit = refl
sectorSlotRoundTrip Inertia.orderFourInertiaOrbit = refl
sectorSlotRoundTrip Inertia.orderThreePairInertiaOrbit = refl
sectorSlotRoundTrip Inertia.orderSixPairInertiaOrbit = refl

independentGeometricDepth : TwoBSourceSlot -> Nat
independentGeometricDepth slot =
  Geometry.sectorIsotropyDenominatorTwoAdicDepth (slotSector slot)

identityGeometricDepth : independentGeometricDepth identitySlot ≡ 3
identityGeometricDepth = refl

minusOneGeometricDepth : independentGeometricDepth minusOneSlot ≡ 3
minusOneGeometricDepth = refl

orderFourGeometricDepth : independentGeometricDepth orderFourSlot ≡ 2
orderFourGeometricDepth = refl

orderThreeGeometricDepth : independentGeometricDepth orderThreeSlot ≡ 1
orderThreeGeometricDepth = refl

orderSixGeometricDepth : independentGeometricDepth orderSixSlot ≡ 1
orderSixGeometricDepth = refl

------------------------------------------------------------------------
-- 2. Concrete non-identifiability of length from Urano parity data.
--
-- Both sample interpretations below satisfy the sourced exclusions:
-- choose an even-degree 'other' module tag throughout, never an even I2
-- nor an odd trivial Z2.  However the associated Nat-valued lengths
-- disagree.  These are COUNTERMODELS, NOT invented integral modules.
------------------------------------------------------------------------

record ParityTagAssignment : Set where
  constructor parity-tag-assignment
  field
    parity : TwoBSourceSlot -> Urano.DegreeParity
    moduleTag : TwoBSourceSlot -> Urano.TwoBModuleTag
    respectsExclusions :
      (slot : TwoBSourceSlot) ->
      Urano.TwoBSourceForbidden (parity slot) (moduleTag slot) -> ⊥

open ParityTagAssignment public

parityOnlyInterpretation : ParityTagAssignment
parityOnlyInterpretation =
  parity-tag-assignment
    (λ slot -> Urano.evenDegree)
    (λ slot -> Urano.otherIntegralModuleTag)
    (λ slot ())

zeroLengthModel : TwoBSourceSlot -> Nat
zeroLengthModel slot = 0

geometricLengthModel : TwoBSourceSlot -> Nat
geometricLengthModel = independentGeometricDepth

sameParityDataAllowsDifferentLengths :
  zeroLengthModel identitySlot ≡ geometricLengthModel identitySlot -> ⊥
sameParityDataAllowsDifferentLengths ()

parityTagDoesNotDetermineLength :
  (readLength :
    Urano.DegreeParity -> Urano.TwoBModuleTag -> Nat) ->
  ((slot : TwoBSourceSlot) ->
    readLength
      (parity parityOnlyInterpretation slot)
      (moduleTag parityOnlyInterpretation slot)
    ≡ zeroLengthModel slot) ->
  ((slot : TwoBSourceSlot) ->
    readLength
      (parity parityOnlyInterpretation slot)
      (moduleTag parityOnlyInterpretation slot)
    ≡ geometricLengthModel slot) ->
  ⊥
parityTagDoesNotDetermineLength readLength zeroLaw geometricLaw =
  sameParityDataAllowsDifferentLengths
    (trans
      (sym (zeroLaw identitySlot))
      (geometricLaw identitySlot))

------------------------------------------------------------------------
-- 3. Same-object source-to-valuation certificate.
--
-- The supplying theorem must select ACTUAL graded 2B Tate pieces from
-- Carnahan's integral Monster form.  A geometric slot names the output
-- indexing site; it is not allowed to create the source piece.
--
-- In particular, an independently chosen Nat assignment cannot
-- inhabit this certificate without simultaneously paying the source
-- inclusion, Igusa localization, finite DVR length, and analytic
-- Hauptmodul/q-expansion comparison for the SAME localized object.
------------------------------------------------------------------------

-- These constructor-free tokens are unpaid EXTERNAL SAME-OBJECT THEOREMS.
-- They are not declarations that the mathematical objects do not exist.
-- A genuine source derivation must introduce verified inhabitants; Boolean
-- flags or a chosen Nat weight vector are deliberately insufficient.
data ActualTwoBGradedSourceEmbeddingReceipt : Set where
data ActualIgusaLocalizationOfThatTwoBSourceReceipt : Set where
data ActualCorrectedHauptmodulComparisonReceipt : Set where

record TwoBSourceIndexedValuationAuthority : Set₁ where
  field
    actualSourceEmbeddingReceipt :
      ActualTwoBGradedSourceEmbeddingReceipt

    actualIgusaLocalizationReceipt :
      ActualIgusaLocalizationOfThatTwoBSourceReceipt

    actualAnalyticComparisonReceipt :
      ActualCorrectedHauptmodulComparisonReceipt

    SourcePiece : Set
    LocalizedPiece : Set
    AnalyticTerm : Set

    sourceAtSlot : TwoBSourceSlot -> SourcePiece
    sourceDegree : SourcePiece -> Nat
    sourceParity : SourcePiece -> Urano.DegreeParity
    sourceModuleTag : SourcePiece -> Urano.TwoBModuleTag

    sourcePieceBelongsToActualIntegral2BTateWeightSpace :
      (slot : TwoBSourceSlot) -> Bool
    sourcePieceBelongsToActualIntegral2BTateWeightSpaceIsTrue :
      (slot : TwoBSourceSlot) ->
      sourcePieceBelongsToActualIntegral2BTateWeightSpace slot ≡ true

    sourcePieceParityMatchesUrano :
      (slot : TwoBSourceSlot) ->
      Urano.TwoBSourceForbidden
        (sourceParity (sourceAtSlot slot))
        (sourceModuleTag (sourceAtSlot slot)) -> ⊥

    localizeActualSourcePiece : SourcePiece -> LocalizedPiece

    -- A single localized object cannot be silently used as two different
    -- inertia-sector witnesses.  This is a typed provenance condition rather
    -- than a separate Boolean claim that the five slots are distinct.
    localizedInertiaSector :
      LocalizedPiece -> Inertia.BinaryTetrahedralInversionOrbit
    localizedSectorIsRequestedSector :
      (slot : TwoBSourceSlot) ->
      localizedInertiaSector
        (localizeActualSourcePiece (sourceAtSlot slot))
      ≡ slotSector slot

    localizedAtPrimeTwoEqualsLevelBadGeometry :
      (slot : TwoBSourceSlot) -> Bool
    localizedAtPrimeTwoEqualsLevelBadGeometryIsTrue :
      (slot : TwoBSourceSlot) ->
      localizedAtPrimeTwoEqualsLevelBadGeometry slot ≡ true

    normalizedDVRCompositionLength : LocalizedPiece -> Nat
    comesWithActualFiniteDVRCompositionSeries :
      (slot : TwoBSourceSlot) -> Bool
    comesWithActualFiniteDVRCompositionSeriesIsTrue :
      (slot : TwoBSourceSlot) ->
      comesWithActualFiniteDVRCompositionSeries slot ≡ true

    lengthIsIndependentIsotropyDepth :
      (slot : TwoBSourceSlot) ->
      normalizedDVRCompositionLength
        (localizeActualSourcePiece (sourceAtSlot slot))
      ≡ independentGeometricDepth slot

    analyticTermFromLocalizedSource : LocalizedPiece -> AnalyticTerm
    analyticTermUsesCarnahanUranoTraceFunctional :
      (slot : TwoBSourceSlot) -> Bool
    analyticTermUsesCarnahanUranoTraceFunctionalIsTrue :
      (slot : TwoBSourceSlot) ->
      analyticTermUsesCarnahanUranoTraceFunctional slot ≡ true

    analyticTermContributesToCorrectedHauptmodulValuation :
      (slot : TwoBSourceSlot) -> Bool
    analyticTermContributesToCorrectedHauptmodulValuationIsTrue :
      (slot : TwoBSourceSlot) ->
      analyticTermContributesToCorrectedHauptmodulValuation slot ≡ true

    analyticMultiplicity : AnalyticTerm -> Nat
    sameLocalizedPiecePaysAnalyticMultiplicity :
      (slot : TwoBSourceSlot) ->
      analyticMultiplicity
        (analyticTermFromLocalizedSource
          (localizeActualSourcePiece (sourceAtSlot slot)))
      ≡ normalizedDVRCompositionLength
          (localizeActualSourcePiece (sourceAtSlot slot))

    noMonsterOrderTargetUsedToSelectSourcePieces : Bool
    noMonsterOrderTargetUsedToSelectSourcePiecesIsTrue :
      noMonsterOrderTargetUsedToSelectSourcePieces ≡ true

open TwoBSourceIndexedValuationAuthority public

------------------------------------------------------------------------
-- 4. Conditional exact sectorwise consequence, NOT unconditional payment.
------------------------------------------------------------------------

sourceLengthAtIdentity :
  (A : TwoBSourceIndexedValuationAuthority) ->
  normalizedDVRCompositionLength A
    (localizeActualSourcePiece A (sourceAtSlot A identitySlot))
  ≡ 3
sourceLengthAtIdentity A =
  trans (lengthIsIndependentIsotropyDepth A identitySlot)
        identityGeometricDepth

sourceLengthAtMinusOne :
  (A : TwoBSourceIndexedValuationAuthority) ->
  normalizedDVRCompositionLength A
    (localizeActualSourcePiece A (sourceAtSlot A minusOneSlot))
  ≡ 3
sourceLengthAtMinusOne A =
  trans (lengthIsIndependentIsotropyDepth A minusOneSlot)
        minusOneGeometricDepth

sourceLengthAtOrderFour :
  (A : TwoBSourceIndexedValuationAuthority) ->
  normalizedDVRCompositionLength A
    (localizeActualSourcePiece A (sourceAtSlot A orderFourSlot))
  ≡ 2
sourceLengthAtOrderFour A =
  trans (lengthIsIndependentIsotropyDepth A orderFourSlot)
        orderFourGeometricDepth

sourceLengthAtOrderThree :
  (A : TwoBSourceIndexedValuationAuthority) ->
  normalizedDVRCompositionLength A
    (localizeActualSourcePiece A (sourceAtSlot A orderThreeSlot))
  ≡ 1
sourceLengthAtOrderThree A =
  trans (lengthIsIndependentIsotropyDepth A orderThreeSlot)
        orderThreeGeometricDepth

sourceLengthAtOrderSix :
  (A : TwoBSourceIndexedValuationAuthority) ->
  normalizedDVRCompositionLength A
    (localizeActualSourcePiece A (sourceAtSlot A orderSixSlot))
  ≡ 1
sourceLengthAtOrderSix A =
  trans (lengthIsIndependentIsotropyDepth A orderSixSlot)
        orderSixGeometricDepth

analyticLengthAtSlot :
  (A : TwoBSourceIndexedValuationAuthority) ->
  (slot : TwoBSourceSlot) ->
  analyticMultiplicity A
    (analyticTermFromLocalizedSource A
      (localizeActualSourcePiece A (sourceAtSlot A slot)))
  ≡ independentGeometricDepth slot
analyticLengthAtSlot A slot =
  trans
    (sameLocalizedPiecePaysAnalyticMultiplicity A slot)
    (lengthIsIndependentIsotropyDepth A slot)

------------------------------------------------------------------------
-- 4b. Same-object provenance prevents accidental reuse across sectors.
------------------------------------------------------------------------

differentSectorsRequireDifferentLocalizedObjects :
  (A : TwoBSourceIndexedValuationAuthority) ->
  (left right : TwoBSourceSlot) ->
  localizeActualSourcePiece A (sourceAtSlot A left)
    ≡ localizeActualSourcePiece A (sourceAtSlot A right) ->
  slotSector left ≡ slotSector right
differentSectorsRequireDifferentLocalizedObjects A left right same =
  trans
    (sym (localizedSectorIsRequestedSector A left))
    (trans
      (cong (localizedInertiaSector A) same)
      (localizedSectorIsRequestedSector A right))

slotsCannotCollapseUnderLocalization :
  (A : TwoBSourceIndexedValuationAuthority) ->
  (left right : TwoBSourceSlot) ->
  localizeActualSourcePiece A (sourceAtSlot A left)
    ≡ localizeActualSourcePiece A (sourceAtSlot A right) ->
  left ≡ right
slotsCannotCollapseUnderLocalization A left right same =
  trans
    (sym (slotSectorRoundTrip left))
    (trans
      (cong sectorSlot
        (differentSectorsRequireDifferentLocalizedObjects A left right same))
      (slotSectorRoundTrip right))

------------------------------------------------------------------------
-- 5. Existing source authority stays attributed by its own owner.
------------------------------------------------------------------------

integralTateReceipt :
  Tate.PBIntegralTateBridgeBoundary
integralTateReceipt =
  Tate.canonicalPBIntegralTateBridgeBoundary

dvrUranoReceipt :
  DVR.DVRLengthBrauerCutsetBoundary
dvrUranoReceipt =
  DVR.canonicalDVRLengthBrauerCutsetBoundary

data SourceIndexedValuationAuthorityAlreadyInhabited : Set where

sourceIndexedValuationNotYetInhabitedHere :
  SourceIndexedValuationAuthorityAlreadyInhabited -> ⊥
sourceIndexedValuationNotYetInhabitedHere ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin = Attribution.openRecognitionConjecture
