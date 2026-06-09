module DASHI.Physics.Closure.CarrierPhaseStructureReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.SupersingularPrimeLaneBridge as SSP

------------------------------------------------------------------------
-- Carrier phase-structure receipt.
--
-- This receipt records the finite carrier phase interpretation without
-- promoting Gate 3 or either Clay problem.  The phase carrier is treated
-- conceptually as the finite product of local unit groups (Z/pZ)^* over the
-- canonical SSP prime list.  The finite product order is recorded exactly
-- for that discrete carrier only.
--
-- FactorVec is explicitly bounded to valuation/amplitude data; it is not a
-- full continuum phase coordinate.  YM is marked easier only because the
-- physical Hilbert space quotients gauge phases.  NS has no analogous gauge
-- quotient in this receipt, so high-prime phases remain physical blockers.
-- Any carrier Gribov/gauge-fix statement below is discrete-only: Gate 3
-- continuum gauge fixing and continuum Gribov-freeness remain open.
-- The braid/KP correction is also fail-closed here: no Yang-Baxter theorem
-- and no KP theorem are implied by the finite phase carrier.

data CarrierPhaseStructureStatus : Set where
  safeFiniteSSPUnitProductConceptRecordedNoPromotion :
    CarrierPhaseStructureStatus

data SafeStatus : Set where
  failClosed :
    SafeStatus

data LocalUnitGroupConcept : Set where
  unitsOfZModP :
    Nat →
    LocalUnitGroupConcept

data CarrierPhaseGroupConcept : Set where
  finiteProductOfLocalUnitGroupsOverSSP :
    CarrierPhaseGroupConcept

data CarrierGribovBoundaryStatus : Set where
  discreteCarrierGaugeFixOnlyGate3ContinuumOpen :
    CarrierGribovBoundaryStatus

data PhaseGroupOrderStatus : Set where
  exactFiniteSSPUnitProductOrderRecorded :
    PhaseGroupOrderStatus

data P7AmplitudeUnitPhaseStatus : Set where
  p7AmplitudeZ7UnitPhaseZ6Incommensurable :
    P7AmplitudeUnitPhaseStatus

data FactorVecPhaseScope : Set where
  valuationsAndAmplitudesOnly :
    FactorVecPhaseScope

data YMPhaseQuotientStatus : Set where
  gaugePhasesQuotientedInPhysicalHilbertSpace :
    YMPhaseQuotientStatus

data NSPhaseQuotientStatus : Set where
  noAnalogousGaugeQuotientHighPrimePhasesPhysical :
    NSPhaseQuotientStatus

data CarrierSectorDensityStatus : Set where
  finiteCarrierVsCountableContinuumDensityOpen :
    CarrierSectorDensityStatus

data TrivialSectorDensityStatus : Set where
  trivialSectorDensityNotProvedNSPhysicalHighPrimeLoss :
    TrivialSectorDensityStatus

data BraidKPBoundaryStatus : Set where
  noYangBaxterOrKPTheoremFromPhaseCarrier :
    BraidKPBoundaryStatus

data DiscourseAritySemantics : Set where
  ternarySquareAsTwoPositions :
    DiscourseAritySemantics

  ternaryCubeAsDialogueThroughTimeSynthesis :
    DiscourseAritySemantics

data DiscourseSemanticsStatus : Set where
  discourseSemanticsRecordedAsCarrierBookkeepingOnly :
    DiscourseSemanticsStatus

data OpenCarrierPhaseObligation : Set where
  proveDiscreteCarrierGaugeFixExtendsToGate3ContinuumIfClaimed :
    OpenCarrierPhaseObligation

  bindFactorVecToContinuumPhaseCoordinateIfClaimed :
    OpenCarrierPhaseObligation

  bridgeFiniteCarrierSectorsToCountableContinuumDensityIfClaimed :
    OpenCarrierPhaseObligation

  accountForP7AmplitudeZ7VsUnitPhaseZ6Incommensurability :
    OpenCarrierPhaseObligation

  dischargeMissingHighPrimeNSPhysicalPhases :
    OpenCarrierPhaseObligation

canonicalOpenCarrierPhaseObligations :
  List OpenCarrierPhaseObligation
canonicalOpenCarrierPhaseObligations =
  proveDiscreteCarrierGaugeFixExtendsToGate3ContinuumIfClaimed
  ∷ bindFactorVecToContinuumPhaseCoordinateIfClaimed
  ∷ bridgeFiniteCarrierSectorsToCountableContinuumDensityIfClaimed
  ∷ accountForP7AmplitudeZ7VsUnitPhaseZ6Incommensurability
  ∷ dischargeMissingHighPrimeNSPhysicalPhases
  ∷ []

canonicalLocalUnitGroupConcepts :
  List LocalUnitGroupConcept
canonicalLocalUnitGroupConcepts =
  unitsOfZModP 2
  ∷ unitsOfZModP 3
  ∷ unitsOfZModP 5
  ∷ unitsOfZModP 7
  ∷ unitsOfZModP 11
  ∷ unitsOfZModP 13
  ∷ unitsOfZModP 17
  ∷ unitsOfZModP 19
  ∷ unitsOfZModP 23
  ∷ unitsOfZModP 29
  ∷ unitsOfZModP 31
  ∷ unitsOfZModP 41
  ∷ unitsOfZModP 47
  ∷ unitsOfZModP 59
  ∷ unitsOfZModP 71
  ∷ []

canonicalDiscourseAritySemantics :
  List DiscourseAritySemantics
canonicalDiscourseAritySemantics =
  ternarySquareAsTwoPositions
  ∷ ternaryCubeAsDialogueThroughTimeSynthesis
  ∷ []

data Gate3Promotion : Set where
data ClayPromotion : Set where

gate3PromotionImpossibleHere :
  Gate3Promotion →
  ⊥
gate3PromotionImpossibleHere ()

clayPromotionImpossibleHere :
  ClayPromotion →
  ⊥
clayPromotionImpossibleHere ()

carrierPhaseConceptSummary : String
carrierPhaseConceptSummary =
  "Carrier phase group is the finite product over SSP primes of local unit groups (Z/pZ)^* with exact order 229013347368960000 recorded for the discrete carrier only."

factorVecScopeSummary : String
factorVecScopeSummary =
  "FactorVec records valuations and amplitudes only, not the full continuum phase coordinate."

ymVsNsPhaseSummary : String
ymVsNsPhaseSummary =
  "YM physical Hilbert space quotients gauge phases, making Gate3 phase handling easier; NS has no analogous gauge quotient here, so missing high-prime phases remain physical."

promotionBoundarySummary : String
promotionBoundarySummary =
  "No Gate3 theorem, Yang-Baxter theorem, KP theorem, Yang-Mills Clay promotion, Navier-Stokes Clay promotion, or terminal Clay claim is promoted by this receipt."

carrierGribovBoundarySummary : String
carrierGribovBoundarySummary =
  "Carrier gauge fixing is discrete-only; no continuum Gribov-free theorem is claimed, and Gate3 continuum gauge fixing remains open."

p7IncommensurabilitySummary : String
p7IncommensurabilitySummary =
  "At p=7 the amplitude residue carrier is Z/7 while the unit/phase group has order 6, so amplitude and unit phase bookkeeping are not the same cyclic sector."

sectorDensitySummary : String
sectorDensitySummary =
  "The receipt distinguishes finite carrier sectors from a countable continuum target; trivial-sector density is not proved, NS phases remain physical, and high-prime phase loss stays open."

braidKPBoundarySummary : String
braidKPBoundarySummary =
  "Finite carrier phase bookkeeping does not imply a Yang-Baxter theorem or KP theorem."

discourseSemanticsSummary : String
discourseSemanticsSummary =
  "Discourse semantics are recorded as carrier bookkeeping: 3^2 names two ternary positions, while 3^3 names dialogue through time/synthesis; no semantic completeness theorem is promoted."

record CarrierPhaseStructureReceipt : Set where
  field
    status :
      CarrierPhaseStructureStatus

    statusIsSafe :
      status ≡ safeFiniteSSPUnitProductConceptRecordedNoPromotion

    safeStatus :
      SafeStatus

    safeStatusIsFailClosed :
      safeStatus ≡ failClosed

    sspPrimeList :
      List Nat

    sspPrimeListIsCanonical :
      sspPrimeList ≡ SSP.canonicalSupersingularPrimeLaneNats

    sspPrimeCount :
      Nat

    sspPrimeCountIsFifteen :
      sspPrimeCount ≡ 15

    localUnitGroupConcepts :
      List LocalUnitGroupConcept

    localUnitGroupConceptsAreCanonical :
      localUnitGroupConcepts ≡ canonicalLocalUnitGroupConcepts

    carrierPhaseGroupConcept :
      CarrierPhaseGroupConcept

    carrierPhaseGroupConceptIsFiniteSSPProduct :
      carrierPhaseGroupConcept ≡ finiteProductOfLocalUnitGroupsOverSSP

    carrierGribovBoundaryStatus :
      CarrierGribovBoundaryStatus

    carrierGribovBoundaryStatusIsDiscreteOnly :
      carrierGribovBoundaryStatus
      ≡ discreteCarrierGaugeFixOnlyGate3ContinuumOpen

    discreteCarrierGaugeFixClaimOnly :
      Bool

    discreteCarrierGaugeFixClaimOnlyIsTrue :
      discreteCarrierGaugeFixClaimOnly ≡ true

    continuumGribovFreeClaimed :
      Bool

    continuumGribovFreeClaimedIsFalse :
      continuumGribovFreeClaimed ≡ false

    gate3ContinuumGaugeFixOpen :
      Bool

    gate3ContinuumGaugeFixOpenIsTrue :
      gate3ContinuumGaugeFixOpen ≡ true

    phaseGroupOrderStatus :
      PhaseGroupOrderStatus

    phaseGroupOrderStatusIsExactFinite :
      phaseGroupOrderStatus ≡ exactFiniteSSPUnitProductOrderRecorded

    exactProductOrderComputed :
      Bool

    exactProductOrderComputedIsTrue :
      exactProductOrderComputed ≡ true

    productOrderArithmeticAsserted :
      Bool

    productOrderArithmeticAssertedIsTrue :
      productOrderArithmeticAsserted ≡ true

    exactSSPUnitProductOrder :
      Nat

    exactSSPUnitProductOrderIsCanonical :
      exactSSPUnitProductOrder ≡ 229013347368960000

    p2UnitOrder :
      Nat

    p2UnitOrderIsOne :
      p2UnitOrder ≡ 1

    p7AmplitudeUnitPhaseStatus :
      P7AmplitudeUnitPhaseStatus

    p7AmplitudeUnitPhaseStatusIsIncommensurable :
      p7AmplitudeUnitPhaseStatus
      ≡ p7AmplitudeZ7UnitPhaseZ6Incommensurable

    p7AmplitudeResidueOrder :
      Nat

    p7AmplitudeResidueOrderIsSeven :
      p7AmplitudeResidueOrder ≡ 7

    p7UnitPhaseOrder :
      Nat

    p7UnitPhaseOrderIsSix :
      p7UnitPhaseOrder ≡ 6

    p7AmplitudeUnitPhaseIncommensurable :
      Bool

    p7AmplitudeUnitPhaseIncommensurableIsTrue :
      p7AmplitudeUnitPhaseIncommensurable ≡ true

    factorVecPhaseScope :
      FactorVecPhaseScope

    factorVecPhaseScopeIsValuationAmplitudeOnly :
      factorVecPhaseScope ≡ valuationsAndAmplitudesOnly

    factorVecCarriesFullContinuumPhase :
      Bool

    factorVecCarriesFullContinuumPhaseIsFalse :
      factorVecCarriesFullContinuumPhase ≡ false

    ymPhaseQuotientStatus :
      YMPhaseQuotientStatus

    ymPhaseQuotientStatusIsGaugeQuotient :
      ymPhaseQuotientStatus
      ≡ gaugePhasesQuotientedInPhysicalHilbertSpace

    ymGate3PhaseHandlingEasier :
      Bool

    ymGate3PhaseHandlingEasierIsTrue :
      ymGate3PhaseHandlingEasier ≡ true

    nsPhaseQuotientStatus :
      NSPhaseQuotientStatus

    nsPhaseQuotientStatusIsNoAnalogousQuotient :
      nsPhaseQuotientStatus
      ≡ noAnalogousGaugeQuotientHighPrimePhasesPhysical

    nsHasAnalogousGaugeQuotient :
      Bool

    nsHasAnalogousGaugeQuotientIsFalse :
      nsHasAnalogousGaugeQuotient ≡ false

    missingHighPrimeNSPhasesRemainPhysical :
      Bool

    missingHighPrimeNSPhasesRemainPhysicalIsTrue :
      missingHighPrimeNSPhasesRemainPhysical ≡ true

    carrierSectorDensityStatus :
      CarrierSectorDensityStatus

    carrierSectorDensityStatusIsOpen :
      carrierSectorDensityStatus
      ≡ finiteCarrierVsCountableContinuumDensityOpen

    finiteCarrierSectorsRecorded :
      Bool

    finiteCarrierSectorsRecordedIsTrue :
      finiteCarrierSectorsRecorded ≡ true

    countableContinuumTargetRecorded :
      Bool

    countableContinuumTargetRecordedIsTrue :
      countableContinuumTargetRecorded ≡ true

    trivialSectorDensityStatus :
      TrivialSectorDensityStatus

    trivialSectorDensityStatusIsOpen :
      trivialSectorDensityStatus
      ≡ trivialSectorDensityNotProvedNSPhysicalHighPrimeLoss

    trivialSectorDenseClaimed :
      Bool

    trivialSectorDenseClaimedIsFalse :
      trivialSectorDenseClaimed ≡ false

    trivialSectorDensityOpen :
      Bool

    trivialSectorDensityOpenIsTrue :
      trivialSectorDensityOpen ≡ true

    highPrimePhaseLossOpen :
      Bool

    highPrimePhaseLossOpenIsTrue :
      highPrimePhaseLossOpen ≡ true

    braidKPBoundaryStatus :
      BraidKPBoundaryStatus

    braidKPBoundaryStatusIsNoTheorem :
      braidKPBoundaryStatus ≡ noYangBaxterOrKPTheoremFromPhaseCarrier

    discourseSemanticsStatus :
      DiscourseSemanticsStatus

    discourseSemanticsStatusIsBookkeepingOnly :
      discourseSemanticsStatus
      ≡ discourseSemanticsRecordedAsCarrierBookkeepingOnly

    discourseAritySemantics :
      List DiscourseAritySemantics

    discourseAritySemanticsAreCanonical :
      discourseAritySemantics ≡ canonicalDiscourseAritySemantics

    ternarySquareTwoPositionsRecorded :
      Bool

    ternarySquareTwoPositionsRecordedIsTrue :
      ternarySquareTwoPositionsRecorded ≡ true

    ternaryCubeDialogueSynthesisRecorded :
      Bool

    ternaryCubeDialogueSynthesisRecordedIsTrue :
      ternaryCubeDialogueSynthesisRecorded ≡ true

    discourseCompletenessTheoremPromoted :
      Bool

    discourseCompletenessTheoremPromotedIsFalse :
      discourseCompletenessTheoremPromoted ≡ false

    yangBaxterTheoremPromoted :
      Bool

    yangBaxterTheoremPromotedIsFalse :
      yangBaxterTheoremPromoted ≡ false

    kpTheoremPromoted :
      Bool

    kpTheoremPromotedIsFalse :
      kpTheoremPromoted ≡ false

    openCarrierPhaseObligations :
      List OpenCarrierPhaseObligation

    openCarrierPhaseObligationsAreCanonical :
      openCarrierPhaseObligations ≡ canonicalOpenCarrierPhaseObligations

    gate3Promoted :
      Bool

    gate3PromotedIsFalse :
      gate3Promoted ≡ false

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    terminalClayClaimPromoted :
      Bool

    terminalClayClaimPromotedIsFalse :
      terminalClayClaimPromoted ≡ false

    noGate3PromotionWithoutAuthority :
      Gate3Promotion →
      ⊥

    noClayPromotionWithoutAuthority :
      ClayPromotion →
      ⊥

    conceptSummary :
      String

    conceptSummaryIsCanonical :
      conceptSummary ≡ carrierPhaseConceptSummary

    factorVecSummary :
      String

    factorVecSummaryIsCanonical :
      factorVecSummary ≡ factorVecScopeSummary

    ymNsPhaseSummary :
      String

    ymNsPhaseSummaryIsCanonical :
      ymNsPhaseSummary ≡ ymVsNsPhaseSummary

    promotionBoundary :
      String

    promotionBoundaryIsCanonical :
      promotionBoundary ≡ promotionBoundarySummary

    gribovBoundary :
      String

    gribovBoundaryIsCanonical :
      gribovBoundary ≡ carrierGribovBoundarySummary

    p7PhaseBoundary :
      String

    p7PhaseBoundaryIsCanonical :
      p7PhaseBoundary ≡ p7IncommensurabilitySummary

    densityBoundary :
      String

    densityBoundaryIsCanonical :
      densityBoundary ≡ sectorDensitySummary

    braidKPBoundary :
      String

    braidKPBoundaryIsCanonical :
      braidKPBoundary ≡ braidKPBoundarySummary

    discourseSemanticsBoundary :
      String

    discourseSemanticsBoundaryIsCanonical :
      discourseSemanticsBoundary ≡ discourseSemanticsSummary

    receiptBoundary :
      List String

open CarrierPhaseStructureReceipt public

canonicalCarrierPhaseStructureReceipt :
  CarrierPhaseStructureReceipt
canonicalCarrierPhaseStructureReceipt =
  record
    { status =
        safeFiniteSSPUnitProductConceptRecordedNoPromotion
    ; statusIsSafe =
        refl
    ; safeStatus =
        failClosed
    ; safeStatusIsFailClosed =
        refl
    ; sspPrimeList =
        SSP.canonicalSupersingularPrimeLaneNats
    ; sspPrimeListIsCanonical =
        refl
    ; sspPrimeCount =
        15
    ; sspPrimeCountIsFifteen =
        refl
    ; localUnitGroupConcepts =
        canonicalLocalUnitGroupConcepts
    ; localUnitGroupConceptsAreCanonical =
        refl
    ; carrierPhaseGroupConcept =
        finiteProductOfLocalUnitGroupsOverSSP
    ; carrierPhaseGroupConceptIsFiniteSSPProduct =
        refl
    ; carrierGribovBoundaryStatus =
        discreteCarrierGaugeFixOnlyGate3ContinuumOpen
    ; carrierGribovBoundaryStatusIsDiscreteOnly =
        refl
    ; discreteCarrierGaugeFixClaimOnly =
        true
    ; discreteCarrierGaugeFixClaimOnlyIsTrue =
        refl
    ; continuumGribovFreeClaimed =
        false
    ; continuumGribovFreeClaimedIsFalse =
        refl
    ; gate3ContinuumGaugeFixOpen =
        true
    ; gate3ContinuumGaugeFixOpenIsTrue =
        refl
    ; phaseGroupOrderStatus =
        exactFiniteSSPUnitProductOrderRecorded
    ; phaseGroupOrderStatusIsExactFinite =
        refl
    ; exactProductOrderComputed =
        true
    ; exactProductOrderComputedIsTrue =
        refl
    ; productOrderArithmeticAsserted =
        true
    ; productOrderArithmeticAssertedIsTrue =
        refl
    ; exactSSPUnitProductOrder =
        229013347368960000
    ; exactSSPUnitProductOrderIsCanonical =
        refl
    ; p2UnitOrder =
        1
    ; p2UnitOrderIsOne =
        refl
    ; p7AmplitudeUnitPhaseStatus =
        p7AmplitudeZ7UnitPhaseZ6Incommensurable
    ; p7AmplitudeUnitPhaseStatusIsIncommensurable =
        refl
    ; p7AmplitudeResidueOrder =
        7
    ; p7AmplitudeResidueOrderIsSeven =
        refl
    ; p7UnitPhaseOrder =
        6
    ; p7UnitPhaseOrderIsSix =
        refl
    ; p7AmplitudeUnitPhaseIncommensurable =
        true
    ; p7AmplitudeUnitPhaseIncommensurableIsTrue =
        refl
    ; factorVecPhaseScope =
        valuationsAndAmplitudesOnly
    ; factorVecPhaseScopeIsValuationAmplitudeOnly =
        refl
    ; factorVecCarriesFullContinuumPhase =
        false
    ; factorVecCarriesFullContinuumPhaseIsFalse =
        refl
    ; ymPhaseQuotientStatus =
        gaugePhasesQuotientedInPhysicalHilbertSpace
    ; ymPhaseQuotientStatusIsGaugeQuotient =
        refl
    ; ymGate3PhaseHandlingEasier =
        true
    ; ymGate3PhaseHandlingEasierIsTrue =
        refl
    ; nsPhaseQuotientStatus =
        noAnalogousGaugeQuotientHighPrimePhasesPhysical
    ; nsPhaseQuotientStatusIsNoAnalogousQuotient =
        refl
    ; nsHasAnalogousGaugeQuotient =
        false
    ; nsHasAnalogousGaugeQuotientIsFalse =
        refl
    ; missingHighPrimeNSPhasesRemainPhysical =
        true
    ; missingHighPrimeNSPhasesRemainPhysicalIsTrue =
        refl
    ; carrierSectorDensityStatus =
        finiteCarrierVsCountableContinuumDensityOpen
    ; carrierSectorDensityStatusIsOpen =
        refl
    ; finiteCarrierSectorsRecorded =
        true
    ; finiteCarrierSectorsRecordedIsTrue =
        refl
    ; countableContinuumTargetRecorded =
        true
    ; countableContinuumTargetRecordedIsTrue =
        refl
    ; trivialSectorDensityStatus =
        trivialSectorDensityNotProvedNSPhysicalHighPrimeLoss
    ; trivialSectorDensityStatusIsOpen =
        refl
    ; trivialSectorDenseClaimed =
        false
    ; trivialSectorDenseClaimedIsFalse =
        refl
    ; trivialSectorDensityOpen =
        true
    ; trivialSectorDensityOpenIsTrue =
        refl
    ; highPrimePhaseLossOpen =
        true
    ; highPrimePhaseLossOpenIsTrue =
        refl
    ; braidKPBoundaryStatus =
        noYangBaxterOrKPTheoremFromPhaseCarrier
    ; braidKPBoundaryStatusIsNoTheorem =
        refl
    ; discourseSemanticsStatus =
        discourseSemanticsRecordedAsCarrierBookkeepingOnly
    ; discourseSemanticsStatusIsBookkeepingOnly =
        refl
    ; discourseAritySemantics =
        canonicalDiscourseAritySemantics
    ; discourseAritySemanticsAreCanonical =
        refl
    ; ternarySquareTwoPositionsRecorded =
        true
    ; ternarySquareTwoPositionsRecordedIsTrue =
        refl
    ; ternaryCubeDialogueSynthesisRecorded =
        true
    ; ternaryCubeDialogueSynthesisRecordedIsTrue =
        refl
    ; discourseCompletenessTheoremPromoted =
        false
    ; discourseCompletenessTheoremPromotedIsFalse =
        refl
    ; yangBaxterTheoremPromoted =
        false
    ; yangBaxterTheoremPromotedIsFalse =
        refl
    ; kpTheoremPromoted =
        false
    ; kpTheoremPromotedIsFalse =
        refl
    ; openCarrierPhaseObligations =
        canonicalOpenCarrierPhaseObligations
    ; openCarrierPhaseObligationsAreCanonical =
        refl
    ; gate3Promoted =
        false
    ; gate3PromotedIsFalse =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; terminalClayClaimPromoted =
        false
    ; terminalClayClaimPromotedIsFalse =
        refl
    ; noGate3PromotionWithoutAuthority =
        gate3PromotionImpossibleHere
    ; noClayPromotionWithoutAuthority =
        clayPromotionImpossibleHere
    ; conceptSummary =
        carrierPhaseConceptSummary
    ; conceptSummaryIsCanonical =
        refl
    ; factorVecSummary =
        factorVecScopeSummary
    ; factorVecSummaryIsCanonical =
        refl
    ; ymNsPhaseSummary =
        ymVsNsPhaseSummary
    ; ymNsPhaseSummaryIsCanonical =
        refl
    ; promotionBoundary =
        promotionBoundarySummary
    ; promotionBoundaryIsCanonical =
        refl
    ; gribovBoundary =
        carrierGribovBoundarySummary
    ; gribovBoundaryIsCanonical =
        refl
    ; p7PhaseBoundary =
        p7IncommensurabilitySummary
    ; p7PhaseBoundaryIsCanonical =
        refl
    ; densityBoundary =
        sectorDensitySummary
    ; densityBoundaryIsCanonical =
        refl
    ; braidKPBoundary =
        braidKPBoundarySummary
    ; braidKPBoundaryIsCanonical =
        refl
    ; discourseSemanticsBoundary =
        discourseSemanticsSummary
    ; discourseSemanticsBoundaryIsCanonical =
        refl
    ; receiptBoundary =
        "Canonical SSP prime list is recorded with count 15."
        ∷ "Carrier phases are finite local-unit factors (Z/pZ)^* with exact product order 229013347368960000."
        ∷ "The p=2 unit group has order 1."
        ∷ "The p=7 amplitude residue Z/7 and unit/phase order 6 are recorded as incommensurable bookkeeping surfaces."
        ∷ "FactorVec is valuation/amplitude data and does not encode the full continuum phase."
        ∷ "Carrier gauge fixing is discrete-only; Gate3 continuum gauge fixing and continuum Gribov-freeness remain open."
        ∷ "Finite carrier sectors are distinguished from the countable continuum target; trivial-sector density is open."
        ∷ "YM quotients gauge phases in the physical Hilbert space; NS does not receive that quotient here."
        ∷ "NS phases remain physical and high-prime phase loss remains open."
        ∷ "Discourse arities are bookkeeping only: 3^2 records two positions and 3^3 records dialogue through time/synthesis."
        ∷ "No discourse semantic completeness theorem is promoted."
        ∷ "Finite carrier phase bookkeeping does not promote a Yang-Baxter theorem or KP theorem."
        ∷ "Gate3 and both Clay promotions remain false."
        ∷ []
    }

carrierPhaseReceiptIsFailClosed :
  safeStatus canonicalCarrierPhaseStructureReceipt ≡ failClosed
carrierPhaseReceiptIsFailClosed =
  refl

carrierPhaseReceiptRecordsFifteenSSPPrimes :
  sspPrimeCount canonicalCarrierPhaseStructureReceipt ≡ 15
carrierPhaseReceiptRecordsFifteenSSPPrimes =
  refl

carrierPhaseReceiptNoGate3Promotion :
  gate3Promoted canonicalCarrierPhaseStructureReceipt ≡ false
carrierPhaseReceiptNoGate3Promotion =
  refl

carrierPhaseReceiptNoClayPromotion :
  terminalClayClaimPromoted canonicalCarrierPhaseStructureReceipt ≡ false
carrierPhaseReceiptNoClayPromotion =
  refl

carrierPhaseReceiptExactProductOrder :
  exactSSPUnitProductOrder canonicalCarrierPhaseStructureReceipt
  ≡ 229013347368960000
carrierPhaseReceiptExactProductOrder =
  refl

carrierPhaseReceiptP2UnitOrderOne :
  p2UnitOrder canonicalCarrierPhaseStructureReceipt ≡ 1
carrierPhaseReceiptP2UnitOrderOne =
  refl

carrierPhaseReceiptGate3ContinuumGaugeFixOpen :
  gate3ContinuumGaugeFixOpen canonicalCarrierPhaseStructureReceipt ≡ true
carrierPhaseReceiptGate3ContinuumGaugeFixOpen =
  refl

carrierPhaseReceiptTrivialSectorDensityOpen :
  trivialSectorDensityOpen canonicalCarrierPhaseStructureReceipt ≡ true
carrierPhaseReceiptTrivialSectorDensityOpen =
  refl

carrierPhaseReceiptNoYangBaxterPromotion :
  yangBaxterTheoremPromoted canonicalCarrierPhaseStructureReceipt ≡ false
carrierPhaseReceiptNoYangBaxterPromotion =
  refl

carrierPhaseReceiptNoKPPromotion :
  kpTheoremPromoted canonicalCarrierPhaseStructureReceipt ≡ false
carrierPhaseReceiptNoKPPromotion =
  refl

carrierPhaseReceiptNoDiscourseCompletenessPromotion :
  discourseCompletenessTheoremPromoted canonicalCarrierPhaseStructureReceipt
  ≡ false
carrierPhaseReceiptNoDiscourseCompletenessPromotion =
  refl
