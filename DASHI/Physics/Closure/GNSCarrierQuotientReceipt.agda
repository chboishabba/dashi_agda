module DASHI.Physics.Closure.GNSCarrierQuotientReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.AQFTNetReceipt as AQFTNet
import DASHI.Physics.QFT.AQFTTypedNetSurface as AQFT
import DASHI.Physics.QFT.AQFTCarrierAlgebraQuotientSurface as L5
import DASHI.Physics.QFT.GNSFellRepresentationSurface as GNSFell
import DASHI.Physics.QFT.ModularTheoryReceiptSurface as Modular

------------------------------------------------------------------------
-- GNS carrier quotient receipt.
--
-- This receipt records the local algebra carrier route needed before a
-- real GNS Hilbert space may be promoted:
--
--   * filtered-colimit local algebra target,
--   * vacuum projection/state-functional target,
--   * null ideal and quotient inner product targets,
--   * GNS/Fell and finite-trace descent receipts already present in Gate 5.
--
-- It deliberately keeps GNSHilbertSpaceConstructed false until the
-- filtered-colimit local algebra is supplied as an inhabited carrier.  The
-- modular and Fell receipts are consumed as non-promoting authority.

data GNSCarrierQuotientStatus : Set where
  gnsCarrierQuotientRecordedFailClosed :
    GNSCarrierQuotientStatus

data GNSCarrierQuotientBlocker : Set where
  missingFilteredColimitLocalAlgebraInhabitant :
    GNSCarrierQuotientBlocker

  missingVacuumProjectionFunctionalConstruction :
    GNSCarrierQuotientBlocker

  missingQuotientInnerProductWellDefinednessTheorem :
    GNSCarrierQuotientBlocker

  missingNullIdealLeftIdealClosureTheorem :
    GNSCarrierQuotientBlocker

  missingGNSCompletionHilbertSpaceFromColimit :
    GNSCarrierQuotientBlocker

  missingGNSFellUniversalProperty :
    GNSCarrierQuotientBlocker

canonicalGNSCarrierQuotientBlockers :
  List GNSCarrierQuotientBlocker
canonicalGNSCarrierQuotientBlockers =
  missingFilteredColimitLocalAlgebraInhabitant
  ∷ missingVacuumProjectionFunctionalConstruction
  ∷ missingQuotientInnerProductWellDefinednessTheorem
  ∷ missingNullIdealLeftIdealClosureTheorem
  ∷ missingGNSCompletionHilbertSpaceFromColimit
  ∷ missingGNSFellUniversalProperty
  ∷ []

data GNSHilbertSpaceConstructionAuthorityToken : Set where

record GNSCarrierQuotientReceipt : Setω where
  field
    status :
      GNSCarrierQuotientStatus

    aqftNetReceipt :
      AQFTNet.AQFTNetReceipt

    aqftNetGNSVacuumAdapterStillOpen :
      AQFTNet.AQFTNetReceipt.gnsVacuumAdapterStillOpen aqftNetReceipt
      ≡
      true

    depthFilteredLocalAlgebraSurface :
      L5.DepthFilteredLocalAlgebraSurface

    l3FilteredColimitAttempt :
      L5.AQFTL3FilteredColimitPreservationAttemptSurface

    filteredColimitLocalAlgebraTarget :
      AQFT.Region →
      Set

    filteredColimitLocalAlgebraTargetMatchesDepthSurface :
      (region : AQFT.Region) →
      filteredColimitLocalAlgebraTarget region
      ≡
      L5.DepthFilteredLocalAlgebraSurface.A_colim
        depthFilteredLocalAlgebraSurface
        region

    filteredColimitPreservationShapeThreaded :
      L5.AQFTL3FilteredColimitPreservationAttemptSurface.filteredColimitShapeThreaded
        l3FilteredColimitAttempt
      ≡
      true

    filteredColimitPreservationProved :
      L5.AQFTL3FilteredColimitPreservationAttemptSurface.filteredColimitPreservationProved
        l3FilteredColimitAttempt
      ≡
      false

    vacuumProjectionFunctionalTarget :
      Modular.StateFunctional Modular.abstractRegion

    vacuumProjectionFunctionalMatchesModularState :
      vacuumProjectionFunctionalTarget
      ≡
      Modular.abstractStateFunctional

    vacuumProjectionFunctionalConstructedFromColimit :
      Bool

    vacuumProjectionFunctionalConstructedFromColimitIsFalse :
      vacuumProjectionFunctionalConstructedFromColimit ≡ false

    nullIdealTarget :
      Modular.GNSNullIdeal
        Modular.abstractRegion
        Modular.abstractStateFunctional

    nullIdealTargetMatchesModular :
      nullIdealTarget
      ≡
      Modular.abstractGNSNullIdeal

    quotientCarrierTarget :
      Modular.GNSPreHilbertQuotient
        Modular.abstractRegion
        Modular.abstractStateFunctional
        Modular.abstractGNSNullIdeal

    quotientCarrierTargetMatchesModular :
      quotientCarrierTarget
      ≡
      Modular.abstractGNSPreHilbertQuotient

    modularNullIdealReceipt :
      Modular.GNSNullIdealPreHilbertQuotientReceipt
        Modular.abstractRegion
        Modular.abstractStateFunctional

    modularNullIdealReceiptInhabited :
      Modular.GNSNullIdealPreHilbertQuotientReceipt.quotientCurrentlyInhabitedAsReceipt
        modularNullIdealReceipt
      ≡
      true

    modularQuotientTheoremPromoted :
      Modular.GNSNullIdealPreHilbertQuotientReceipt.quotientTheoremPromoted
        modularNullIdealReceipt
      ≡
      false

    modularInnerProductWellDefinedness :
      Modular.M4GNSInnerProductNullIdealWellDefinednessReceipt

    nullIdealLeftIdealTargetThreaded :
      Modular.M4GNSNullIdealPreHilbertHilbertBridgeReceipt.nullIdealLeftIdealTargetThreaded
        (Modular.M4GNSInnerProductNullIdealWellDefinednessReceipt.nullIdealHilbertBridge
          modularInnerProductWellDefinedness)
      ≡
      true

    innerProductDescendsTargetThreaded :
      Modular.M4GNSNullIdealPreHilbertHilbertBridgeReceipt.innerProductDescendsTargetThreaded
        (Modular.M4GNSInnerProductNullIdealWellDefinednessReceipt.nullIdealHilbertBridge
          modularInnerProductWellDefinedness)
      ≡
      true

    modularWellDefinednessPromoted :
      Modular.M4GNSInnerProductNullIdealWellDefinednessReceipt.wellDefinednessPromoted
        modularInnerProductWellDefinedness
      ≡
      false

    gnsFellRepresentationSurface :
      GNSFell.GNSFellRepresentationSurface

    gnsFellPromoted :
      GNSFell.GNSFellRepresentationSurface.gnsFellPromoted
        gnsFellRepresentationSurface
      ≡
      false

    gnsQuotientInnerProductDescent :
      GNSFell.GNSFellL5M4QuotientInnerProductDescentCurrentWaveReceipt

    gnsQuotientRelationAdvanced :
      GNSFell.GNSFellL5M4QuotientInnerProductDescentCurrentWaveReceipt.fellQuotientRelationAdvanced
        gnsQuotientInnerProductDescent
      ≡
      true

    gnsQuotientNormReceiptOnly :
      GNSFell.GNSFellL5M4QuotientInnerProductDescentCurrentWaveReceipt.fellQuotientNormReceiptOnly
        gnsQuotientInnerProductDescent
      ≡
      true

    gnsQuotientInnerProductPromoted :
      GNSFell.GNSFellL5M4QuotientInnerProductDescentCurrentWaveReceipt.quotientInnerProductWellDefinednessPromoted
        gnsQuotientInnerProductDescent
      ≡
      false

    gnsDescentExactAnalyticBlocker :
      GNSFell.GNSFellL5M4QuotientInnerProductDescentCurrentWaveReceipt.exactAnalyticBlocker
        gnsQuotientInnerProductDescent
      ≡
      "missingStateCauchySchwarzInequalityForParametricPreCStarAlgebra"

    finiteTraceStateDescent :
      GNSFell.GNSFellFiniteTraceStateDescentConsumptionReceipt

    finiteTraceStateAPIAvailable :
      GNSFell.GNSFellFiniteTraceStateDescentConsumptionReceipt.finiteTraceStateAPIAvailable
        finiteTraceStateDescent
      ≡
      true

    finiteTraceQuotientDescentPromoted :
      Modular.M4FiniteTraceStateCauchySchwarzDescentReceipt.quotientInnerProductDescentPromoted
        (GNSFell.GNSFellFiniteTraceStateDescentConsumptionReceipt.modularFiniteTraceDescent
          finiteTraceStateDescent)
      ≡
      false

    aqftGNSStoneClosure :
      L5.L5L6M4U5AQFTGNSStoneLocalAlgebraClosureFailClosedReceipt

    finiteLocalAlgebraClosureRecorded :
      L5.L5L6M4U5AQFTGNSStoneLocalAlgebraClosureFailClosedReceipt.closurePromoted
        aqftGNSStoneClosure
      ≡
      true

    finiteLocalAlgebraDoesNotSupplyContinuumGNSHilbert :
      Bool

    finiteLocalAlgebraDoesNotSupplyContinuumGNSHilbertIsTrue :
      finiteLocalAlgebraDoesNotSupplyContinuumGNSHilbert ≡ true

    filteredColimitLocalAlgebraInhabited :
      Bool

    filteredColimitLocalAlgebraInhabitedIsFalse :
      filteredColimitLocalAlgebraInhabited ≡ false

    GNSHilbertSpaceConstructed :
      Bool

    GNSHilbertSpaceConstructedIsFalse :
      GNSHilbertSpaceConstructed ≡ false

    GNSHilbertSpaceRequiresColimitInhabitant :
      filteredColimitLocalAlgebraInhabited
      ≡
      false
      →
      GNSHilbertSpaceConstructed
      ≡
      false

    firstBlocker :
      GNSCarrierQuotientBlocker

    firstBlockerIsFilteredColimitInhabitant :
      firstBlocker
      ≡
      missingFilteredColimitLocalAlgebraInhabitant

    blockers :
      List GNSCarrierQuotientBlocker

    blockersAreCanonical :
      blockers ≡ canonicalGNSCarrierQuotientBlockers

    noHilbertSpaceConstructionWithoutAuthority :
      GNSHilbertSpaceConstructionAuthorityToken →
      ⊥

    receiptBoundary :
      List String

open GNSCarrierQuotientReceipt public

canonicalGNSCarrierQuotientReceipt :
  GNSCarrierQuotientReceipt
canonicalGNSCarrierQuotientReceipt =
  record
    { status =
        gnsCarrierQuotientRecordedFailClosed
    ; aqftNetReceipt =
        AQFTNet.canonicalAQFTNetReceipt
    ; aqftNetGNSVacuumAdapterStillOpen =
        AQFTNet.AQFTNetReceipt.gnsVacuumAdapterStillOpen-v
          AQFTNet.canonicalAQFTNetReceipt
    ; depthFilteredLocalAlgebraSurface =
        L5.canonicalDepthFilteredLocalAlgebraSurface
    ; l3FilteredColimitAttempt =
        L5.canonicalAQFTL3FilteredColimitPreservationAttemptSurface
    ; filteredColimitLocalAlgebraTarget =
        L5.DepthFilteredLocalAlgebraSurface.A_colim
          L5.canonicalDepthFilteredLocalAlgebraSurface
    ; filteredColimitLocalAlgebraTargetMatchesDepthSurface =
        λ _ →
          refl
    ; filteredColimitPreservationShapeThreaded =
        L5.AQFTL3FilteredColimitPreservationAttemptSurface.filteredColimitShapeThreadedIsTrue
          L5.canonicalAQFTL3FilteredColimitPreservationAttemptSurface
    ; filteredColimitPreservationProved =
        L5.AQFTL3FilteredColimitPreservationAttemptSurface.filteredColimitPreservationProvedIsFalse
          L5.canonicalAQFTL3FilteredColimitPreservationAttemptSurface
    ; vacuumProjectionFunctionalTarget =
        Modular.abstractStateFunctional
    ; vacuumProjectionFunctionalMatchesModularState =
        refl
    ; vacuumProjectionFunctionalConstructedFromColimit =
        false
    ; vacuumProjectionFunctionalConstructedFromColimitIsFalse =
        refl
    ; nullIdealTarget =
        Modular.abstractGNSNullIdeal
    ; nullIdealTargetMatchesModular =
        refl
    ; quotientCarrierTarget =
        Modular.abstractGNSPreHilbertQuotient
    ; quotientCarrierTargetMatchesModular =
        refl
    ; modularNullIdealReceipt =
        Modular.canonicalGNSNullIdealPreHilbertQuotientReceipt
    ; modularNullIdealReceiptInhabited =
        Modular.GNSNullIdealPreHilbertQuotientReceipt.quotientCurrentlyInhabitedAsReceiptIsTrue
          Modular.canonicalGNSNullIdealPreHilbertQuotientReceipt
    ; modularQuotientTheoremPromoted =
        Modular.GNSNullIdealPreHilbertQuotientReceipt.quotientTheoremPromotedIsFalse
          Modular.canonicalGNSNullIdealPreHilbertQuotientReceipt
    ; modularInnerProductWellDefinedness =
        Modular.canonicalM4GNSInnerProductNullIdealWellDefinednessReceipt
    ; nullIdealLeftIdealTargetThreaded =
        Modular.M4GNSInnerProductNullIdealWellDefinednessReceipt.nullIdealLeftIdealThreaded
          Modular.canonicalM4GNSInnerProductNullIdealWellDefinednessReceipt
    ; innerProductDescendsTargetThreaded =
        Modular.M4GNSInnerProductNullIdealWellDefinednessReceipt.innerProductDescendsThreaded
          Modular.canonicalM4GNSInnerProductNullIdealWellDefinednessReceipt
    ; modularWellDefinednessPromoted =
        Modular.M4GNSInnerProductNullIdealWellDefinednessReceipt.wellDefinednessPromotedIsFalse
          Modular.canonicalM4GNSInnerProductNullIdealWellDefinednessReceipt
    ; gnsFellRepresentationSurface =
        GNSFell.canonicalGNSFellRepresentationSurface
    ; gnsFellPromoted =
        GNSFell.GNSFellRepresentationSurface.gnsFellPromotedIsFalse
          GNSFell.canonicalGNSFellRepresentationSurface
    ; gnsQuotientInnerProductDescent =
        GNSFell.canonicalGNSFellL5M4QuotientInnerProductDescentCurrentWaveReceipt
    ; gnsQuotientRelationAdvanced =
        GNSFell.GNSFellL5M4QuotientInnerProductDescentCurrentWaveReceipt.fellQuotientRelationAdvancedIsTrue
          GNSFell.canonicalGNSFellL5M4QuotientInnerProductDescentCurrentWaveReceipt
    ; gnsQuotientNormReceiptOnly =
        GNSFell.GNSFellL5M4QuotientInnerProductDescentCurrentWaveReceipt.fellQuotientNormReceiptOnlyIsTrue
          GNSFell.canonicalGNSFellL5M4QuotientInnerProductDescentCurrentWaveReceipt
    ; gnsQuotientInnerProductPromoted =
        GNSFell.GNSFellL5M4QuotientInnerProductDescentCurrentWaveReceipt.quotientInnerProductWellDefinednessPromotedIsFalse
          GNSFell.canonicalGNSFellL5M4QuotientInnerProductDescentCurrentWaveReceipt
    ; gnsDescentExactAnalyticBlocker =
        GNSFell.GNSFellL5M4QuotientInnerProductDescentCurrentWaveReceipt.exactAnalyticBlocker-v
          GNSFell.canonicalGNSFellL5M4QuotientInnerProductDescentCurrentWaveReceipt
    ; finiteTraceStateDescent =
        GNSFell.canonicalGNSFellFiniteTraceStateDescentConsumptionReceipt
    ; finiteTraceStateAPIAvailable =
        GNSFell.GNSFellFiniteTraceStateDescentConsumptionReceipt.finiteTraceStateAPIAvailableIsTrue
          GNSFell.canonicalGNSFellFiniteTraceStateDescentConsumptionReceipt
    ; finiteTraceQuotientDescentPromoted =
        GNSFell.GNSFellFiniteTraceStateDescentConsumptionReceipt.quotientInnerProductDescentPromoted
          GNSFell.canonicalGNSFellFiniteTraceStateDescentConsumptionReceipt
    ; aqftGNSStoneClosure =
        L5.canonicalL5L6M4U5AQFTGNSStoneLocalAlgebraClosureFailClosedReceipt
    ; finiteLocalAlgebraClosureRecorded =
        L5.L5L6M4U5AQFTGNSStoneLocalAlgebraClosureFailClosedReceipt.closurePromotedIsTrue
          L5.canonicalL5L6M4U5AQFTGNSStoneLocalAlgebraClosureFailClosedReceipt
    ; finiteLocalAlgebraDoesNotSupplyContinuumGNSHilbert =
        true
    ; finiteLocalAlgebraDoesNotSupplyContinuumGNSHilbertIsTrue =
        refl
    ; filteredColimitLocalAlgebraInhabited =
        false
    ; filteredColimitLocalAlgebraInhabitedIsFalse =
        refl
    ; GNSHilbertSpaceConstructed =
        false
    ; GNSHilbertSpaceConstructedIsFalse =
        refl
    ; GNSHilbertSpaceRequiresColimitInhabitant =
        λ _ →
          refl
    ; firstBlocker =
        missingFilteredColimitLocalAlgebraInhabitant
    ; firstBlockerIsFilteredColimitInhabitant =
        refl
    ; blockers =
        canonicalGNSCarrierQuotientBlockers
    ; blockersAreCanonical =
        refl
    ; noHilbertSpaceConstructionWithoutAuthority =
        λ ()
    ; receiptBoundary =
        "GNSCarrierQuotientReceipt records colim_d A_d(O) as the local algebra carrier target from AQFTCarrierAlgebraQuotientSurface"
        ∷ "the vacuum projection functional is only Modular.abstractStateFunctional; AQFTNet still marks the GNS/vacuum adapter open"
        ∷ "the null ideal N_phi, quotient A/N_phi, and inner-product descent target are consumed from ModularTheoryReceiptSurface"
        ∷ "GNS/Fell quotient descent and finite-trace receipts are consumed as non-promoting authority"
        ∷ "the finite local-algebra closure receipt is acknowledged, but it does not supply the continuum GNS Hilbert carrier here"
        ∷ "GNSHilbertSpaceConstructed is fixed false until a filtered-colimit local-algebra inhabitant is supplied"
        ∷ []
    }

gnsCarrierQuotientKeepsHilbertFalse :
  GNSHilbertSpaceConstructed canonicalGNSCarrierQuotientReceipt
  ≡
  false
gnsCarrierQuotientKeepsHilbertFalse =
  GNSHilbertSpaceConstructedIsFalse canonicalGNSCarrierQuotientReceipt

gnsCarrierQuotientColimitStillUninhabited :
  filteredColimitLocalAlgebraInhabited canonicalGNSCarrierQuotientReceipt
  ≡
  false
gnsCarrierQuotientColimitStillUninhabited =
  filteredColimitLocalAlgebraInhabitedIsFalse canonicalGNSCarrierQuotientReceipt

gnsCarrierQuotientConsumesQuotientDescent :
  GNSFell.GNSFellL5M4QuotientInnerProductDescentCurrentWaveReceipt.fellQuotientRelationAdvanced
    (gnsQuotientInnerProductDescent canonicalGNSCarrierQuotientReceipt)
  ≡
  true
gnsCarrierQuotientConsumesQuotientDescent =
  gnsQuotientRelationAdvanced canonicalGNSCarrierQuotientReceipt

gnsCarrierQuotientKeepsInnerProductFailClosed :
  GNSFell.GNSFellL5M4QuotientInnerProductDescentCurrentWaveReceipt.quotientInnerProductWellDefinednessPromoted
    (gnsQuotientInnerProductDescent canonicalGNSCarrierQuotientReceipt)
  ≡
  false
gnsCarrierQuotientKeepsInnerProductFailClosed =
  gnsQuotientInnerProductPromoted canonicalGNSCarrierQuotientReceipt

gnsCarrierQuotientFirstBlocker :
  firstBlocker canonicalGNSCarrierQuotientReceipt
  ≡
  missingFilteredColimitLocalAlgebraInhabitant
gnsCarrierQuotientFirstBlocker =
  firstBlockerIsFilteredColimitInhabitant canonicalGNSCarrierQuotientReceipt
