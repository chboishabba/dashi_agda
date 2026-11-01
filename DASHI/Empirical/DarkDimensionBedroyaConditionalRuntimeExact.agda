module DASHI.Empirical.DarkDimensionBedroyaConditionalRuntimeExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.ProofDebtRouterExact as ProofDebt
import DASHI.Empirical.DarkDimensionBedroyaBackgroundInputContractExact as Input
import DASHI.Empirical.DarkDimensionSharedBAOObservationKeyExact as ObservationKey

------------------------------------------------------------------------
-- CONDITIONAL BEDROYA BACKGROUND / BAO RUNTIME SURFACE
--
-- This is an input and receipt contract, not a numerical solver.  It permits
-- downstream runtime implementation only after the complete source-bound input
-- object is supplied.  BAO normalization is a second stage requiring the
-- same-fit baryon drag horizon in addition to an actual background-vector
-- receipt.  No default numerical values are manufactured here.
------------------------------------------------------------------------

record CompleteBedroyaBackgroundInput : Set where
  constructor completeBedroyaBackgroundInput
  field
    h0Input : String
    omegaR0Input : String
    omegaB0Input : String
    sampledDMNormalizationInput : String
    v0NormalizationInput : String
    initialScalarVelocityInput : String
    inputProvenanceReference : String

open CompleteBedroyaBackgroundInput public

record BedroyaBAONormalizationInput : Set where
  constructor bedroyaBAONormalizationInput
  field
    sameFitRDragInput : String
    rDragProvenanceReference : String

open BedroyaBAONormalizationInput public

record BedroyaBackgroundVectorRequest : Set where
  constructor bedroyaBackgroundVectorRequest
  field
    lrg1RedshiftMilli : String
    lrg2RedshiftMilli : String
    lrg3Elg1RedshiftMilli : String
    elg2RedshiftMilli : String
    qsoRedshiftMilli : String
    lyaRedshiftMilli : String
    sixObservationRedshiftsPinned : Bool
    requestReference : String

open BedroyaBackgroundVectorRequest public

canonicalBedroyaBackgroundVectorRequest : BedroyaBackgroundVectorRequest
canonicalBedroyaBackgroundVectorRequest =
  bedroyaBackgroundVectorRequest
    "510" "706" "934" "1321" "1484" "2330"
    true
    "DESI DR2 six-anisotropic-bin Bedroya background-vector request"

record BedroyaBackgroundVectorReceipt : Set where
  constructor bedroyaBackgroundVectorReceipt
  field
    hVectorPresent : Bool
    dmVectorPresent : Bool
    dhVectorPresent : Bool
    runtimeExecutionReference : String
    inputIdentityReference : String

open BedroyaBackgroundVectorReceipt public

-- The conditional development exposes the implementation boundary without
-- pretending that the repository already contains a numerical ODE backend.
-- A supplied complete input object is necessary to construct even the pending
-- runtime request receipt; vector-presence flags remain false until execution.
runBedroyaBackgroundConditionally :
  BedroyaBackgroundVectorRequest →
  ProofDebt.ConditionalDevelopment
    CompleteBedroyaBackgroundInput
    BedroyaBackgroundVectorReceipt
runBedroyaBackgroundConditionally request input =
  bedroyaBackgroundVectorReceipt
    false false false
    "conditional Bedroya background runtime requested; numerical execution receipt not present"
    (inputProvenanceReference input)

canonicalConditionalBackgroundReceipt :
  ProofDebt.ConditionalDevelopment
    CompleteBedroyaBackgroundInput
    BedroyaBackgroundVectorReceipt
canonicalConditionalBackgroundReceipt =
  runBedroyaBackgroundConditionally canonicalBedroyaBackgroundVectorRequest

record BackgroundVectorAvailable (receipt : BedroyaBackgroundVectorReceipt) : Set where
  constructor backgroundVectorAvailable
  field
    hPaid : hVectorPresent receipt ≡ true
    dmPaid : dmVectorPresent receipt ≡ true
    dhPaid : dhVectorPresent receipt ≡ true

open BackgroundVectorAvailable public

record BedroyaSameKeyBAOReceipt : Set where
  constructor bedroyaSameKeyBAOReceipt
  field
    baoRatiosPresent : Bool
    backgroundReceiptReference : String
    rDragReceiptReference : String

open BedroyaSameKeyBAOReceipt public

-- BAO promotion requires a genuinely executed background-vector receipt and
-- a separately source-bound r_drag input.  The existence of the schema alone
-- does not create either witness.
normalizeBackgroundToBAO :
  (background : BedroyaBackgroundVectorReceipt) →
  BackgroundVectorAvailable background →
  BedroyaBAONormalizationInput →
  BedroyaSameKeyBAOReceipt
normalizeBackgroundToBAO background available rdrag =
  bedroyaSameKeyBAOReceipt
    true
    (runtimeExecutionReference background)
    (rDragProvenanceReference rdrag)

------------------------------------------------------------------------
-- Fail-closed boundaries.
------------------------------------------------------------------------

data NoCompleteInputMeansNoRuntimeReceipt : Set where

data BackgroundReceiptWithoutRDragPaysBAORatios : Set where

noCompleteInputDoesNotManufactureRuntimeReceipt :
  NoCompleteInputMeansNoRuntimeReceipt → ⊥
noCompleteInputDoesNotManufactureRuntimeReceipt ()

backgroundReceiptDoesNotPayBAOWithoutRDrag :
  BackgroundReceiptWithoutRDragPaysBAORatios → ⊥
backgroundReceiptDoesNotPayBAOWithoutRDrag ()

canonicalRuntimeRequestStillBlocked :
  Input.completeBackgroundInputManifestLocated
    Input.canonicalBedroyaBackgroundInputStatus
  ≡ false
canonicalRuntimeRequestStillBlocked = Input.completeBackgroundInputStillOpen

canonicalBAONormalizationStillBlocked :
  Input.exactRDragSameFitLocated
    Input.canonicalBedroyaBackgroundInputStatus
  ≡ false
canonicalBAONormalizationStillBlocked = Input.exactRDragSameFitStillOpen

-- Key ownership remains external and source-pinned rather than being silently
-- recreated by the runtime schema.
lrg1KeyRemainsPinned : ObservationKey.redshiftMilli ObservationKey.lrg1TransverseKey ≡ 510
lrg1KeyRemainsPinned = refl
