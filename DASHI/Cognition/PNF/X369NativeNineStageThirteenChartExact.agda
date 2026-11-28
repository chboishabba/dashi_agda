module DASHI.Cognition.PNF.X369NativeNineStageThirteenChartExact where

-- Explicit CHOSEN atlas from native nine typed SSP trits into the
-- original actual StageAtlasZeroToEleven plus thirteenth centre.
-- This uses the already existing SSPTrit <-> TriTruth BIDI.
-- It is a coordinate construction, NOT an assertion that arbitrary
-- original neural history already admits this source interpretation.
-- Original Leech-LILA: Anatolii Kornienko; DASHI extension.
-- Kernel deferred.
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
import Base369 as Base
import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Foundations.Base369NineCoordinateAggregateBridgeExact as Nine
import DASHI.Foundations.StageAtlasZeroToEleven as Atlas
import DASHI.Biology.RelationalAppraisalPointedPhaseExact as Rel
import DASHI.Foundations.TernaryThirteenCentralCompletionBundleSheafExact as Sheaf
import DASHI.Foundations.TernaryThirteenPantsSheafGluingTransportExact as Pants13
import DASHI.Foundations.TernaryThirteenOriginalPantsFrontierBridgeExact as Bridge13

-- Last three original stage valuation slots plus the actual
-- thirteenth central value. They are independent source residuals.
record StageFour : Set where
  constructor stageFour
  field
    stage9 : Base.TriTruth
    stage10 : Base.TriTruth
    stage11 : Base.TriTruth
    centre12 : Base.TriTruth
open StageFour public

sourceCentralFromNinePlusFour :
  Nine.NineTrits → StageFour →
  Rel.SourceCentralCompletionCarrier
sourceCentralFromNinePlusFour
  (Nine.nineTrits i0 i1 i2 a0 a1 a2 b0 b1 b2)
  extra = (valuation , centre12 extra)
  where
    valuation : Rel.SourceTwelveAxisValuation
    valuation Atlas.atlas-0 = SSP.toTriTruth i0
    valuation Atlas.atlas-1 = SSP.toTriTruth i1
    valuation Atlas.atlas-2 = SSP.toTriTruth i2
    valuation Atlas.atlas-3 = SSP.toTriTruth a0
    valuation Atlas.atlas-4 = SSP.toTriTruth a1
    valuation Atlas.atlas-5 = SSP.toTriTruth a2
    valuation Atlas.atlas-6 = SSP.toTriTruth b0
    valuation Atlas.atlas-7 = SSP.toTriTruth b1
    valuation Atlas.atlas-8 = SSP.toTriTruth b2
    valuation Atlas.atlas-9 = stage9 extra
    valuation Atlas.atlas-10 = stage10 extra
    valuation Atlas.atlas-11 = stage11 extra

nativeNineFromCentral :
  Rel.SourceCentralCompletionCarrier → Nine.NineTrits
nativeNineFromCentral (valuation , centre) =
  Nine.nineTrits
    (SSP.fromTriTruth (valuation Atlas.atlas-0))
    (SSP.fromTriTruth (valuation Atlas.atlas-1))
    (SSP.fromTriTruth (valuation Atlas.atlas-2))
    (SSP.fromTriTruth (valuation Atlas.atlas-3))
    (SSP.fromTriTruth (valuation Atlas.atlas-4))
    (SSP.fromTriTruth (valuation Atlas.atlas-5))
    (SSP.fromTriTruth (valuation Atlas.atlas-6))
    (SSP.fromTriTruth (valuation Atlas.atlas-7))
    (SSP.fromTriTruth (valuation Atlas.atlas-8))

stageFourFromCentral :
  Rel.SourceCentralCompletionCarrier → StageFour
stageFourFromCentral (valuation , centre) =
  stageFour (valuation Atlas.atlas-9)
            (valuation Atlas.atlas-10)
            (valuation Atlas.atlas-11)
            centre

nineBidi : (n : Nine.NineTrits) (extra : StageFour) →
  nativeNineFromCentral (sourceCentralFromNinePlusFour n extra) ≡ n
nineBidi (Nine.nineTrits i0 i1 i2 a0 a1 a2 b0 b1 b2) extra
  rewrite SSP.fromTriTruth-toTriTruth i0
        | SSP.fromTriTruth-toTriTruth i1
        | SSP.fromTriTruth-toTriTruth i2
        | SSP.fromTriTruth-toTriTruth a0
        | SSP.fromTriTruth-toTriTruth a1
        | SSP.fromTriTruth-toTriTruth a2
        | SSP.fromTriTruth-toTriTruth b0
        | SSP.fromTriTruth-toTriTruth b1
        | SSP.fromTriTruth-toTriTruth b2 = refl

fourBidi : (n : Nine.NineTrits) (extra : StageFour) →
  stageFourFromCentral (sourceCentralFromNinePlusFour n extra) ≡ extra
fourBidi n (stageFour p q r s) = refl

-- This equation is pointwise, avoiding unearned function extensionality.
originalStage13ReopensAtEachAxis :
  (original : Rel.SourceCentralCompletionCarrier)
  (axis : Atlas.StageAtlasZeroToEleven) →
  proj₁ (sourceCentralFromNinePlusFour
           (nativeNineFromCentral original)
           (stageFourFromCentral original)) axis
  ≡ proj₁ original axis
originalStage13ReopensAtEachAxis (valuation , centre) Atlas.atlas-0 =
  SSP.toTriTruth-fromTriTruth (valuation Atlas.atlas-0)
originalStage13ReopensAtEachAxis (valuation , centre) Atlas.atlas-1 =
  SSP.toTriTruth-fromTriTruth (valuation Atlas.atlas-1)
originalStage13ReopensAtEachAxis (valuation , centre) Atlas.atlas-2 =
  SSP.toTriTruth-fromTriTruth (valuation Atlas.atlas-2)
originalStage13ReopensAtEachAxis (valuation , centre) Atlas.atlas-3 =
  SSP.toTriTruth-fromTriTruth (valuation Atlas.atlas-3)
originalStage13ReopensAtEachAxis (valuation , centre) Atlas.atlas-4 =
  SSP.toTriTruth-fromTriTruth (valuation Atlas.atlas-4)
originalStage13ReopensAtEachAxis (valuation , centre) Atlas.atlas-5 =
  SSP.toTriTruth-fromTriTruth (valuation Atlas.atlas-5)
originalStage13ReopensAtEachAxis (valuation , centre) Atlas.atlas-6 =
  SSP.toTriTruth-fromTriTruth (valuation Atlas.atlas-6)
originalStage13ReopensAtEachAxis (valuation , centre) Atlas.atlas-7 =
  SSP.toTriTruth-fromTriTruth (valuation Atlas.atlas-7)
originalStage13ReopensAtEachAxis (valuation , centre) Atlas.atlas-8 =
  SSP.toTriTruth-fromTriTruth (valuation Atlas.atlas-8)
originalStage13ReopensAtEachAxis (valuation , centre) Atlas.atlas-9 = refl
originalStage13ReopensAtEachAxis (valuation , centre) Atlas.atlas-10 = refl
originalStage13ReopensAtEachAxis (valuation , centre) Atlas.atlas-11 = refl

originalCentreReopens :
  (original : Rel.SourceCentralCompletionCarrier) →
  proj₂ (sourceCentralFromNinePlusFour
           (nativeNineFromCentral original)
           (stageFourFromCentral original))
  ≡ proj₂ original
originalCentreReopens (valuation , centre) = refl

-- The constructed stage13 source family is ACTUALLY compatible,
-- and its original pants path reopens the source at EVERY axis.
ninePlusFourLocalFamily :
  Nine.NineTrits → StageFour → Sheaf.CentralLocalFamily
ninePlusFourLocalFamily n residual =
  Sheaf.restrictCentral (sourceCentralFromNinePlusFour n residual)

ninePlusFourCompatible :
  (n : Nine.NineTrits) (extra : StageFour) →
  Sheaf.centralFamilyCompatible (ninePlusFourLocalFamily n extra)
ninePlusFourCompatible n extra =
  Sheaf.centralRestrictsCompatible
    (sourceCentralFromNinePlusFour n extra)

ninePlusFourLocalPantsBidi :
  (n : Nine.NineTrits) (extra : StageFour)
  (axis : Atlas.StageAtlasZeroToEleven) →
  Sheaf.restrictCentral
    (Bridge13.pants13ToSourceCentral
      (Pants13.glueCompatibleLocalsToPants
        (ninePlusFourLocalFamily n extra)
        (ninePlusFourCompatible n extra))) axis
  ≡ ninePlusFourLocalFamily n extra axis
ninePlusFourLocalPantsBidi n extra axis =
  Pants13.originalPantsGlueRestricts
    (ninePlusFourLocalFamily n extra)
    (ninePlusFourCompatible n extra) axis

-- This is a chosen chart. Existing original 369 source alignment
-- requires proof that nativeNineFromCentral original equals the
-- ACTUAL full-fabric nine-trit address. Otherwise return retained
-- residual/difference: do not identify the two source readings.
