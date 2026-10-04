module DASHI.Moonshine.OggSSP2BDefectTwoBitProvenanceSelectorExact where

------------------------------------------------------------------------
-- FINAL D MAX-CUT: TWO SOURCE DECISIONS
--
-- The sourced defect profile leaves exactly four compatible charts.  The
-- ambiguity is exactly 2 x 2:
--
--   depth 3: mode09/mode18 <-> identity/centralMinusOne
--   depth 2: mode27        -> orderFour                 (forced)
--   depth 1: mode36/mode45 <-> orderThree/orderSix
--
-- Therefore D needs two independent provenance decisions, not an arbitrary
-- five-label bijection.  This owner compiles those decisions into the existing
-- source-recognition surface without fabricating them.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String; primStringAppend)
open import Data.Empty using (⊥)

import DASHI.Biology.NonaryCompletionPhaseQuotientExact as Completion
import DASHI.Moonshine.OggSSP2BBinaryTetrahedralDefectSourceExact as Defect

------------------------------------------------------------------------
-- 1. The two unresolved orientations.
------------------------------------------------------------------------

data DepthThreeOrientation : Set where
  mode09IsIdentity mode18IsIdentity : DepthThreeOrientation

data DepthOneOrientation : Set where
  mode36IsOrderThree mode45IsOrderThree : DepthOneOrientation

record ProvenanceBits : Set where
  constructor provenance-bits
  field
    depthThree : DepthThreeOrientation
    depthOne : DepthOneOrientation

open ProvenanceBits public

provenanceChoiceCount : Nat
provenanceChoiceCount = 4

provenanceChoiceCountIsFour : provenanceChoiceCount ≡ 4
provenanceChoiceCountIsFour = refl

------------------------------------------------------------------------
-- 2. Compile the choices to the five order strata.
------------------------------------------------------------------------

chartFromBits :
  ProvenanceBits → Completion.ComplementMode5 → Defect.OrderStratum
chartFromBits (provenance-bits mode09IsIdentity mode36IsOrderThree) Completion.mode09 = Defect.identity
chartFromBits (provenance-bits mode09IsIdentity mode36IsOrderThree) Completion.mode18 = Defect.centralMinusOne
chartFromBits (provenance-bits mode09IsIdentity mode36IsOrderThree) Completion.mode27 = Defect.orderFour
chartFromBits (provenance-bits mode09IsIdentity mode36IsOrderThree) Completion.mode36 = Defect.orderThree
chartFromBits (provenance-bits mode09IsIdentity mode36IsOrderThree) Completion.mode45 = Defect.orderSix
chartFromBits (provenance-bits mode18IsIdentity mode36IsOrderThree) Completion.mode09 = Defect.centralMinusOne
chartFromBits (provenance-bits mode18IsIdentity mode36IsOrderThree) Completion.mode18 = Defect.identity
chartFromBits (provenance-bits mode18IsIdentity mode36IsOrderThree) Completion.mode27 = Defect.orderFour
chartFromBits (provenance-bits mode18IsIdentity mode36IsOrderThree) Completion.mode36 = Defect.orderThree
chartFromBits (provenance-bits mode18IsIdentity mode36IsOrderThree) Completion.mode45 = Defect.orderSix
chartFromBits (provenance-bits mode09IsIdentity mode45IsOrderThree) Completion.mode09 = Defect.identity
chartFromBits (provenance-bits mode09IsIdentity mode45IsOrderThree) Completion.mode18 = Defect.centralMinusOne
chartFromBits (provenance-bits mode09IsIdentity mode45IsOrderThree) Completion.mode27 = Defect.orderFour
chartFromBits (provenance-bits mode09IsIdentity mode45IsOrderThree) Completion.mode36 = Defect.orderSix
chartFromBits (provenance-bits mode09IsIdentity mode45IsOrderThree) Completion.mode45 = Defect.orderThree
chartFromBits (provenance-bits mode18IsIdentity mode45IsOrderThree) Completion.mode09 = Defect.centralMinusOne
chartFromBits (provenance-bits mode18IsIdentity mode45IsOrderThree) Completion.mode18 = Defect.identity
chartFromBits (provenance-bits mode18IsIdentity mode45IsOrderThree) Completion.mode27 = Defect.orderFour
chartFromBits (provenance-bits mode18IsIdentity mode45IsOrderThree) Completion.mode36 = Defect.orderSix
chartFromBits (provenance-bits mode18IsIdentity mode45IsOrderThree) Completion.mode45 = Defect.orderThree

orderFourIsForced :
  (bits : ProvenanceBits) →
  chartFromBits bits Completion.mode27 ≡ Defect.orderFour
orderFourIsForced (provenance-bits mode09IsIdentity mode36IsOrderThree) = refl
orderFourIsForced (provenance-bits mode18IsIdentity mode36IsOrderThree) = refl
orderFourIsForced (provenance-bits mode09IsIdentity mode45IsOrderThree) = refl
orderFourIsForced (provenance-bits mode18IsIdentity mode45IsOrderThree) = refl

------------------------------------------------------------------------
-- 3. The only remaining D source receipt.
------------------------------------------------------------------------

record TwoBitSourceReceipt : Set where
  constructor two-bit-source-receipt
  field
    bits : ProvenanceBits
    depthThreeSourceProvenance : String
    depthOneSourceProvenance : String
    independentlySourced : Bool

open TwoBitSourceReceipt public

toFiveModeRecognition :
  TwoBitSourceReceipt →
  Defect.FiveModeToOrderStratumRecognition Completion.ComplementMode5
toFiveModeRecognition r = record
  { modeToOrderStratum = chartFromBits (bits r)
  ; sourceProvenance =
      primStringAppend "depth-3: "
        (primStringAppend (depthThreeSourceProvenance r)
          (primStringAppend "; depth-1: " (depthOneSourceProvenance r)))
  ; independentlySourced = independentlySourced r
  }

data DefectProfileConstructsTwoProvenanceBits : Set where

defectProfileDoesNotConstructTwoProvenanceBits :
  DefectProfileConstructsTwoProvenanceBits → ⊥
defectProfileDoesNotConstructTwoProvenanceBits ()

record FinalDResidualStatus : Set where
  constructor final-d-residual-status
  field
    arbitraryFiveLabelBijections : Nat
    defectCompatibleCharts : Nat
    remainingIndependentSourceDecisions : Nat
    orderFourAssignmentForced : Bool
    sourceSelectionPaid : Bool

canonicalFinalDResidualStatus : FinalDResidualStatus
canonicalFinalDResidualStatus =
  final-d-residual-status 120 4 2 true false
