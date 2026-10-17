module DASHI.Moonshine.OggSSP2BTerminalRecognitionProductExact where

------------------------------------------------------------------------
-- TERMINAL 2B RECOGNITION PRODUCT
--
-- The post-Brauer programme has two and only two independent source-facing
-- producers left:
--
--   B'+C' : one ActualTateQ10Recognition on the literal Tate head, carrying
--           the actual ten-dimensional subquotient and descended outer action;
--
--   D     : one TwoBitSourceReceipt selecting the two remaining provenance
--           orientations of the five-mode defect chart.
--
-- Everything else on the current branch is compiler output, finite/runtime
-- evidence, or a deliberate firewall.  In particular 30->31->279 is not a
-- third producer and cannot close either component of this product.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Moonshine.OggSSP2BActualQ10RecognitionContractExact as Q10
import DASHI.Moonshine.OggSSP2BDefectTwoBitProvenanceSelectorExact as D
import DASHI.Moonshine.OggSSP2BBinaryTetrahedralDefectSourceExact as Defect
import DASHI.Biology.NonaryCompletionPhaseQuotientExact as Completion

record Terminal2BRecognition : Set₁ where
  constructor terminal-2b-recognition
  field
    actualQ10 : Q10.ActualTateQ10Recognition
    defectSource : D.TwoBitSourceReceipt
    defectSourceIsIndependent : D.independentlySourced defectSource ≡ true

open Terminal2BRecognition public

terminalFiveModeRecognition :
  Terminal2BRecognition →
  Defect.FiveModeToOrderStratumRecognition Completion.ComplementMode5
terminalFiveModeRecognition terminal =
  D.toFiveModeRecognition (defectSource terminal)

terminalActualQ10 :
  Terminal2BRecognition → Q10.ActualTateQ10Recognition
terminalActualQ10 = actualQ10

terminalDefectSource :
  Terminal2BRecognition → D.TwoBitSourceReceipt
terminalDefectSource = defectSource

record Terminal2BMaxCut : Set where
  constructor terminal-2b-max-cut
  field
    BrauerSemisimplifiedIngressPaid : Bool
    finiteTenAndOuterSourcePaid : Bool
    sameObjectQ10AndOuterDescentPaid : Bool
    independentTwoBitDefectSourcePaid : Bool
    downstream31PromotionRequired : Bool
    downstream279PromotionRequired : Bool

open Terminal2BMaxCut public

canonicalTerminal2BMaxCut : Terminal2BMaxCut
canonicalTerminal2BMaxCut =
  terminal-2b-max-cut
    true true
    false false
    false false

-- Once the two source-facing producers are inhabited, there is no third
-- mathematical integration receipt at this level: the terminal package itself
-- is the product.
assembleTerminal2BRecognition :
  (q10 : Q10.ActualTateQ10Recognition) →
  (defect : D.TwoBitSourceReceipt) →
  D.independentlySourced defect ≡ true →
  Terminal2BRecognition
assembleTerminal2BRecognition q10 defect independent =
  terminal-2b-recognition q10 defect independent
