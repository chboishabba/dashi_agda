module DASHI.ComputerScience.TekumHardwareCodecCrossPollinationExact where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Maybe using (just)

import DASHI.Algebra.Trit as Trit
import DASHI.Codec.VerifiedFiniteTritCoder as Binary
import DASHI.Foundations.SSPTritCarrier as SSPTrit
import DASHI.ComputerScience.TekumSSPFRACTRANBridgeExact as SSPF

------------------------------------------------------------------------
-- One Tekum trit has three deliberately distinct implementation views:
-- native Trit, fixed two-bit binary code, and SSP/FRACTRAN signed carrier.

record TekumDigitImplementationViews : Set where
  constructor tekumDigitImplementationViews
  field
    sourceTrit : Trit.Trit
    binaryCode : Binary.Word2
    sspTrit : SSPTrit.SSPTrit
open TekumDigitImplementationViews public

views : Trit.Trit → TekumDigitImplementationViews
views t =
  tekumDigitImplementationViews
    t
    (Binary.encodeTrit t)
    (SSPF.tekumTritToSSP t)

binaryViewRoundTrips :
  (t : Trit.Trit) →
  Binary.decodeWord (binaryCode (views t)) ≡ just t
binaryViewRoundTrips = Binary.decode-encode

record CostAxesBoundary : Set where
  constructor costAxesBoundary
  field
    storageDensityDistinctFromTransitionDilation : Bool
    transitionDilationDistinctFromAdderCriticalPath : Bool
    nineTritOptimalBinaryWidthIsFifteenBits : Bool
    naiveTwoBitNineTritWidthIsEighteenBits : Bool
    schloeglFeyTimingRemainsAttributedEmpiricalEvidence : Bool

canonicalCostAxesBoundary : CostAxesBoundary
canonicalCostAxesBoundary =
  costAxesBoundary true true true true true
