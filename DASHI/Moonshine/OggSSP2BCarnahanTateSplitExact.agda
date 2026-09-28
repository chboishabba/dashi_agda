module DASHI.Moonshine.OggSSP2BCarnahanTateSplitExact where

------------------------------------------------------------------------
-- 2B CARNAHAN TATE H0/H1 SPLIT
--
-- EXTERNAL SOURCE
--
-- Scott Carnahan, "A Self-Dual Integral Form of the Moonshine Module",
-- SIGMA 15 (2019), Corollary 3.25.
--
-- For g in class 2B the graded Tate traces are the half-sum / half-difference
--
--   H^0 : (T_gh(tau) + T_gh(tau+1/2)) / 2
--   H^1 : (T_gh(tau) - T_gh(tau+1/2)) / 2.
--
-- Thus the 2B Tate object has a genuine source-native binary cohomological
-- grading independent of the later inertia-sector geometry.
--
-- Carnahan does NOT identify this binary grading with any of the five
-- characteristic-2 inertia sectors or with Urano's parity/module tags.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Source attribution.
------------------------------------------------------------------------

carnahanSelfDualIntegralForm : Source.AttributedSource
carnahanSelfDualIntegralForm =
  Source.mkDOISource
    "Scott Carnahan"
    "A Self-Dual Integral Form of the Moonshine Module"
    "Symmetry, Integrability and Geometry: Methods and Applications 15, 030"
    "2019"
    "10.3842/SIGMA.2019.030"
    "https://doi.org/10.3842/SIGMA.2019.030"
    Source.academicArticleSource
    "Corollary 3.25 gives the 2B Tate H^0/H^1 half-sum/half-difference trace formulas involving tau and tau+1/2; no five-inertia-sector identification is stated"
    Source.publicAttribution

twoBTateSplitSourceAtlas : Source.AttributedSourceAtlas
twoBTateSplitSourceAtlas =
  Source.mkSourceAtlas
    "Carnahan 2B Tate split"
    "DASHI.Moonshine.OggSSP2BCarnahanTateSplitExact"
    (carnahanSelfDualIntegralForm ∷ [])
    "external source owns the binary Tate cohomological split only; DASHI owns any later refinement against Urano tags or inertia sectors"

------------------------------------------------------------------------
-- 2. Exact source-native binary grading.
------------------------------------------------------------------------

data TwoBTateDegree : Set where
  tateH0 :
    TwoBTateDegree
  tateH1 :
    TwoBTateDegree

data TwoBTateTraceSign : Set where
  halfSum :
    TwoBTateTraceSign
  halfDifference :
    TwoBTateTraceSign

traceSign :
  TwoBTateDegree ->
  TwoBTateTraceSign
traceSign tateH0 = halfSum
traceSign tateH1 = halfDifference

h0NotH1 :
  tateH0 ≡ tateH1 -> ⊥
h0NotH1 ()

------------------------------------------------------------------------
-- 3. Source receipt.
------------------------------------------------------------------------

record CarnahanTwoBTateSplitReceipt : Set where
  constructor carnahan-two-b-tate-split-receipt
  field
    twoBFormulaSourced :
      Bool
    twoBFormulaSourcedIsTrue :
      twoBFormulaSourced ≡ true

    h0HalfSumSourced :
      Bool
    h0HalfSumSourcedIsTrue :
      h0HalfSumSourced ≡ true

    h1HalfDifferenceSourced :
      Bool
    h1HalfDifferenceSourcedIsTrue :
      h1HalfDifferenceSourced ≡ true

    tauShiftByHalfAppears :
      Bool
    tauShiftByHalfAppearsIsTrue :
      tauShiftByHalfAppears ≡ true

    sourceIdentifiesTateDegreeWithUranoPattern :
      Bool

    sourceIdentifiesTateDegreeWithInertiaSector :
      Bool

canonicalCarnahanTwoBTateSplitReceipt :
  CarnahanTwoBTateSplitReceipt
canonicalCarnahanTwoBTateSplitReceipt =
  carnahan-two-b-tate-split-receipt
    true refl
    true refl
    true refl
    true refl
    false
    false

------------------------------------------------------------------------
-- 4. Attribution firewalls.
------------------------------------------------------------------------

data TateDegreeIsUranoParityTag : Set where
data TateDegreeIsInertiaSector : Set where
data TauHalfShiftIsPrimeLevelInertiaLocalization : Set where

tateDegreeNotIdentifiedWithUranoPattern :
  TateDegreeIsUranoParityTag -> ⊥
tateDegreeNotIdentifiedWithUranoPattern ()

tateDegreeNotIdentifiedWithInertiaSector :
  TateDegreeIsInertiaSector -> ⊥
tateDegreeNotIdentifiedWithInertiaSector ()

tauHalfShiftNotPromotedToInertiaLocalization :
  TauHalfShiftIsPrimeLevelInertiaLocalization -> ⊥
tauHalfShiftNotPromotedToInertiaLocalization ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.repositoryFormalReconstruction

record TwoBTateSplitBoundary : Set where
  constructor two-b-tate-split-boundary
  field
    carnahanExplicitlyAttributed : Bool
    twoBTateH0H1SplitSourced : Bool
    tauHalfShiftFormulaSourced : Bool
    sourceNativeBinaryCoordinateAvailable : Bool
    uranoPatternIdentificationSourced : Bool
    inertiaSectorIdentificationSourced : Bool
    attributionFirewallPreserved : Bool

canonicalTwoBTateSplitBoundary :
  TwoBTateSplitBoundary
canonicalTwoBTateSplitBoundary =
  two-b-tate-split-boundary
    true true true true false false true
