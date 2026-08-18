module DASHI.Physics.Closure.NSTriadKNTwoChannelStructuredCauchyOverlayRound74Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Augustin-Louis Cauchy; Hermann Amandus Schwarz.
-- Classical finite Cauchy--Schwarz inequality; DOI not applicable.
--
-- Author: Fabian Waleffe.
-- Title: "The nature of triad interactions in homogeneous turbulence".
-- DOI: 10.1063/1.858309.
--
-- ROUND74 / TWO PRODUCT CHANNELS PER PHYSICAL TRIAD
--
-- Round72's finite Cauchy engine already consumes an arbitrary flat list of
-- product contributions.  Only its structured overlay forced one product per
-- triadic atom.  Round74 removes that artificial restriction.
--
-- Every triadic atom may now refine canonically as
--
--     a_tau = x0_tau y0_tau + x1_tau y1_tau.
--
-- The extracted contribution list contains TWO entries for that same atom.
-- Its factorized signed sum is proved to equal the original Round71 triadic
-- signed sum exactly, so all existing Q/W Cauchy machinery applies unchanged.
--
-- This is the exact downstream consumer required by the literal complex
-- identity Re(zw)=Re(z)Re(w)-Im(z)Im(w).  No phase alignment or arbitrary
-- post-hoc rescaling is required merely to obtain a product decomposition.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSTriadKNLuoPhysicalFiveClassSupportRound25Exact as Support
import DASHI.Physics.Closure.NSTriadKNLocalizedPDEStructuredAtomsRound62Exact as Structured
import DASHI.Physics.Closure.NSTriadKNCriticalRemainderTriadicCauchyRound71Exact as R71
import DASHI.Physics.Closure.NSTriadKNFactorizedEffectiveComplexityCauchyRound72Exact as Effective
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2

data TriadicTwoChannelOverlay :
    List Structured.LocalizedPDEAtom → Set where
  overlay[] : TriadicTwoChannelOverlay []

  overlayTriadic2 :
    ∀ {classified selected compatible value rest}
      (left0 right0 left1 right1 : ℚ) →
    value ≡ left0 * right0 + left1 * right1 →
    TriadicTwoChannelOverlay rest →
    TriadicTwoChannelOverlay
      (Structured.physicalAtom (Support.triadicSource classified)
        selected compatible value ∷ rest)

  overlayCom :
    ∀ {output selected compatible value rest} →
    TriadicTwoChannelOverlay rest →
    TriadicTwoChannelOverlay
      (Structured.physicalAtom (Support.differentiatedCommutator output)
        selected compatible value ∷ rest)

  overlayTail : ∀ {value rest} →
    TriadicTwoChannelOverlay rest →
    TriadicTwoChannelOverlay (Structured.tailAtom value ∷ rest)

  overlayDuplicateKernel : ∀ {value rest} →
    TriadicTwoChannelOverlay rest →
    TriadicTwoChannelOverlay (Structured.duplicateKernelAtom value ∷ rest)

  overlayCancellingKernel : ∀ {left right cancellation rest} →
    TriadicTwoChannelOverlay rest →
    TriadicTwoChannelOverlay
      (Structured.cancellingKernelPair left right cancellation ∷ rest)

  overlayIndependentKernel : ∀ {value rest} →
    TriadicTwoChannelOverlay rest →
    TriadicTwoChannelOverlay (Structured.independentKernelAtom value ∷ rest)

  overlayLowerBoundary : ∀ {reason value rest} →
    TriadicTwoChannelOverlay rest →
    TriadicTwoChannelOverlay
      (Structured.lowerBoundaryAtom reason value ∷ rest)

  overlayUpperBoundary : ∀ {reason value rest} →
    TriadicTwoChannelOverlay rest →
    TriadicTwoChannelOverlay
      (Structured.upperBoundaryAtom reason value ∷ rest)

twoChannelFactors :
  ∀ {atoms} → TriadicTwoChannelOverlay atoms →
  List Effective.FactorizedContribution
twoChannelFactors overlay[] = []
twoChannelFactors
    (overlayTriadic2 left0 right0 left1 right1 exact rest) =
  Effective.factorized-contribution left0 right0
  ∷ Effective.factorized-contribution left1 right1
  ∷ twoChannelFactors rest
twoChannelFactors (overlayCom rest) = twoChannelFactors rest
twoChannelFactors (overlayTail rest) = twoChannelFactors rest
twoChannelFactors (overlayDuplicateKernel rest) = twoChannelFactors rest
twoChannelFactors (overlayCancellingKernel rest) = twoChannelFactors rest
twoChannelFactors (overlayIndependentKernel rest) = twoChannelFactors rest
twoChannelFactors (overlayLowerBoundary rest) = twoChannelFactors rest
twoChannelFactors (overlayUpperBoundary rest) = twoChannelFactors rest

twoChannelSignedSumExact :
  ∀ {atoms} (overlay : TriadicTwoChannelOverlay atoms) →
  Effective.factorizedSignedSum (twoChannelFactors overlay)
  ≡ R71.triadicSignedSum atoms
twoChannelSignedSumExact overlay[] = refl
twoChannelSignedSumExact
    (overlayTriadic2 {value = value}
      left0 right0 left1 right1 exact rest) =
  let
    tail = R71.triadicSignedSum _
  in
  trans
    (cong
      (λ selectedTail →
        left0 * right0 + (left1 * right1 + selectedTail))
      (twoChannelSignedSumExact rest))
    (trans
      (sym (ℚP.+-assoc (left0 * right0) (left1 * right1) tail))
      (cong (λ head → head + tail) (sym exact)))
twoChannelSignedSumExact (overlayCom rest) = twoChannelSignedSumExact rest
twoChannelSignedSumExact (overlayTail rest) = twoChannelSignedSumExact rest
twoChannelSignedSumExact (overlayDuplicateKernel rest) = twoChannelSignedSumExact rest
twoChannelSignedSumExact (overlayCancellingKernel rest) = twoChannelSignedSumExact rest
twoChannelSignedSumExact (overlayIndependentKernel rest) = twoChannelSignedSumExact rest
twoChannelSignedSumExact (overlayLowerBoundary rest) = twoChannelSignedSumExact rest
twoChannelSignedSumExact (overlayUpperBoundary rest) = twoChannelSignedSumExact rest

twoChannelCharge : ∀ {atoms} → TriadicTwoChannelOverlay atoms → ℚ
twoChannelCharge overlay =
  Effective.concentrationCharge (twoChannelFactors overlay)

twoChannelEffectiveComplexity :
  ∀ {atoms} → TriadicTwoChannelOverlay atoms → ℚ
twoChannelEffectiveComplexity overlay =
  Effective.effectiveComplexity (twoChannelFactors overlay)

twoChannelCauchy :
  ∀ {atoms} (overlay : TriadicTwoChannelOverlay atoms) →
  L2.square (R71.triadicSignedSum atoms)
  ≤ twoChannelCharge overlay * twoChannelEffectiveComplexity overlay
twoChannelCauchy overlay =
  subst
    (λ signed →
      L2.square signed
      ≤ twoChannelCharge overlay * twoChannelEffectiveComplexity overlay)
    (twoChannelSignedSumExact overlay)
    (Effective.factorizedCauchy (twoChannelFactors overlay))

round74TwoChannelStructuredOverlayConstructed : Bool
round74TwoChannelStructuredOverlayConstructed = true

round74TwoChannelCauchyConsumesSameRound62AtomList : Bool
round74TwoChannelCauchyConsumesSameRound62AtomList = true

round74PhysicalRealImaginaryChannelsTransportedToRationalOverlay : Bool
round74PhysicalRealImaginaryChannelsTransportedToRationalOverlay = false

round74TwoChannelStructuredOverlayConstructedIsTrue :
  round74TwoChannelStructuredOverlayConstructed ≡ true
round74TwoChannelStructuredOverlayConstructedIsTrue = refl

round74PhysicalRealImaginaryChannelsTransportedToRationalOverlayIsFalse :
  round74PhysicalRealImaginaryChannelsTransportedToRationalOverlay ≡ false
round74PhysicalRealImaginaryChannelsTransportedToRationalOverlayIsFalse = refl
