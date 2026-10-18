module DASHI.Moonshine.OggSSPP2TrialecticNineObserverReconciliationExact where

------------------------------------------------------------------------
-- p=2 RESIDUAL TARGET <-> PRE-RH TRIALECTIC NINE-OBSERVER RECONCILIATION
--
-- DASHI CONTRIBUTION
--
-- The p=2 residual target already owns
--
--   DuplicatedCentre10 -> NineSheet = T^2
--
-- by collapsing the duplicated centre.
--
-- Independently, the pre-RH trialectic dyadic-local observer uses the ordinary
-- nine-state carrier
--
--   PhaseQuotient9 = TriTruth x TriTruth.
--
-- This module reconciles those finite carriers without importing the newer
-- trialectic observer owner into this older PR branch:
--
--   NineSheet  <-> PhaseQuotient9
--
-- and, through the canonical TriadicPAdicCodec carrier,
--
--   Kernel 2   <-> PhaseQuotient9.
--
-- The eight-state p=2 conjugate fibre is therefore exactly the noncentral
-- sector PhaseQuotient9 \ {(mid,mid)}.
--
-- Global sign inversion commutes with the rechart.  This is a finite carrier /
-- action theorem only; it does not identify the sign action with arithmetic
-- Frobenius, analytic Fricke, or Monster transport.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Product using (_×_; _,_; Σ)
open import Data.Empty using (⊥)

import Base369 as Base
import DASHI.Algebra.Trit as Trit
import DASHI.Codec.TriadicPAdicCodec as Codec
import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic
import DASHI.Foundations.TernaryEndomorphismPhaseQuotientExact as Phase
import DASHI.Moonshine.OggSSPP2BalancedTernaryPuncturedPlaneExact as Plane
import DASHI.Moonshine.OggSSPP2PuncturedKernel2BidiExact as Punctured
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Exact scalar Trit <-> TriTruth chart.
------------------------------------------------------------------------

tritToTri :
  Trit.Trit ->
  Base.TriTruth
tritToTri Trit.neg = Base.tri-low
tritToTri Trit.zer = Base.tri-mid
tritToTri Trit.pos = Base.tri-high

triToTrit :
  Base.TriTruth ->
  Trit.Trit
triToTrit Base.tri-low = Trit.neg
triToTrit Base.tri-mid = Trit.zer
triToTrit Base.tri-high = Trit.pos

triTritRoundTrip :
  (value : Base.TriTruth) ->
  tritToTri (triToTrit value) ≡ value
triTritRoundTrip Base.tri-low = refl
triTritRoundTrip Base.tri-mid = refl
triTritRoundTrip Base.tri-high = refl

tritTriRoundTrip :
  (value : Trit.Trit) ->
  triToTrit (tritToTri value) ≡ value
tritTriRoundTrip Trit.neg = refl
tritTriRoundTrip Trit.zer = refl
tritTriRoundTrip Trit.pos = refl

------------------------------------------------------------------------
-- 2. Canonical Kernel 2 <-> PhaseQuotient9.
------------------------------------------------------------------------

Kernel2 : Set
Kernel2 = Codec.Kernel 2

kernel2ToPhaseNine :
  Kernel2 ->
  Phase.PhaseQuotient9
kernel2ToPhaseNine
  (left Codec.∷ᵥ right Codec.∷ᵥ Codec.[]ᵥ) =
  tritToTri left , tritToTri right

phaseNineToKernel2 :
  Phase.PhaseQuotient9 ->
  Kernel2
phaseNineToKernel2 (left , right) =
  triToTrit left Codec.∷ᵥ
  triToTrit right Codec.∷ᵥ
  Codec.[]ᵥ

kernelPhaseRoundTrip :
  (kernel : Kernel2) ->
  phaseNineToKernel2 (kernel2ToPhaseNine kernel) ≡ kernel
kernelPhaseRoundTrip
  (left Codec.∷ᵥ right Codec.∷ᵥ Codec.[]ᵥ)
  rewrite tritTriRoundTrip left
        | tritTriRoundTrip right = refl

phaseKernelRoundTrip :
  (phase : Phase.PhaseQuotient9) ->
  kernel2ToPhaseNine (phaseNineToKernel2 phase) ≡ phase
phaseKernelRoundTrip (left , right)
  rewrite triTritRoundTrip left
        | triTritRoundTrip right = refl

------------------------------------------------------------------------
-- 3. Existing NineSheet <-> canonical Kernel 2.
------------------------------------------------------------------------

kernelTritToTrit :
  Triadic.KernelTrit ->
  Trit.Trit
kernelTritToTrit Triadic.negativeTrit = Trit.neg
kernelTritToTrit Triadic.zeroTrit = Trit.zer
kernelTritToTrit Triadic.positiveTrit = Trit.pos

tritToKernelTrit :
  Trit.Trit ->
  Triadic.KernelTrit
tritToKernelTrit Trit.neg = Triadic.negativeTrit
tritToKernelTrit Trit.zer = Triadic.zeroTrit
tritToKernelTrit Trit.pos = Triadic.positiveTrit

kernelTritRoundTrip :
  (value : Triadic.KernelTrit) ->
  tritToKernelTrit (kernelTritToTrit value) ≡ value
kernelTritRoundTrip Triadic.negativeTrit = refl
kernelTritRoundTrip Triadic.zeroTrit = refl
kernelTritRoundTrip Triadic.positiveTrit = refl

tritKernelTritRoundTrip :
  (value : Trit.Trit) ->
  kernelTritToTrit (tritToKernelTrit value) ≡ value
tritKernelTritRoundTrip Trit.neg = refl
tritKernelTritRoundTrip Trit.zer = refl
tritKernelTritRoundTrip Trit.pos = refl

nineSheetToKernel2 :
  Triadic.NineSheet ->
  Kernel2
nineSheetToKernel2 (left , right) =
  kernelTritToTrit left Codec.∷ᵥ
  kernelTritToTrit right Codec.∷ᵥ
  Codec.[]ᵥ

kernel2ToNineSheet :
  Kernel2 ->
  Triadic.NineSheet
kernel2ToNineSheet
  (left Codec.∷ᵥ right Codec.∷ᵥ Codec.[]ᵥ) =
  tritToKernelTrit left , tritToKernelTrit right

nineKernelRoundTrip :
  (sheet : Triadic.NineSheet) ->
  kernel2ToNineSheet (nineSheetToKernel2 sheet) ≡ sheet
nineKernelRoundTrip (left , right)
  rewrite kernelTritRoundTrip left
        | kernelTritRoundTrip right = refl

kernelNineRoundTrip :
  (kernel : Kernel2) ->
  nineSheetToKernel2 (kernel2ToNineSheet kernel) ≡ kernel
kernelNineRoundTrip
  (left Codec.∷ᵥ right Codec.∷ᵥ Codec.[]ᵥ)
  rewrite tritKernelTritRoundTrip left
        | tritKernelTritRoundTrip right = refl

nineSheetToPhaseNine :
  Triadic.NineSheet ->
  Phase.PhaseQuotient9
nineSheetToPhaseNine sheet =
  kernel2ToPhaseNine (nineSheetToKernel2 sheet)

phaseNineToNineSheet :
  Phase.PhaseQuotient9 ->
  Triadic.NineSheet
phaseNineToNineSheet phase =
  kernel2ToNineSheet (phaseNineToKernel2 phase)

ninePhaseRoundTrip :
  (sheet : Triadic.NineSheet) ->
  phaseNineToNineSheet (nineSheetToPhaseNine sheet) ≡ sheet
ninePhaseRoundTrip (left , right)
  rewrite kernelTritRoundTrip left
        | kernelTritRoundTrip right = refl

phaseNineRoundTrip :
  (phase : Phase.PhaseQuotient9) ->
  nineSheetToPhaseNine (phaseNineToNineSheet phase) ≡ phase
phaseNineRoundTrip (left , right)
  rewrite triTritRoundTrip left
        | triTritRoundTrip right = refl

------------------------------------------------------------------------
-- 4. p=2 duplicated-centre target collapses to the SAME nine carrier.
------------------------------------------------------------------------

duplicatedCentreToPhaseNine :
  Plane.DuplicatedCentreNineSheet ->
  Phase.PhaseQuotient9
duplicatedCentreToPhaseNine state =
  nineSheetToPhaseNine (Plane.collapseDuplicatedCentre state)

bothCentresBecomePhaseOrigin :
  duplicatedCentreToPhaseNine Plane.lowerCentre
  ≡ duplicatedCentreToPhaseNine Plane.upperCentre
bothCentresBecomePhaseOrigin = refl

lowerCentreBecomesMidMid :
  duplicatedCentreToPhaseNine Plane.lowerCentre
  ≡ (Base.tri-mid , Base.tri-mid)
lowerCentreBecomesMidMid = refl

upperCentreBecomesMidMid :
  duplicatedCentreToPhaseNine Plane.upperCentre
  ≡ (Base.tri-mid , Base.tri-mid)
upperCentreBecomesMidMid = refl

------------------------------------------------------------------------
-- 5. Exact punctured/noncentral phase sector.
------------------------------------------------------------------------

data PhaseNineNoncentral :
  Phase.PhaseQuotient9 -> Set where

  lowMid :
    PhaseNineNoncentral
      (Base.tri-low , Base.tri-mid)

  highMid :
    PhaseNineNoncentral
      (Base.tri-high , Base.tri-mid)

  midLow :
    PhaseNineNoncentral
      (Base.tri-mid , Base.tri-low)

  midHigh :
    PhaseNineNoncentral
      (Base.tri-mid , Base.tri-high)

  lowLow :
    PhaseNineNoncentral
      (Base.tri-low , Base.tri-low)

  highHigh :
    PhaseNineNoncentral
      (Base.tri-high , Base.tri-high)

  lowHigh :
    PhaseNineNoncentral
      (Base.tri-low , Base.tri-high)

  highLow :
    PhaseNineNoncentral
      (Base.tri-high , Base.tri-low)

PuncturedPhaseNine : Set
PuncturedPhaseNine =
  Σ Phase.PhaseQuotient9 PhaseNineNoncentral

puncturedKernel2ToPhaseNine :
  Punctured.PuncturedKernel2 ->
  PuncturedPhaseNine
puncturedKernel2ToPhaseNine
  ((Trit.neg Codec.∷ᵥ Trit.zer Codec.∷ᵥ Codec.[]ᵥ) , Punctured.negZero) =
  (Base.tri-low , Base.tri-mid) , lowMid
puncturedKernel2ToPhaseNine
  ((Trit.pos Codec.∷ᵥ Trit.zer Codec.∷ᵥ Codec.[]ᵥ) , Punctured.posZero) =
  (Base.tri-high , Base.tri-mid) , highMid
puncturedKernel2ToPhaseNine
  ((Trit.zer Codec.∷ᵥ Trit.neg Codec.∷ᵥ Codec.[]ᵥ) , Punctured.zeroNeg) =
  (Base.tri-mid , Base.tri-low) , midLow
puncturedKernel2ToPhaseNine
  ((Trit.zer Codec.∷ᵥ Trit.pos Codec.∷ᵥ Codec.[]ᵥ) , Punctured.zeroPos) =
  (Base.tri-mid , Base.tri-high) , midHigh
puncturedKernel2ToPhaseNine
  ((Trit.neg Codec.∷ᵥ Trit.neg Codec.∷ᵥ Codec.[]ᵥ) , Punctured.negNeg) =
  (Base.tri-low , Base.tri-low) , lowLow
puncturedKernel2ToPhaseNine
  ((Trit.pos Codec.∷ᵥ Trit.pos Codec.∷ᵥ Codec.[]ᵥ) , Punctured.posPos) =
  (Base.tri-high , Base.tri-high) , highHigh
puncturedKernel2ToPhaseNine
  ((Trit.neg Codec.∷ᵥ Trit.pos Codec.∷ᵥ Codec.[]ᵥ) , Punctured.negPos) =
  (Base.tri-low , Base.tri-high) , lowHigh
puncturedKernel2ToPhaseNine
  ((Trit.pos Codec.∷ᵥ Trit.neg Codec.∷ᵥ Codec.[]ᵥ) , Punctured.posNeg) =
  (Base.tri-high , Base.tri-low) , highLow

puncturedPhaseNineToKernel2 :
  PuncturedPhaseNine ->
  Punctured.PuncturedKernel2
puncturedPhaseNineToKernel2
  ((Base.tri-low , Base.tri-mid) , lowMid) =
  (Trit.neg Codec.∷ᵥ Trit.zer Codec.∷ᵥ Codec.[]ᵥ) , Punctured.negZero
puncturedPhaseNineToKernel2
  ((Base.tri-high , Base.tri-mid) , highMid) =
  (Trit.pos Codec.∷ᵥ Trit.zer Codec.∷ᵥ Codec.[]ᵥ) , Punctured.posZero
puncturedPhaseNineToKernel2
  ((Base.tri-mid , Base.tri-low) , midLow) =
  (Trit.zer Codec.∷ᵥ Trit.neg Codec.∷ᵥ Codec.[]ᵥ) , Punctured.zeroNeg
puncturedPhaseNineToKernel2
  ((Base.tri-mid , Base.tri-high) , midHigh) =
  (Trit.zer Codec.∷ᵥ Trit.pos Codec.∷ᵥ Codec.[]ᵥ) , Punctured.zeroPos
puncturedPhaseNineToKernel2
  ((Base.tri-low , Base.tri-low) , lowLow) =
  (Trit.neg Codec.∷ᵥ Trit.neg Codec.∷ᵥ Codec.[]ᵥ) , Punctured.negNeg
puncturedPhaseNineToKernel2
  ((Base.tri-high , Base.tri-high) , highHigh) =
  (Trit.pos Codec.∷ᵥ Trit.pos Codec.∷ᵥ Codec.[]ᵥ) , Punctured.posPos
puncturedPhaseNineToKernel2
  ((Base.tri-low , Base.tri-high) , lowHigh) =
  (Trit.neg Codec.∷ᵥ Trit.pos Codec.∷ᵥ Codec.[]ᵥ) , Punctured.negPos
puncturedPhaseNineToKernel2
  ((Base.tri-high , Base.tri-low) , highLow) =
  (Trit.pos Codec.∷ᵥ Trit.neg Codec.∷ᵥ Codec.[]ᵥ) , Punctured.posNeg

puncturedKernelPhaseRoundTrip :
  (point : Punctured.PuncturedKernel2) ->
  puncturedPhaseNineToKernel2
    (puncturedKernel2ToPhaseNine point)
  ≡ point
puncturedKernelPhaseRoundTrip
  ((Trit.neg Codec.∷ᵥ Trit.zer Codec.∷ᵥ Codec.[]ᵥ) , Punctured.negZero) = refl
puncturedKernelPhaseRoundTrip
  ((Trit.pos Codec.∷ᵥ Trit.zer Codec.∷ᵥ Codec.[]ᵥ) , Punctured.posZero) = refl
puncturedKernelPhaseRoundTrip
  ((Trit.zer Codec.∷ᵥ Trit.neg Codec.∷ᵥ Codec.[]ᵥ) , Punctured.zeroNeg) = refl
puncturedKernelPhaseRoundTrip
  ((Trit.zer Codec.∷ᵥ Trit.pos Codec.∷ᵥ Codec.[]ᵥ) , Punctured.zeroPos) = refl
puncturedKernelPhaseRoundTrip
  ((Trit.neg Codec.∷ᵥ Trit.neg Codec.∷ᵥ Codec.[]ᵥ) , Punctured.negNeg) = refl
puncturedKernelPhaseRoundTrip
  ((Trit.pos Codec.∷ᵥ Trit.pos Codec.∷ᵥ Codec.[]ᵥ) , Punctured.posPos) = refl
puncturedKernelPhaseRoundTrip
  ((Trit.neg Codec.∷ᵥ Trit.pos Codec.∷ᵥ Codec.[]ᵥ) , Punctured.negPos) = refl
puncturedKernelPhaseRoundTrip
  ((Trit.pos Codec.∷ᵥ Trit.neg Codec.∷ᵥ Codec.[]ᵥ) , Punctured.posNeg) = refl

puncturedPhaseKernelRoundTrip :
  (point : PuncturedPhaseNine) ->
  puncturedKernel2ToPhaseNine
    (puncturedPhaseNineToKernel2 point)
  ≡ point
puncturedPhaseKernelRoundTrip
  ((Base.tri-low , Base.tri-mid) , lowMid) = refl
puncturedPhaseKernelRoundTrip
  ((Base.tri-high , Base.tri-mid) , highMid) = refl
puncturedPhaseKernelRoundTrip
  ((Base.tri-mid , Base.tri-low) , midLow) = refl
puncturedPhaseKernelRoundTrip
  ((Base.tri-mid , Base.tri-high) , midHigh) = refl
puncturedPhaseKernelRoundTrip
  ((Base.tri-low , Base.tri-low) , lowLow) = refl
puncturedPhaseKernelRoundTrip
  ((Base.tri-high , Base.tri-high) , highHigh) = refl
puncturedPhaseKernelRoundTrip
  ((Base.tri-low , Base.tri-high) , lowHigh) = refl
puncturedPhaseKernelRoundTrip
  ((Base.tri-high , Base.tri-low) , highLow) = refl

------------------------------------------------------------------------
-- 6. Global signed C2 intertwining on the shared nine carrier.
------------------------------------------------------------------------

negateTri :
  Base.TriTruth ->
  Base.TriTruth
negateTri Base.tri-low = Base.tri-high
negateTri Base.tri-mid = Base.tri-mid
negateTri Base.tri-high = Base.tri-low

negatePhaseNine :
  Phase.PhaseQuotient9 ->
  Phase.PhaseQuotient9
negatePhaseNine (left , right) =
  negateTri left , negateTri right

kernel2PhaseNegationIntertwines :
  (kernel : Kernel2) ->
  kernel2ToPhaseNine (Codec.invertKernel kernel)
  ≡ negatePhaseNine (kernel2ToPhaseNine kernel)
kernel2PhaseNegationIntertwines
  (Trit.neg Codec.∷ᵥ Trit.neg Codec.∷ᵥ Codec.[]ᵥ) = refl
kernel2PhaseNegationIntertwines
  (Trit.neg Codec.∷ᵥ Trit.zer Codec.∷ᵥ Codec.[]ᵥ) = refl
kernel2PhaseNegationIntertwines
  (Trit.neg Codec.∷ᵥ Trit.pos Codec.∷ᵥ Codec.[]ᵥ) = refl
kernel2PhaseNegationIntertwines
  (Trit.zer Codec.∷ᵥ Trit.neg Codec.∷ᵥ Codec.[]ᵥ) = refl
kernel2PhaseNegationIntertwines
  (Trit.zer Codec.∷ᵥ Trit.zer Codec.∷ᵥ Codec.[]ᵥ) = refl
kernel2PhaseNegationIntertwines
  (Trit.zer Codec.∷ᵥ Trit.pos Codec.∷ᵥ Codec.[]ᵥ) = refl
kernel2PhaseNegationIntertwines
  (Trit.pos Codec.∷ᵥ Trit.neg Codec.∷ᵥ Codec.[]ᵥ) = refl
kernel2PhaseNegationIntertwines
  (Trit.pos Codec.∷ᵥ Trit.zer Codec.∷ᵥ Codec.[]ᵥ) = refl
kernel2PhaseNegationIntertwines
  (Trit.pos Codec.∷ᵥ Trit.pos Codec.∷ᵥ Codec.[]ᵥ) = refl

------------------------------------------------------------------------
-- 7. Reconciliation boundary.
------------------------------------------------------------------------

data SharedNineCarrierCreatesArithmeticRecognition : Set where
data SharedSignedC2CreatesFrickeOrMonsterRecognition : Set where

sharedNineCarrierDoesNotCreateArithmeticRecognition :
  SharedNineCarrierCreatesArithmeticRecognition -> ⊥
sharedNineCarrierDoesNotCreateArithmeticRecognition ()

sharedSignedC2DoesNotCreateFrickeOrMonsterRecognition :
  SharedSignedC2CreatesFrickeOrMonsterRecognition -> ⊥
sharedSignedC2DoesNotCreateFrickeOrMonsterRecognition ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin = Attribution.repositoryCrossModuleInference

record P2TrialecticNineObserverReconciliationBoundary : Set where
  constructor p2-trialectic-nine-observer-reconciliation-boundary
  field
    kernel2ToPhaseNineBidiPaid : Bool
    nineSheetToPhaseNineBidiPaid : Bool
    duplicatedCentreTenCollapsesToPhaseNine : Bool
    puncturedKernel2EqualsNoncentralPhaseSector : Bool
    signedC2IntertwinerPaid : Bool
    arithmeticRecognitionClaimed : Bool
    analyticFrickeOrMonsterRecognitionClaimed : Bool

canonicalP2TrialecticNineObserverReconciliationBoundary :
  P2TrialecticNineObserverReconciliationBoundary
canonicalP2TrialecticNineObserverReconciliationBoundary =
  p2-trialectic-nine-observer-reconciliation-boundary
    true true true true true false false
