module DASHI.Moonshine.GoldenRatioFibonacci369RichFibreLiftExact where

------------------------------------------------------------------------
-- RICH FIBRE LIFT OF THE FIBONACCI 3 / 6 / 9 / 27 OBSERVER
--
-- Retain the information deliberately forgotten by the finite observer:
-- exact numerator/denominator, quadratic-defect magnitude, and signed-prime
-- compression.  The Base369 3/6/9/27 objects are projections of this richer
-- carrier, not substitutes for it.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic
import DASHI.Biology.SignedSSPFRACTRANWeaveExact as SSP
import DASHI.Physics.Closure.SU2SO3369HypervoxelBridge as Hyper
import DASHI.Moonshine.QuadraticApproximationPrimeCompressionBidiExact as Compression
import DASHI.Moonshine.GoldenRatioFibonacci369SheetVoxelBridgeExact as Fib369

record RichDefectFibre : Set where
  constructor rich-defect-fibre
  field
    numerator : Nat
    denominator : Nat
    defectSign : Triadic.KernelTrit
    defectMagnitude : Nat
    primeCompression : Compression.PrimeCompressionFibre

open RichDefectFibre public

observe3 : RichDefectFibre → Triadic.KernelTrit
observe3 = defectSign

flipRichObserver : RichDefectFibre → RichDefectFibre
flipRichObserver f =
  rich-defect-fibre
    (numerator f)
    (denominator f)
    (Triadic.negateTrit (defectSign f))
    (defectMagnitude f)
    (primeCompression f)

flipRichObserverPreservesMagnitude :
  ∀ f → defectMagnitude (flipRichObserver f) ≡ defectMagnitude f
flipRichObserverPreservesMagnitude f = refl

flipRichObserverPreservesCompression :
  ∀ f → primeCompression (flipRichObserver f) ≡ primeCompression f
flipRichObserverPreservesCompression f = refl

flipRichObserverProjectsToFibTritStep :
  ∀ f → observe3 (flipRichObserver f) ≡ Fib369.fibTritStep (observe3 f)
flipRichObserverProjectsToFibTritStep f = refl

flipRichObserverInvolutive :
  ∀ f → flipRichObserver (flipRichObserver f) ≡ f
flipRichObserverInvolutive
  (rich-defect-fibre p q Triadic.negativeTrit m c) = refl
flipRichObserverInvolutive
  (rich-defect-fibre p q Triadic.zeroTrit m c) = refl
flipRichObserverInvolutive
  (rich-defect-fibre p q Triadic.positiveTrit m c) = refl

emptyResidual : List Compression.PrimeExponent
emptyResidual = []

phi2Over1PrimeFibre : Compression.PrimeCompressionFibre
phi2Over1PrimeFibre =
  Compression.prime-compression-fibre
    (Compression.primeExponent 2 (SSP.positiveMultiplicity 1) ∷ []) []

phi5Over3PrimeFibre : Compression.PrimeCompressionFibre
phi5Over3PrimeFibre =
  Compression.prime-compression-fibre
    (Compression.primeExponent 5 (SSP.positiveMultiplicity 1) ∷
     Compression.primeExponent 3 (SSP.negativeMultiplicity 1) ∷ []) []

phi13Over8PrimeFibre : Compression.PrimeCompressionFibre
phi13Over8PrimeFibre =
  Compression.prime-compression-fibre
    (Compression.primeExponent 13 (SSP.positiveMultiplicity 1) ∷
     Compression.primeExponent 2 (SSP.negativeMultiplicity 3) ∷ []) []

phi34Over21PrimeFibre : Compression.PrimeCompressionFibre
phi34Over21PrimeFibre =
  Compression.prime-compression-fibre
    (Compression.primeExponent 2 (SSP.positiveMultiplicity 1) ∷
     Compression.primeExponent 17 (SSP.positiveMultiplicity 1) ∷
     Compression.primeExponent 3 (SSP.negativeMultiplicity 1) ∷
     Compression.primeExponent 7 (SSP.negativeMultiplicity 1) ∷ []) []

phi2Over1Rich : RichDefectFibre
phi2Over1Rich = rich-defect-fibre 2 1 Triadic.positiveTrit 1 phi2Over1PrimeFibre

phi5Over3Rich : RichDefectFibre
phi5Over3Rich = rich-defect-fibre 5 3 Triadic.positiveTrit 1 phi5Over3PrimeFibre

phi13Over8Rich : RichDefectFibre
phi13Over8Rich = rich-defect-fibre 13 8 Triadic.positiveTrit 1 phi13Over8PrimeFibre

phi34Over21Rich : RichDefectFibre
phi34Over21Rich = rich-defect-fibre 34 21 Triadic.positiveTrit 1 phi34Over21PrimeFibre

normOneMagnitudesRetained :
  (defectMagnitude phi2Over1Rich ≡ 1) ×
  (defectMagnitude phi5Over3Rich ≡ 1) ×
  (defectMagnitude phi13Over8Rich ≡ 1) ×
  (defectMagnitude phi34Over21Rich ≡ 1)
normOneMagnitudesRetained = refl , refl , refl , refl

------------------------------------------------------------------------
-- Rich six-line.  The deck transformation preserves the projected 3-base and
-- flips only the two-sheet polarity.  It is a chirality lift of the Fibonacci
-- transition, not the whole arithmetic transition.
------------------------------------------------------------------------

record RichSixLine : Set where
  constructor rich-six-line
  field
    payload : RichDefectFibre
    side : Compression.StrictSignedSide

open RichSixLine public

observe6 : RichSixLine → Fib369.FibSixLine
observe6 x = observe3 (payload x) , side x

deckFlipRichSix : RichSixLine → RichSixLine
deckFlipRichSix x =
  rich-six-line (payload x) (Fib369.flipStrictSide (side x))

observe6DeckFlip :
  ∀ x → observe6 (deckFlipRichSix x) ≡ Fib369.fibSixFlip (observe6 x)
observe6DeckFlip (rich-six-line f Compression.lowerSide) = refl
observe6DeckFlip (rich-six-line f Compression.upperSide) = refl

richSixDeckTransformationAgreesWithExisting :
  ∀ x →
  Fib369.sixToExistingAxisLift (observe6 (deckFlipRichSix x))
  ≡ Hyper.flipAxisLift (Fib369.sixToExistingAxisLift (observe6 x))
richSixDeckTransformationAgreesWithExisting x =
  Fib369.fibSixFlipIsExistingDeckTransformation (observe6 x)

------------------------------------------------------------------------
-- Rich nine comparison sheet.
------------------------------------------------------------------------

record RichComparisonSheet9 : Set where
  constructor rich-comparison-sheet9
  field
    current : RichDefectFibre
    next : RichDefectFibre

open RichComparisonSheet9 public

observe9 : RichComparisonSheet9 → Triadic.NineSheet
observe9 s = observe3 (current s) , observe3 (next s)

observerFibComparison : RichDefectFibre → RichComparisonSheet9
observerFibComparison f = rich-comparison-sheet9 f (flipRichObserver f)

observeObserverFibComparison :
  ∀ f → observe9 (observerFibComparison f) ≡ Fib369.fibComparison (observe3 f)
observeObserverFibComparison f = refl

------------------------------------------------------------------------
-- Rich 27 voxel.
------------------------------------------------------------------------

record RichVoxel27 : Set where
  constructor rich-voxel27
  field
    step0 : RichDefectFibre
    step1 : RichDefectFibre
    step2 : RichDefectFibre

open RichVoxel27 public

observe27 : RichVoxel27 → Fib369.FibVoxel27
observe27 v = observe3 (step0 v) , observe3 (step1 v) , observe3 (step2 v)

observerFibVoxel : RichDefectFibre → RichVoxel27
observerFibVoxel f = rich-voxel27 f (flipRichObserver f) f

observeObserverFibVoxel :
  ∀ f → observe27 (observerFibVoxel f) ≡ Fib369.fibVoxel (observe3 f)
observeObserverFibVoxel f = refl

advanceObserverVoxel : RichVoxel27 → RichVoxel27
advanceObserverVoxel v =
  rich-voxel27
    (flipRichObserver (step0 v))
    (flipRichObserver (step1 v))
    (flipRichObserver (step2 v))

observeAdvanceObserverVoxel :
  ∀ v → observe27 (advanceObserverVoxel v) ≡ Fib369.negateVoxel (observe27 v)
observeAdvanceObserverVoxel v = refl

advanceObserverVoxelPreservesAllMagnitudes :
  ∀ v →
  (defectMagnitude (step0 (advanceObserverVoxel v)) ≡ defectMagnitude (step0 v)) ×
  (defectMagnitude (step1 (advanceObserverVoxel v)) ≡ defectMagnitude (step1 v)) ×
  (defectMagnitude (step2 (advanceObserverVoxel v)) ≡ defectMagnitude (step2 v))
advanceObserverVoxelPreservesAllMagnitudes v = refl , refl , refl

data RichFibreResidual : Set where
  missingArithmeticEvolutionWeld : RichFibreResidual
  missingGeneralPrimeFactorisationProducer : RichFibreResidual
  missingCompressionCostTheorem : RichFibreResidual
  missingSameBishopPhiLimitBridge : RichFibreResidual

record RichFibonacci369Frontier : Set where
  constructor rich-fibonacci369-frontier
  field
    signProjectionExact : Bool
    defectMagnitudeRetained : Bool
    primeCompressionRetained : Bool
    sixDeckProjectionExact : Bool
    nineComparisonProjectionExact : Bool
    voxelProjectionExact : Bool
    arithmeticNumeratorDenominatorEvolutionSameObject : Bool
    bishopPhiLimitPaid : Bool
    firstResidual : RichFibreResidual

canonicalRichFibonacci369Frontier : RichFibonacci369Frontier
canonicalRichFibonacci369Frontier =
  rich-fibonacci369-frontier
    true true true true true true false false
    missingArithmeticEvolutionWeld
