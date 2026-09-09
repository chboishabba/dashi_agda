module DASHI.Moonshine.GoldenRatioFibonacci369RichFibreLiftExact where

------------------------------------------------------------------------
-- RICH FIBRE LIFT OF THE FIBONACCI 3 / 6 / 9 / 27 OBSERVER
--
-- The previous bridge proved that the balanced sign of the golden-ratio
-- quadratic defect follows the existing Base369 hierarchy:
--
--   3  : one defect trit
--   6  : 3-valued base x two-sheet strict-nonzero polarity
--   9  : current/next comparison sheet
--   27 : three-step local voxel
--
-- This owner retains the information deliberately forgotten by that observer:
-- exact defect magnitude and the signed-prime/FRACTRAN representation fibre.
-- The 3/6/9/27 objects are projections of this richer carrier, not substitutes
-- for it.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic
import DASHI.Biology.SignedSSPFRACTRANWeaveExact as SSP
import DASHI.Foundations.Base369MobiusTransport as Mobius
import DASHI.Physics.Closure.SU2SO3369HypervoxelBridge as Hyper
import DASHI.Moonshine.QuadraticApproximationPrimeCompressionBidiExact as Compression
import DASHI.Moonshine.GoldenRatioFibonacci369SheetVoxelBridgeExact as Fib369

------------------------------------------------------------------------
-- 1. Rich approximation fibre.
------------------------------------------------------------------------

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

-- A Fibonacci step changes the sign observer while retaining the other fibre
-- coordinates at this abstraction boundary.  Exact arithmetic evolution of
-- numerator/denominator is supplied by the Fibonacci owner; this map isolates
-- the deck-action coordinate.
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

------------------------------------------------------------------------
-- 2. Exact prime fibres for the first four norm-one Fibonacci approximants.
------------------------------------------------------------------------

emptyResidual : List Compression.PrimeExponent
emptyResidual = []

phi2Over1PrimeFibre : Compression.PrimeCompressionFibre
phi2Over1PrimeFibre =
  Compression.prime-compression-fibre
    (Compression.primeExponent 2 (SSP.positiveMultiplicity 1) ∷ [])
    emptyResidual

phi5Over3PrimeFibre : Compression.PrimeCompressionFibre
phi5Over3PrimeFibre =
  Compression.prime-compression-fibre
    (Compression.primeExponent 5 (SSP.positiveMultiplicity 1) ∷
     Compression.primeExponent 3 (SSP.negativeMultiplicity 1) ∷ [])
    emptyResidual

phi13Over8PrimeFibre : Compression.PrimeCompressionFibre
phi13Over8PrimeFibre =
  Compression.prime-compression-fibre
    (Compression.primeExponent 13 (SSP.positiveMultiplicity 1) ∷
     Compression.primeExponent 2 (SSP.negativeMultiplicity 3) ∷ [])
    emptyResidual

phi34Over21PrimeFibre : Compression.PrimeCompressionFibre
phi34Over21PrimeFibre =
  Compression.prime-compression-fibre
    (Compression.primeExponent 2 (SSP.positiveMultiplicity 1) ∷
     Compression.primeExponent 17 (SSP.positiveMultiplicity 1) ∷
     Compression.primeExponent 3 (SSP.negativeMultiplicity 1) ∷
     Compression.primeExponent 7 (SSP.negativeMultiplicity 1) ∷ [])
    emptyResidual

phi2Over1Rich : RichDefectFibre
phi2Over1Rich =
  rich-defect-fibre 2 1 Triadic.positiveTrit 1 phi2Over1PrimeFibre

phi5Over3Rich : RichDefectFibre
phi5Over3Rich =
  rich-defect-fibre 5 3 Triadic.positiveTrit 1 phi5Over3PrimeFibre

phi13Over8Rich : RichDefectFibre
phi13Over8Rich =
  rich-defect-fibre 13 8 Triadic.positiveTrit 1 phi13Over8PrimeFibre

phi34Over21Rich : RichDefectFibre
phi34Over21Rich =
  rich-defect-fibre 34 21 Triadic.positiveTrit 1 phi34Over21PrimeFibre

normOneMagnitudesRetained :
  (defectMagnitude phi2Over1Rich ≡ 1) ×
  (defectMagnitude phi5Over3Rich ≡ 1) ×
  (defectMagnitude phi13Over8Rich ≡ 1) ×
  (defectMagnitude phi34Over21Rich ≡ 1)
normOneMagnitudesRetained = refl , refl , refl , refl

------------------------------------------------------------------------
-- 3. Rich six-line: strict nonzero sheet plus the complete payload.
------------------------------------------------------------------------

record RichSixLine : Set where
  constructor rich-six-line
  field
    payload : RichDefectFibre
    side : Compression.StrictSignedSide

open RichSixLine public

observe6 : RichSixLine → Fib369.FibSixLine
observe6 x = observe3 (payload x) , side x

flipRichSix : RichSixLine → RichSixLine
flipRichSix x =
  rich-six-line (flipRichObserver (payload x)) (Fib369.flipStrictSide (side x))

observe6Flip :
  ∀ x → observe6 (flipRichSix x) ≡ Fib369.fibSixFlip (observe6 x)
observe6Flip (rich-six-line f Compression.lowerSide) = refl
observe6Flip (rich-six-line f Compression.upperSide) = refl

richSixDeckTransformationAgreesWithExisting :
  ∀ x →
  Fib369.sixToExistingAxisLift (observe6 (flipRichSix x))
  ≡
  Hyper.flipAxisLift (Fib369.sixToExistingAxisLift (observe6 x))
richSixDeckTransformationAgreesWithExisting x =
  Fib369.fibSixFlipIsExistingDeckTransformation (observe6 x)

------------------------------------------------------------------------
-- 4. Rich nine-sheet: comparison without throwing away either payload.
------------------------------------------------------------------------

record RichComparisonSheet9 : Set where
  constructor rich-comparison-sheet9
  field
    current : RichDefectFibre
    next : RichDefectFibre

open RichComparisonSheet9 public

observe9 : RichComparisonSheet9 → Triadic.NineSheet
observe9 s = observe3 (current s) , observe3 (next s)

richFibComparison : RichDefectFibre → RichComparisonSheet9
richFibComparison f = rich-comparison-sheet9 f (flipRichObserver f)

observeRichFibComparison :
  ∀ f → observe9 (richFibComparison f) ≡ Fib369.fibComparison (observe3 f)
observeRichFibComparison f = refl

richComparisonRetainsCurrentMagnitude :
  ∀ f → defectMagnitude (current (richFibComparison f)) ≡ defectMagnitude f
richComparisonRetainsCurrentMagnitude f = refl

richComparisonRetainsNextMagnitude :
  ∀ f → defectMagnitude (next (richFibComparison f)) ≡ defectMagnitude f
richComparisonRetainsNextMagnitude f = refl

------------------------------------------------------------------------
-- 5. Rich 27-voxel: local three-step history with all fibres retained.
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

richFibVoxel : RichDefectFibre → RichVoxel27
richFibVoxel f =
  rich-voxel27 f (flipRichObserver f) f

observeRichFibVoxel :
  ∀ f → observe27 (richFibVoxel f) ≡ Fib369.fibVoxel (observe3 f)
observeRichFibVoxel f = refl

advanceRichVoxel : RichVoxel27 → RichVoxel27
advanceRichVoxel v =
  rich-voxel27
    (flipRichObserver (step0 v))
    (flipRichObserver (step1 v))
    (flipRichObserver (step2 v))

observeAdvanceRichVoxel :
  ∀ v → observe27 (advanceRichVoxel v) ≡ Fib369.negateVoxel (observe27 v)
observeAdvanceRichVoxel
  (rich-voxel27
    (rich-defect-fibre p0 q0 Triadic.negativeTrit m0 c0)
    (rich-defect-fibre p1 q1 Triadic.negativeTrit m1 c1)
    (rich-defect-fibre p2 q2 Triadic.negativeTrit m2 c2)) = refl
observeAdvanceRichVoxel
  (rich-voxel27
    (rich-defect-fibre p0 q0 Triadic.negativeTrit m0 c0)
    (rich-defect-fibre p1 q1 Triadic.negativeTrit m1 c1)
    (rich-defect-fibre p2 q2 Triadic.zeroTrit m2 c2)) = refl
observeAdvanceRichVoxel
  (rich-voxel27
    (rich-defect-fibre p0 q0 Triadic.negativeTrit m0 c0)
    (rich-defect-fibre p1 q1 Triadic.negativeTrit m1 c1)
    (rich-defect-fibre p2 q2 Triadic.positiveTrit m2 c2)) = refl
observeAdvanceRichVoxel
  (rich-voxel27
    (rich-defect-fibre p0 q0 Triadic.negativeTrit m0 c0)
    (rich-defect-fibre p1 q1 Triadic.zeroTrit m1 c1)
    (rich-defect-fibre p2 q2 Triadic.negativeTrit m2 c2)) = refl
observeAdvanceRichVoxel
  (rich-voxel27
    (rich-defect-fibre p0 q0 Triadic.negativeTrit m0 c0)
    (rich-defect-fibre p1 q1 Triadic.zeroTrit m1 c1)
    (rich-defect-fibre p2 q2 Triadic.zeroTrit m2 c2)) = refl
observeAdvanceRichVoxel
  (rich-voxel27
    (rich-defect-fibre p0 q0 Triadic.negativeTrit m0 c0)
    (rich-defect-fibre p1 q1 Triadic.zeroTrit m1 c1)
    (rich-defect-fibre p2 q2 Triadic.positiveTrit m2 c2)) = refl
observeAdvanceRichVoxel
  (rich-voxel27
    (rich-defect-fibre p0 q0 Triadic.negativeTrit m0 c0)
    (rich-defect-fibre p1 q1 Triadic.positiveTrit m1 c1)
    (rich-defect-fibre p2 q2 Triadic.negativeTrit m2 c2)) = refl
observeAdvanceRichVoxel
  (rich-voxel27
    (rich-defect-fibre p0 q0 Triadic.negativeTrit m0 c0)
    (rich-defect-fibre p1 q1 Triadic.positiveTrit m1 c1)
    (rich-defect-fibre p2 q2 Triadic.zeroTrit m2 c2)) = refl
observeAdvanceRichVoxel
  (rich-voxel27
    (rich-defect-fibre p0 q0 Triadic.negativeTrit m0 c0)
    (rich-defect-fibre p1 q1 Triadic.positiveTrit m1 c1)
    (rich-defect-fibre p2 q2 Triadic.positiveTrit m2 c2)) = refl
observeAdvanceRichVoxel
  (rich-voxel27
    (rich-defect-fibre p0 q0 Triadic.zeroTrit m0 c0)
    (rich-defect-fibre p1 q1 Triadic.negativeTrit m1 c1)
    (rich-defect-fibre p2 q2 Triadic.negativeTrit m2 c2)) = refl
observeAdvanceRichVoxel
  (rich-voxel27
    (rich-defect-fibre p0 q0 Triadic.zeroTrit m0 c0)
    (rich-defect-fibre p1 q1 Triadic.negativeTrit m1 c1)
    (rich-defect-fibre p2 q2 Triadic.zeroTrit m2 c2)) = refl
observeAdvanceRichVoxel
  (rich-voxel27
    (rich-defect-fibre p0 q0 Triadic.zeroTrit m0 c0)
    (rich-defect-fibre p1 q1 Triadic.negativeTrit m1 c1)
    (rich-defect-fibre p2 q2 Triadic.positiveTrit m2 c2)) = refl
observeAdvanceRichVoxel
  (rich-voxel27
    (rich-defect-fibre p0 q0 Triadic.zeroTrit m0 c0)
    (rich-defect-fibre p1 q1 Triadic.zeroTrit m1 c1)
    (rich-defect-fibre p2 q2 Triadic.negativeTrit m2 c2)) = refl
observeAdvanceRichVoxel
  (rich-voxel27
    (rich-defect-fibre p0 q0 Triadic.zeroTrit m0 c0)
    (rich-defect-fibre p1 q1 Triadic.zeroTrit m1 c1)
    (rich-defect-fibre p2 q2 Triadic.zeroTrit m2 c2)) = refl
observeAdvanceRichVoxel
  (rich-voxel27
    (rich-defect-fibre p0 q0 Triadic.zeroTrit m0 c0)
    (rich-defect-fibre p1 q1 Triadic.zeroTrit m1 c1)
    (rich-defect-fibre p2 q2 Triadic.positiveTrit m2 c2)) = refl
observeAdvanceRichVoxel
  (rich-voxel27
    (rich-defect-fibre p0 q0 Triadic.zeroTrit m0 c0)
    (rich-defect-fibre p1 q1 Triadic.positiveTrit m1 c1)
    (rich-defect-fibre p2 q2 Triadic.negativeTrit m2 c2)) = refl
observeAdvanceRichVoxel
  (rich-voxel27
    (rich-defect-fibre p0 q0 Triadic.zeroTrit m0 c0)
    (rich-defect-fibre p1 q1 Triadic.positiveTrit m1 c1)
    (rich-defect-fibre p2 q2 Triadic.zeroTrit m2 c2)) = refl
observeAdvanceRichVoxel
  (rich-voxel27
    (rich-defect-fibre p0 q0 Triadic.zeroTrit m0 c0)
    (rich-defect-fibre p1 q1 Triadic.positiveTrit m1 c1)
    (rich-defect-fibre p2 q2 Triadic.positiveTrit m2 c2)) = refl
observeAdvanceRichVoxel
  (rich-voxel27
    (rich-defect-fibre p0 q0 Triadic.positiveTrit m0 c0)
    (rich-defect-fibre p1 q1 Triadic.negativeTrit m1 c1)
    (rich-defect-fibre p2 q2 Triadic.negativeTrit m2 c2)) = refl
observeAdvanceRichVoxel
  (rich-voxel27
    (rich-defect-fibre p0 q0 Triadic.positiveTrit m0 c0)
    (rich-defect-fibre p1 q1 Triadic.negativeTrit m1 c1)
    (rich-defect-fibre p2 q2 Triadic.zeroTrit m2 c2)) = refl
observeAdvanceRichVoxel
  (rich-voxel27
    (rich-defect-fibre p0 q0 Triadic.positiveTrit m0 c0)
    (rich-defect-fibre p1 q1 Triadic.negativeTrit m1 c1)
    (rich-defect-fibre p2 q2 Triadic.positiveTrit m2 c2)) = refl
observeAdvanceRichVoxel
  (rich-voxel27
    (rich-defect-fibre p0 q0 Triadic.positiveTrit m0 c0)
    (rich-defect-fibre p1 q1 Triadic.zeroTrit m1 c1)
    (rich-defect-fibre p2 q2 Triadic.negativeTrit m2 c2)) = refl
observeAdvanceRichVoxel
  (rich-voxel27
    (rich-defect-fibre p0 q0 Triadic.positiveTrit m0 c0)
    (rich-defect-fibre p1 q1 Triadic.zeroTrit m1 c1)
    (rich-defect-fibre p2 q2 Triadic.zeroTrit m2 c2)) = refl
observeAdvanceRichVoxel
  (rich-voxel27
    (rich-defect-fibre p0 q0 Triadic.positiveTrit m0 c0)
    (rich-defect-fibre p1 q1 Triadic.zeroTrit m1 c1)
    (rich-defect-fibre p2 q2 Triadic.positiveTrit m2 c2)) = refl
observeAdvanceRichVoxel
  (rich-voxel27
    (rich-defect-fibre p0 q0 Triadic.positiveTrit m0 c0)
    (rich-defect-fibre p1 q1 Triadic.positiveTrit m1 c1)
    (rich-defect-fibre p2 q2 Triadic.negativeTrit m2 c2)) = refl
observeAdvanceRichVoxel
  (rich-voxel27
    (rich-defect-fibre p0 q0 Triadic.positiveTrit m0 c0)
    (rich-defect-fibre p1 q1 Triadic.positiveTrit m1 c1)
    (rich-defect-fibre p2 q2 Triadic.zeroTrit m2 c2)) = refl
observeAdvanceRichVoxel
  (rich-voxel27
    (rich-defect-fibre p0 q0 Triadic.positiveTrit m0 c0)
    (rich-defect-fibre p1 q1 Triadic.positiveTrit m1 c1)
    (rich-defect-fibre p2 q2 Triadic.positiveTrit m2 c2)) = refl

advanceRichVoxelPreservesAllMagnitudes :
  ∀ v →
  (defectMagnitude (step0 (advanceRichVoxel v)) ≡ defectMagnitude (step0 v)) ×
  (defectMagnitude (step1 (advanceRichVoxel v)) ≡ defectMagnitude (step1 v)) ×
  (defectMagnitude (step2 (advanceRichVoxel v)) ≡ defectMagnitude (step2 v))
advanceRichVoxelPreservesAllMagnitudes v = refl , refl , refl

------------------------------------------------------------------------
-- 6. Frontier.
------------------------------------------------------------------------

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
