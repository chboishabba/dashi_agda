module DASHI.Moonshine.QuadraticIrrationalSignedApproximationFibreExact where

------------------------------------------------------------------------
-- QUADRATIC-IRRATIONAL APPROXIMATION AS A BALANCED SIGNED FIBRE
--
-- Representation and approximation are intentionally separate coordinates.
-- A rational p/q may be represented by signed prime valuations (the existing
-- signed-FRACTRAN lane), while a quadratic norm defect determines whether the
-- rational lies on the under / exact / over side of the algebraic target.
--
-- This owner stays finite/exact.  It does not construct another real number:
-- the analytic target remains the already-owned Bishop real square-root carrier
-- (and the existing phi carrier once its live derivation is paid).
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic

------------------------------------------------------------------------
-- 1. Generic balanced direction observer.
------------------------------------------------------------------------

data ApproximationDirection : Set where
  belowTarget : ApproximationDirection
  exactTarget : ApproximationDirection
  aboveTarget : ApproximationDirection

directionTrit : ApproximationDirection → Triadic.KernelTrit
directionTrit belowTarget = Triadic.negativeTrit
directionTrit exactTarget = Triadic.zeroTrit
directionTrit aboveTarget = Triadic.positiveTrit

------------------------------------------------------------------------
-- 2. sqrt(3)/2 defect certificates.
--
-- D(p,q) = 4 p^2 - 3 q^2.
-- Rather than introducing signed integer normalization here, store the exact
-- Nat equality witnessing which side of zero the defect occupies.
------------------------------------------------------------------------

data SqrtThreeHalfDefect (p q : Nat) : Set where
  defectBelow : (delta : Nat) → 4 * p * p + delta ≡ 3 * q * q →
                SqrtThreeHalfDefect p q
  defectExact : 4 * p * p ≡ 3 * q * q →
                SqrtThreeHalfDefect p q
  defectAbove : (delta : Nat) → 4 * p * p ≡ 3 * q * q + delta →
                SqrtThreeHalfDefect p q

sqrtThreeHalfDirection :
  {p q : Nat} → SqrtThreeHalfDefect p q → ApproximationDirection
sqrtThreeHalfDirection (defectBelow delta eq) = belowTarget
sqrtThreeHalfDirection (defectExact eq) = exactTarget
sqrtThreeHalfDirection (defectAbove delta eq) = aboveTarget

sqrtThreeHalfTrit :
  {p q : Nat} → SqrtThreeHalfDefect p q → Triadic.KernelTrit
sqrtThreeHalfTrit d = directionTrit (sqrtThreeHalfDirection d)

-- The decimal rendering 0.866025 = 34641 / 40000 is exactly below the target
-- with square-defect magnitude 4476.
decimal866025Defect : SqrtThreeHalfDefect 34641 40000
decimal866025Defect = defectBelow 4476 refl

decimal866025IsNegativeTrit :
  sqrtThreeHalfTrit decimal866025Defect ≡ Triadic.negativeTrit
decimal866025IsNegativeTrit = refl

-- Representative Pell/continued-fraction fibres.
sqrt3Below6Over7 : SqrtThreeHalfDefect 6 7
sqrt3Below6Over7 = defectBelow 3 refl

sqrt3Above13Over15 : SqrtThreeHalfDefect 13 15
sqrt3Above13Over15 = defectAbove 1 refl

sqrt3Below84Over97 : SqrtThreeHalfDefect 84 97
sqrt3Below84Over97 = defectBelow 3 refl

sqrt3Above181Over209 : SqrtThreeHalfDefect 181 209
sqrt3Above181Over209 = defectAbove 1 refl

sqrt3Below1170Over1351 : SqrtThreeHalfDefect 1170 1351
sqrt3Below1170Over1351 = defectBelow 3 refl

sqrt3Above2521Over2911 : SqrtThreeHalfDefect 2521 2911
sqrt3Above2521Over2911 = defectAbove 1 refl

sqrt3AlternatingSigns :
  (sqrtThreeHalfTrit sqrt3Below6Over7 ≡ Triadic.negativeTrit) ×
  (sqrtThreeHalfTrit sqrt3Above13Over15 ≡ Triadic.positiveTrit) ×
  (sqrtThreeHalfTrit sqrt3Below84Over97 ≡ Triadic.negativeTrit) ×
  (sqrtThreeHalfTrit sqrt3Above181Over209 ≡ Triadic.positiveTrit)
sqrt3AlternatingSigns = refl , refl , refl , refl

------------------------------------------------------------------------
-- 3. Golden-ratio Cassini defect certificates.
--
-- D_phi(p,q) = p^2 - p q - q^2.
------------------------------------------------------------------------

data GoldenRatioDefect (p q : Nat) : Set where
  phiBelow : (delta : Nat) → p * p + delta ≡ p * q + q * q →
             GoldenRatioDefect p q
  phiExact : p * p ≡ p * q + q * q →
             GoldenRatioDefect p q
  phiAbove : (delta : Nat) → p * p ≡ p * q + q * q + delta →
             GoldenRatioDefect p q

goldenRatioDirection :
  {p q : Nat} → GoldenRatioDefect p q → ApproximationDirection
goldenRatioDirection (phiBelow delta eq) = belowTarget
goldenRatioDirection (phiExact eq) = exactTarget
goldenRatioDirection (phiAbove delta eq) = aboveTarget

goldenRatioTrit :
  {p q : Nat} → GoldenRatioDefect p q → Triadic.KernelTrit
goldenRatioTrit d = directionTrit (goldenRatioDirection d)

-- The existing balanced-FRACTRAN even-step Fibonacci path lies on D_phi = +1.
phi2Over1 : GoldenRatioDefect 2 1
phi2Over1 = phiAbove 1 refl

phi5Over3 : GoldenRatioDefect 5 3
phi5Over3 = phiAbove 1 refl

phi13Over8 : GoldenRatioDefect 13 8
phi13Over8 = phiAbove 1 refl

phi34Over21 : GoldenRatioDefect 34 21
phi34Over21 = phiAbove 1 refl

balancedFibPathStaysPositive :
  (goldenRatioTrit phi2Over1 ≡ Triadic.positiveTrit) ×
  (goldenRatioTrit phi5Over3 ≡ Triadic.positiveTrit) ×
  (goldenRatioTrit phi13Over8 ≡ Triadic.positiveTrit) ×
  (goldenRatioTrit phi34Over21 ≡ Triadic.positiveTrit)
balancedFibPathStaysPositive = refl , refl , refl , refl

------------------------------------------------------------------------
-- 4. Introspective frontier.
------------------------------------------------------------------------

data QuadraticApproximationResidual : Set where
  missingPrimeValuationCompressionWeld : QuadraticApproximationResidual
  missingBoundedDefectDenominatorGrowthConvergence : QuadraticApproximationResidual
  missingSameBishopCarrierIdentification : QuadraticApproximationResidual
  missingCodecAdmissibilityOptimality : QuadraticApproximationResidual

record QuadraticSignedApproximationFrontier : Set where
  constructor quadratic-signed-approximation-frontier
  field
    balancedDirectionObserverExact : Bool
    decimalCodecWitnessExact : Bool
    pellAlternationExact : Bool
    cassiniNormOneFibreExact : Bool
    newRealCarrierRequired : Bool
    convergenceOnBishopCarrierProved : Bool
    firstResidual : QuadraticApproximationResidual

canonicalQuadraticSignedApproximationFrontier :
  QuadraticSignedApproximationFrontier
canonicalQuadraticSignedApproximationFrontier =
  quadratic-signed-approximation-frontier
    true true true true false false
    missingPrimeValuationCompressionWeld
