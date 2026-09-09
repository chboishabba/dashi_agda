module DASHI.Moonshine.GoldenRatioBalancedTernaryFRACTRANModularPathExact where

------------------------------------------------------------------------
-- BALANCED-TERNARY FRACTRAN CONTROL -> EXACT FIBONACCI TWO-STEP PATH
--
-- The golden-ratio lane is made repo-native here: the control alphabet is not
-- an external binary machine.  We reuse SignedSSPFRACTRANWeaveExact's native
-- signed multiplicities and project them to the canonical balanced trit.
--
-- On a two-register Nat fibre:
--   - (negative/converging) acts by the lower shear L,
--   0 acts as fibre identity,
--   + (positive/diverging) acts by the upper shear T.
--
-- The signed macro word [-,+] is exactly TWO Fibonacci updates on the pair
-- convention (F_(n+1), F_n).  Repeating that balanced-ternary word therefore
-- generates the even-step Fibonacci subsequence entirely inside the signed
-- FRACTRAN observer semantics.  The remaining phi claim is analytic: construct
-- a positive real ratio carrier and prove convergence to the positive root of
-- x^2 = x + 1.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic
import DASHI.Biology.SignedSSPFRACTRANWeaveExact as SSP
import DASHI.Moonshine.JInvariantOrderThreeOrbitBalancedTernaryBidiExact as Orbit

------------------------------------------------------------------------
-- 1. Fibonacci pair carrier.
------------------------------------------------------------------------

record FibPair : Set where
  constructor fibPair
  field
    hi lo : Nat

open FibPair public

-- Pair convention: (F_(n+1), F_n).
fibStep : FibPair → FibPair
fibStep (fibPair a b) = fibPair (a + b) a

fibStart : FibPair
fibStart = fibPair 1 0

fib1 : fibStep fibStart ≡ fibPair 1 1
fib1 = refl

fib2 : fibStep (fibStep fibStart) ≡ fibPair 2 1
fib2 = refl

------------------------------------------------------------------------
-- 2. Balanced-trit actions induced by signed FRACTRAN multiplicity.
------------------------------------------------------------------------

lowerPairShear : FibPair → FibPair
lowerPairShear (fibPair a b) = fibPair a (a + b)

upperPairShear : FibPair → FibPair
upperPairShear (fibPair a b) = fibPair (b + a) b

tritPairAction : Triadic.KernelTrit → FibPair → FibPair
tritPairAction Triadic.negativeTrit = lowerPairShear
tritPairAction Triadic.zeroTrit p = p
tritPairAction Triadic.positiveTrit = upperPairShear

multiplicityPairAction : SSP.SignedMultiplicity → FibPair → FibPair
multiplicityPairAction m = tritPairAction (SSP.coarseMultiplicity m)

negativeFibToken : SSP.SignedMultiplicity
negativeFibToken = SSP.negativeMultiplicity 1

positiveFibToken : SSP.SignedMultiplicity
positiveFibToken = SSP.positiveMultiplicity 1

neutralFibToken : SSP.SignedMultiplicity
neutralFibToken = SSP.zeroMultiplicity

negativeFibTokenIsConverging :
  Orbit.seamDynamicsOfMultiplicity negativeFibToken ≡ Orbit.convergingSeam
negativeFibTokenIsConverging = refl

positiveFibTokenIsDiverging :
  Orbit.seamDynamicsOfMultiplicity positiveFibToken ≡ Orbit.divergingSeam
positiveFibTokenIsDiverging = refl

neutralFibTokenIsIdentity :
  Orbit.seamDynamicsOfMultiplicity neutralFibToken ≡ Orbit.seamIdentity
neutralFibTokenIsIdentity = refl

------------------------------------------------------------------------
-- 3. Exact theorem: [-,+] = two Fibonacci steps.
------------------------------------------------------------------------

balancedFibMacro : FibPair → FibPair
balancedFibMacro p =
  multiplicityPairAction positiveFibToken
    (multiplicityPairAction negativeFibToken p)

balancedFibMacroIsTwoFibSteps :
  (p : FibPair) → balancedFibMacro p ≡ fibStep (fibStep p)
balancedFibMacroIsTwoFibSteps (fibPair a b) = refl

balancedFibMacroStart : balancedFibMacro fibStart ≡ fibPair 2 1
balancedFibMacroStart = refl

balancedFibMacroTwice :
  balancedFibMacro (balancedFibMacro fibStart) ≡ fibPair 5 3
balancedFibMacroTwice = refl

balancedFibMacroThrice :
  balancedFibMacro
    (balancedFibMacro (balancedFibMacro fibStart))
  ≡ fibPair 13 8
balancedFibMacroThrice = refl

balancedFibMacroFourTimes :
  balancedFibMacro
    (balancedFibMacro
      (balancedFibMacro (balancedFibMacro fibStart)))
  ≡ fibPair 34 21
balancedFibMacroFourTimes = refl

------------------------------------------------------------------------
-- 4. Recursive execution on the signed fibre.
------------------------------------------------------------------------

iterateBalancedFib : Nat → FibPair → FibPair
iterateBalancedFib zero p = p
iterateBalancedFib (suc n) p = iterateBalancedFib n (balancedFibMacro p)

balancedFibDepth0 : iterateBalancedFib 0 fibStart ≡ fibPair 1 0
balancedFibDepth0 = refl

balancedFibDepth1 : iterateBalancedFib 1 fibStart ≡ fibPair 2 1
balancedFibDepth1 = refl

balancedFibDepth2 : iterateBalancedFib 2 fibStart ≡ fibPair 5 3
balancedFibDepth2 = refl

balancedFibDepth3 : iterateBalancedFib 3 fibStart ≡ fibPair 13 8
balancedFibDepth3 = refl

balancedFibDepth4 : iterateBalancedFib 4 fibStart ≡ fibPair 34 21
balancedFibDepth4 = refl

------------------------------------------------------------------------
-- 5. Introspective meaning.
--
-- The same balanced alphabet has two distinct paths now:
--
--   j cusp seam:      + followed by repeated -    (L^k T)
--   Fibonacci path:   repeated [-,+] macros       ((T L)^n)
--
-- Their finite recurrences are different.  Hence phi must not be forced onto
-- the quadratic k^2+k+1 cusp family; it belongs to the alternating path if the
-- analytic ratio theorem is paid.
------------------------------------------------------------------------

data GoldenRatioFibreResidual : Set where
  missingPositiveRealRatioCarrier : GoldenRatioFibreResidual
  missingBalancedFibRatioConvergence : GoldenRatioFibreResidual
  missingPositiveRootUniqueness : GoldenRatioFibreResidual
  missingVisualScaleSameObjectIdentification : GoldenRatioFibreResidual

firstGoldenRatioFibreResidual : GoldenRatioFibreResidual
firstGoldenRatioFibreResidual = missingPositiveRealRatioCarrier

record GoldenRatioBalancedFRACTRANFrontier : Set where
  constructor golden-ratio-balanced-fractran-frontier
  field
    signedFRACTRANIsPrimitiveControl : Bool
    binaryFibonacciMachineRequired : Bool
    balancedMacroEqualsTwoFibSteps : Bool
    exactFiniteRatiosAvailable : Bool
    realPhiLimitProved : Bool
    firstResidual : GoldenRatioFibreResidual

canonicalGoldenRatioBalancedFRACTRANFrontier :
  GoldenRatioBalancedFRACTRANFrontier
canonicalGoldenRatioBalancedFRACTRANFrontier =
  golden-ratio-balanced-fractran-frontier
    true false true true false firstGoldenRatioFibreResidual
