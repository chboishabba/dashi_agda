module DASHI.Moonshine.JInvariantOrderThreeSeamModularWordExact where

------------------------------------------------------------------------
-- EXACT MODULAR WORD FOR THE ORDER-THREE j SEAM FAMILY
--
-- The previously constructed symbolic family
--
--   gamma_k = [ 1  1 ; k  k+1 ]
--
-- is not an arbitrary matrix sequence.  It is generated exactly by the two
-- standard integral shear actions
--
--   T = [1 1; 0 1]      and      L = [1 0; 1 1]
--
-- via gamma_0 = T and gamma_(k+1) = L gamma_k.  Hence gamma_k = L^k T in the
-- recursive word sense.  We interpret T/L only through the repository's
-- already-native signed FRACTRAN multiplicities:
--
--   positive multiplicity -> + -> diverging/commuting observer -> T
--   zero multiplicity     -> 0 -> fibre identity
--   negative multiplicity -> - -> converging/anti observer   -> L
--
-- This derives the exact finite/symbolic modular word behind the seam family.
-- It still does NOT identify these symbolic shears with the analytic Mobius
-- action used by the rendered j-image; that same-object bridge remains typed.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic
import DASHI.Biology.SignedSSPFRACTRANWeaveExact as SSP
import DASHI.Moonshine.JInvariantOrderThreeOrbitBalancedTernaryBidiExact as Orbit

------------------------------------------------------------------------
-- 1. Minimal Nat matrix carrier for the exact word calculation.
------------------------------------------------------------------------

record NatMatrix2 : Set where
  constructor matrix2
  field
    a b c d : Nat

open NatMatrix2 public

identityMatrix : NatMatrix2
identityMatrix = matrix2 1 0 0 1

upperShearT : NatMatrix2
upperShearT = matrix2 1 1 0 1

-- Left multiplication by L = [1 0; 1 1].
lowerShearL : NatMatrix2 → NatMatrix2
lowerShearL (matrix2 a b c d) = matrix2 a b (a + c) (b + d)

-- Left multiplication by T = [1 1; 0 1].
upperShearAction : NatMatrix2 → NatMatrix2
upperShearAction (matrix2 a b c d) = matrix2 (a + c) (b + d) c d

------------------------------------------------------------------------
-- 2. Closed family and exact L^k T recursion.
------------------------------------------------------------------------

gammaClosed : Nat → NatMatrix2
gammaClosed k = matrix2 1 1 k (suc k)

gammaClosedZeroIsT : gammaClosed 0 ≡ upperShearT
gammaClosedZeroIsT = refl

gammaClosedStep : (k : Nat) →
  lowerShearL (gammaClosed k) ≡ gammaClosed (suc k)
gammaClosedStep k = refl

gammaWord : Nat → NatMatrix2
gammaWord zero = upperShearT
gammaWord (suc k) = lowerShearL (gammaWord k)

gammaWordIsClosedFamily : (k : Nat) → gammaWord k ≡ gammaClosed k
gammaWordIsClosedFamily zero = refl
gammaWordIsClosedFamily (suc k) rewrite gammaWordIsClosedFamily k = gammaClosedStep k

gammaBottomRowMatchesOrbitIndex : (k : Nat) →
  c (gammaWord k) ≡ k × d (gammaWord k) ≡ suc k
gammaBottomRowMatchesOrbitIndex k rewrite gammaWordIsClosedFamily k = refl , refl

------------------------------------------------------------------------
-- 3. Same balanced-ternary/FRACTRAN sign carrier controls the two shears.
------------------------------------------------------------------------

positiveShearToken : SSP.SignedMultiplicity
positiveShearToken = SSP.positiveMultiplicity 1

negativeShearToken : SSP.SignedMultiplicity
negativeShearToken = SSP.negativeMultiplicity 1

neutralShearToken : SSP.SignedMultiplicity
neutralShearToken = SSP.zeroMultiplicity

signedShearAction : SSP.SignedMultiplicity → NatMatrix2 → NatMatrix2
signedShearAction m M with SSP.coarseMultiplicity m
... | Triadic.negativeTrit = lowerShearL M
... | Triadic.zeroTrit = M
... | Triadic.positiveTrit = upperShearAction M

positiveTokenIsDiverging :
  Orbit.seamDynamicsOfMultiplicity positiveShearToken ≡ Orbit.divergingSeam
positiveTokenIsDiverging = refl

negativeTokenIsConverging :
  Orbit.seamDynamicsOfMultiplicity negativeShearToken ≡ Orbit.convergingSeam
negativeTokenIsConverging = refl

neutralTokenIsFibreIdentity :
  Orbit.seamDynamicsOfMultiplicity neutralShearToken ≡ Orbit.seamIdentity
neutralTokenIsFibreIdentity = refl

positiveTokenProducesTFromIdentity :
  signedShearAction positiveShearToken identityMatrix ≡ upperShearT
positiveTokenProducesTFromIdentity = refl

negativeTokenAdvancesSeamFamily : (k : Nat) →
  signedShearAction negativeShearToken (gammaClosed k) ≡ gammaClosed (suc k)
negativeTokenAdvancesSeamFamily = gammaClosedStep

------------------------------------------------------------------------
-- 4. Rendering decimal is an observer coordinate, not the exact rho height.
--
-- 0.866025 = 34641/40000 exactly as a finite decimal.  Its square lies just
-- below 3/4; the exact analytic ordinate remains sqrt(3)/2.
------------------------------------------------------------------------

renderedRhoHeightNumerator : Nat
renderedRhoHeightNumerator = 34641

renderedRhoHeightDenominator : Nat
renderedRhoHeightDenominator = 40000

renderedRhoHeightSquareDefect :
  4 * renderedRhoHeightNumerator * renderedRhoHeightNumerator + 4476
  ≡
  3 * renderedRhoHeightDenominator * renderedRhoHeightDenominator
renderedRhoHeightSquareDefect = refl

------------------------------------------------------------------------
-- 5. BIDI frontier after deriving the word.
------------------------------------------------------------------------

data SeamWordResidual : Set where
  missingAnalyticLowerShearSameObjectAction : SeamWordResidual
  missingAnalyticUpperShearSameObjectAction : SeamWordResidual
  missingRenderedBeamWordIdentification : SeamWordResidual
  missingActualRefinementGluingSquare : SeamWordResidual

firstSeamWordResidual : SeamWordResidual
firstSeamWordResidual = missingAnalyticLowerShearSameObjectAction

record SeamWordFrontier : Set where
  constructor seam-word-frontier
  field
    exactLPowerTWordDerived : Bool
    balancedTernaryFRACTRANControlDerived : Bool
    closedMatrixFamilyMatchesOrbitIndex : Bool
    decimalObserverKeptSeparateFromExactRootCarrier : Bool
    analyticMobiusSameObjectPaid : Bool
    firstResidual : SeamWordResidual

canonicalSeamWordFrontier : SeamWordFrontier
canonicalSeamWordFrontier =
  seam-word-frontier true true true true false firstSeamWordResidual
