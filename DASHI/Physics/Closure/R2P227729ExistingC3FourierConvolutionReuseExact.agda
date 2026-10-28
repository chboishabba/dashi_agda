module DASHI.Physics.Closure.R2P227729ExistingC3FourierConvolutionReuseExact where

------------------------------------------------------------------------
-- REUSE-ONLY FINITE FOURIER AUTHORITY WITH NEW 27-MODE FUNCTION CHART.
--
-- Original mathematical / DASHI proof owners:
--   Biology.Physical.C3CubeCyclotomicFourierExact
--       exact 27-point C3^3 DFT and two-sided inverse;
--   Biology.Physical.C3CubeCyclotomicParsevalExact
--       cyclotomic unnormalised and normalised Parseval;
--   Biology.Physical.C3CubeDirectGroupConvolutionExact
--       direct CYCLIC convolution and its exact Fourier theorem.
--
-- NEW CHART: a scalar function on the 27 signed Fourier *labels*
-- is bijective (by packing/unpacking) with the original CubeSignal.
-- The source transform therefore applies without being re-proved.
--
-- CRITICAL: the original cyclic product is modulo 3 in EACH axis,
-- whereas physical integer Fourier / Galerkin convolution uses
-- k=p+q IN Z^3. That is the exact aliased-vs-Galerkin seam, not a
-- missing DFT theorem. A 27-element finite group is not a proof of
-- the 5x5x5 padded sampling operator, NS regularity or Monster 3B.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
import Data.Rational.Base as Q

import DASHI.Physics.Closure.R2P2ThreeModeBinaryTernaryNSAliasingCutExact as M
import DASHI.Physics.Closure.R2P227729FourierObserverIncidenceExact as I
import DASHI.Biology.Physical.C3CubeCyclotomicFourierExact as F
import DASHI.Biology.Physical.C3CubeCyclotomicParsevalExact as P
import DASHI.Biology.Physical.C3CubeDirectGroupConvolutionExact as C

tripleFromModes : ∀ {A : Set} → (M.ThreeMode → A) → F.Triple A
tripleFromModes f =
  F.triple (f M.modeMinus) (f M.modeZero) (f M.modePlus)

lookupTriple : ∀ {A : Set} → F.Triple A → M.ThreeMode → A
lookupTriple (F.triple a b c) M.modeMinus = a
lookupTriple (F.triple a b c) M.modeZero = b
lookupTriple (F.triple a b c) M.modePlus = c

lookupAfterTriple :
  ∀ {A : Set} (f : M.ThreeMode → A) (m : M.ThreeMode) →
  lookupTriple (tripleFromModes f) m ≡ f m
lookupAfterTriple f M.modeMinus = refl
lookupAfterTriple f M.modeZero = refl
lookupAfterTriple f M.modePlus = refl

tripleAfterLookup :
  ∀ {A : Set} (values : F.Triple A) →
  tripleFromModes (lookupTriple values) ≡ values
tripleAfterLookup (F.triple a b c) = refl

ModeCoefficient27 : Set
ModeCoefficient27 = I.ModeCube27 → F.Cyclotomic3

packModeSignal : ModeCoefficient27 → F.CubeSignal
packModeSignal amplitude =
  tripleFromModes (λ a →
    tripleFromModes (λ b →
      tripleFromModes (λ c →
        amplitude (I.modeCube a b c))))

unpackModeSignal : F.CubeSignal → ModeCoefficient27
unpackModeSignal signal (I.modeCube a b c) =
  lookupTriple (lookupTriple (lookupTriple signal a) b) c

unpackAfterPack :
  (f : ModeCoefficient27) (m : I.ModeCube27) →
  unpackModeSignal (packModeSignal f) m ≡ f m
unpackAfterPack f (I.modeCube a b c)
  rewrite lookupAfterTriple
    (λ a' → tripleFromModes
      (λ b' → tripleFromModes (λ c' → f (I.modeCube a' b' c')))) a
        | lookupAfterTriple
          (λ b' → tripleFromModes (λ c' → f (I.modeCube a b' c'))) b
        | lookupAfterTriple (λ c' → f (I.modeCube a b c')) c = refl

packAfterUnpack : (signal : F.CubeSignal) →
  packModeSignal (unpackModeSignal signal) ≡ signal
packAfterUnpack
  (F.triple
    (F.triple (F.triple a000 a001 a002)
              (F.triple a010 a011 a012)
              (F.triple a020 a021 a022))
    (F.triple (F.triple a100 a101 a102)
              (F.triple a110 a111 a112)
              (F.triple a120 a121 a122))
    (F.triple (F.triple a200 a201 a202)
              (F.triple a210 a211 a212)
              (F.triple a220 a221 a222))) = refl

-- The theorem below is a transport of the original *periodic* DFT
-- inverse. This is not a fresh proof of 27-point orthogonality.
existingPeriodic27FourierRoundTrip :
  (f : ModeCoefficient27) (m : I.ModeCube27) →
  unpackModeSignal
    (F.inverseFourier27 (F.fourier27 (packModeSignal f))) m
    ≡ f m
existingPeriodic27FourierRoundTrip f m
  rewrite F.cubeFourierInversion (packModeSignal f)
        | unpackAfterPack f m = refl

existingPeriodic27FourierForwardInverse :
  (signal : F.CubeSignal) →
  F.fourier27 (F.inverseFourier27 signal) ≡ signal
existingPeriodic27FourierForwardInverse = F.cubeFourierForwardInverse

existingCyclic27DirectConvolutionTheorem :
  (f g : F.CubeSignal) →
  F.fourier27 (C.convolution3 f g)
    ≡ C.pointwise3 (F.fourier27 f) (F.fourier27 g)
existingCyclic27DirectConvolutionTheorem =
  C.c3CubeDirectConvolutionTheorem

existingCyclic27ConvolutionEqualsSpectral :
  (f g : F.CubeSignal) →
  C.convolution3 f g ≡ F.spectralConvolution f g
existingCyclic27ConvolutionEqualsSpectral =
  C.directEqualsSpectralConvolution

existingCyclic27Parseval :
  (signal : F.CubeSignal) →
  Q._*_ P.twentySeventh (P.energy3 (F.fourier27 signal))
    ≡ P.energy3 signal
existingCyclic27Parseval = P.cubeParsevalNormalised

-- EXISTING DFT applies to the quotient, not to the true high-frequency
-- integer output. This is the concrete alias witness to transport around.
cyclicC3ConvolutionCanAliasIntegerPlusTwo :
  M.periodicQuadraticModeSum M.modePlus M.modePlus ≡ M.modeMinus
cyclicC3ConvolutionCanAliasIntegerPlusTwo =
  M.positivePositiveAliasesToNegative
