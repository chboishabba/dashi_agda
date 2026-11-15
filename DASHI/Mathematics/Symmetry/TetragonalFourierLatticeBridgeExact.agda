module DASHI.Mathematics.Symmetry.TetragonalFourierLatticeBridgeExact where

-- Native FourierMode carrier from the Navier–Stokes closure corpus,
-- transported through the shared integral D4h signed-coordinate
-- representation. No physical frequency calibration or Bloch
-- Hamiltonian is asserted here.
--
-- Classical crystal symmetry / Fourier duality prior art. This is
-- source-preserving cross-module formalisation.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Data.Integer using (ℤ; _+_)
import Data.Integer.Properties as IntP
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as NS
import DASHI.Mathematics.Symmetry.TetragonalD4hNormalFormExact as D
import DASHI.Mathematics.Symmetry.TetragonalIntegralLatticeActionExact as T
import DASHI.Mathematics.Symmetry.TetragonalIntegerMetricPairingExact as Metric

fromMode : NS.FourierMode → T.Triple ℤ
fromMode (NS.mode x y z) = T.xyz x y z

toMode : T.Triple ℤ → NS.FourierMode
toMode (T.xyz x y z) = NS.mode x y z

modeRoundTrip : (p : NS.FourierMode) → toMode (fromMode p) ≡ p
modeRoundTrip (NS.mode x y z) = refl

tripleRoundTrip : (p : T.Triple ℤ) → fromMode (toMode p) ≡ p
tripleRoundTrip (T.xyz x y z) = refl

add3 : T.Triple ℤ → T.Triple ℤ → T.Triple ℤ
add3 (T.xyz x y z) (T.xyz u v w) =
  T.xyz (x + u) (y + v) (z + w)

fromModeAdd : (p q : NS.FourierMode) →
  fromMode (NS.addMode p q) ≡ add3 (fromMode p) (fromMode q)
fromModeAdd (NS.mode x y z) (NS.mode u v w) = refl

rotateAdd : (p q : T.Triple ℤ) →
  T.R Metric.integerSignedCarrier (add3 p q) ≡
  add3 (T.R Metric.integerSignedCarrier p)
       (T.R Metric.integerSignedCarrier q)
rotateAdd (T.xyz x y z) (T.xyz u v w)
  rewrite IntP.neg-distrib-+ y v = refl

verticalAdd : (p q : T.Triple ℤ) →
  T.V Metric.integerSignedCarrier (add3 p q) ≡
  add3 (T.V Metric.integerSignedCarrier p)
       (T.V Metric.integerSignedCarrier q)
verticalAdd (T.xyz x y z) (T.xyz u v w)
  rewrite IntP.neg-distrib-+ y v = refl

horizontalAdd : (p q : T.Triple ℤ) →
  T.H Metric.integerSignedCarrier (add3 p q) ≡
  add3 (T.H Metric.integerSignedCarrier p)
       (T.H Metric.integerSignedCarrier q)
horizontalAdd (T.xyz x y z) (T.xyz u v w)
  rewrite IntP.neg-distrib-+ z w = refl

quarterAdd : (a : D.Quarter) (p q : T.Triple ℤ) →
  T.quarter Metric.integerSignedCarrier a (add3 p q) ≡
  add3 (T.quarter Metric.integerSignedCarrier a p)
       (T.quarter Metric.integerSignedCarrier a q)
quarterAdd D.q0 p q = refl
quarterAdd D.q1 p q = rotateAdd p q
quarterAdd D.q2 p q =
  trans (cong (T.R Metric.integerSignedCarrier) (rotateAdd p q))
        (rotateAdd (T.R Metric.integerSignedCarrier p)
                   (T.R Metric.integerSignedCarrier q))
quarterAdd D.q3 p q =
  trans (cong (T.R Metric.integerSignedCarrier) (quarterAdd D.q2 p q))
        (rotateAdd
          (T.quarter Metric.integerSignedCarrier D.q2 p)
          (T.quarter Metric.integerSignedCarrier D.q2 q))

verticalBitAdd : (b : Bool) (p q : T.Triple ℤ) →
  T.vertical Metric.integerSignedCarrier b (add3 p q) ≡
  add3 (T.vertical Metric.integerSignedCarrier b p)
       (T.vertical Metric.integerSignedCarrier b q)
verticalBitAdd false p q = refl
verticalBitAdd true p q = verticalAdd p q

horizontalBitAdd : (b : Bool) (p q : T.Triple ℤ) →
  T.horizontal Metric.integerSignedCarrier b (add3 p q) ≡
  add3 (T.horizontal Metric.integerSignedCarrier b p)
       (T.horizontal Metric.integerSignedCarrier b q)
horizontalBitAdd false p q = refl
horizontalBitAdd true p q = horizontalAdd p q

-- Additivity of all sixteen signed-coordinate operations.
fullAdd : (g : D.D4h) (p q : T.Triple ℤ) →
  T.act Metric.integerSignedCarrier g (add3 p q) ≡
  add3 (T.act Metric.integerSignedCarrier g p)
       (T.act Metric.integerSignedCarrier g q)
fullAdd (D.element a b c) p q =
  trans
    (cong (λ t → T.quarter Metric.integerSignedCarrier a
                        (T.vertical Metric.integerSignedCarrier b t))
          (horizontalBitAdd c p q))
    (trans
      (cong (T.quarter Metric.integerSignedCarrier a)
            (verticalBitAdd b
              (T.horizontal Metric.integerSignedCarrier c p)
              (T.horizontal Metric.integerSignedCarrier c q)))
      (quarterAdd a
        (T.vertical Metric.integerSignedCarrier b
          (T.horizontal Metric.integerSignedCarrier c p))
        (T.vertical Metric.integerSignedCarrier b
          (T.horizontal Metric.integerSignedCarrier c q))))

toModeAdd : (p q : T.Triple ℤ) →
  toMode (add3 p q) ≡ NS.addMode (toMode p) (toMode q)
toModeAdd (T.xyz x y z) (T.xyz u v w) = refl

actMode : D.D4h → NS.FourierMode → NS.FourierMode
actMode g p =
  toMode (T.act Metric.integerSignedCarrier g (fromMode p))

-- The existing Fourier resonance/addition operation is equivariant.
actModeAdd : (g : D.D4h) (p q : NS.FourierMode) →
  actMode g (NS.addMode p q) ≡
  NS.addMode (actMode g p) (actMode g q)
actModeAdd g (NS.mode x y z) (NS.mode u v w) =
  trans
    (cong toMode
      (fullAdd g (T.xyz x y z) (T.xyz u v w)))
    (toModeAdd
      (T.act Metric.integerSignedCarrier g (T.xyz x y z))
      (T.act Metric.integerSignedCarrier g (T.xyz u v w)))

modeWeightedPairing :
  ℤ → ℤ → NS.FourierMode → NS.FourierMode → ℤ
modeWeightedPairing a c p k =
  Metric.weightedDot a c (fromMode p) (fromMode k)

modePairingInvariant :
  (a c : ℤ) (g : D.D4h) (p k : NS.FourierMode) →
  modeWeightedPairing a c (actMode g p) (actMode g k) ≡
  modeWeightedPairing a c p k
modePairingInvariant a c g p k
  rewrite tripleRoundTrip (T.act Metric.integerSignedCarrier g (fromMode p))
        | tripleRoundTrip (T.act Metric.integerSignedCarrier g (fromMode k)) =
  Metric.fullTetragonalMetricInvariant a c g (fromMode p) (fromMode k)

modeShellInvariant :
  (a c : ℤ) (g : D.D4h) (p : NS.FourierMode) →
  modeWeightedPairing a c (actMode g p) (actMode g p) ≡
  modeWeightedPairing a c p p
modeShellInvariant a c g p = modePairingInvariant a c g p p

-- Addition/orthogonality/shell invariance on Z^3 is now reusable by
-- Fourier-mode, crystal, and spectral consumers. Non-symmorphic
-- Seitz translations, magnetic/antiunitary actions, and actual Bloch
-- bands are separate downstream obligations.
