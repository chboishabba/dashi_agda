module DASHI.Mathematics.Topology.AlexanderHornedC3SpinCyclotomicIntertwinerExact where

------------------------------------------------------------------------
-- ACTUAL SAME REPRESENTATION, NOT A CHARACTER-POLYNOMIAL MATCH
--
-- Prior DASHI:
-- * BalabanP33RationalQuaternionCoreExact (same quaternion field)
-- * CayleyDicksonRationalComplexQuaternionExact (exact Q(i) product)
-- * AlexanderHornedQuaternionC3SpinExact (same coherent -q rotor)
-- * AlexanderHornedC3MaschkeReynoldsExact (actual R3 cycle)
--
-- q=(1+i+j+k)/2, coherent spin lift s=-q.
-- Embed each rational quaternion a+bi+cj+dk as
--   U(q) = [[a+bi, c+di],[-c+di,a-bi]]
-- acting on Gaussian-rational two-spinors. Then V=U(-q) has
--
-- V = [ -(1+i)/2   -(1+i)/2 ]
--     [  (1-i)/2   (-1+i)/2 ]
--
-- and A=[[0,-1],[1,-1]]. Let
--   T = [ 1  -(1+i)/2 ]    T^-1 = [ 1  i   ]
--       [ 0   (1-i)/2 ]           [ 0  1+i ]
-- Then V T = T A; T^-1 T = T T^-1 = I.
--
-- This gives the EXACT missing same-matrix comparison:
-- the actual SU2 quaternion rotor and the integral C3 companion
-- are conjugate over Q(i), not just isospectral.
--
-- The determinant of T is (1-i)/2, a unit in the Gaussian
-- integer localization at every ODD prime (norm =1/2).
-- Thus reduction modulo 3 (in F9) carries the SAME Jordan
-- degeneration, while at 5 and 7 Maschke is available.
-- No change of coefficients at p=2 asserted: 1/2 unavailable.
--
-- Kernel and geometry boundaries: source-written Agda;
-- no complete Clifford/Dirac continuum spinor bundle theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; ½; -½; -_)
import Data.Rational.Tactic.RingSolver as Ring

import DASHI.Mathematics.Algebra.CayleyDicksonRationalComplexQuaternionExact as CD
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionCoreExact as Q
import DASHI.Mathematics.Topology.AlexanderHornedQuaternionC3SpinExact as Horn

record Spinor2 : Set where
  constructor spinor2
  field
    first second : CD.RationalComplex
open Spinor2 public

record ComplexMatrix2 : Set where
  constructor complexMatrix2
  field
    a00 a01 a10 a11 : CD.RationalComplex
open ComplexMatrix2 public

fromQuaternion : Q.RationalQuaternion → ComplexMatrix2
fromQuaternion (Q.quat a b c d) =
  complexMatrix2
    (CD.complex a b)
    (CD.complex c d)
    (CD.complex (- c) d)
    (CD.complex a (- b))

apply : ComplexMatrix2 → Spinor2 → Spinor2
apply (complexMatrix2 a b c d) (spinor2 x y) =
  spinor2
    (CD._+c_ (CD._*c_ a x) (CD._*c_ b y))
    (CD._+c_ (CD._*c_ c x) (CD._*c_ d y))

spinCoherent : ComplexMatrix2
spinCoherent = fromQuaternion Horn.negativeRotor

oneC iC onePlusI : CD.RationalComplex
oneC = CD.oneC
iC = CD.complex 0ℚ 1ℚ
onePlusI = CD.complex 1ℚ 1ℚ

w1 w2 : CD.RationalComplex
w1 = CD.complex -½ -½
w2 = CD.complex ½ -½

-- The change-of-basis columns are e1 and V(e1).
T : Spinor2 → Spinor2
T (spinor2 x y) =
  spinor2
    (CD._+c_ x (CD._*c_ w1 y))
    (CD._*c_ w2 y)

Tinverse : Spinor2 → Spinor2
Tinverse (spinor2 x y) =
  spinor2
    (CD._+c_ x (CD._*c_ iC y))
    (CD._*c_ onePlusI y)

-- Standard 2-dimensional cyclotomic companion representation:
-- same A used in the char 3/5/7 regression.
companion : Spinor2 → Spinor2
companion (spinor2 x y) =
  spinor2 (CD.negC y) (CD._-c_ x y)

spinor2Ext : ∀ {x y x' y'} →
  x ≡ x' → y ≡ y' →
  spinor2 x y ≡ spinor2 x' y'
spinor2Ext refl refl = refl

TLeftInverse : ∀ v → Tinverse (T v) ≡ v
TLeftInverse (spinor2 (CD.complex xr xi) (CD.complex yr yi)) =
  spinor2Ext
    (CD.complexExt
      (Ring.solve-∀ xr xi yr yi)
      (Ring.solve-∀ xr xi yr yi))
    (CD.complexExt
      (Ring.solve-∀ xr xi yr yi)
      (Ring.solve-∀ xr xi yr yi))

TRightInverse : ∀ v → T (Tinverse v) ≡ v
TRightInverse (spinor2 (CD.complex xr xi) (CD.complex yr yi)) =
  spinor2Ext
    (CD.complexExt
      (Ring.solve-∀ xr xi yr yi)
      (Ring.solve-∀ xr xi yr yi))
    (CD.complexExt
      (Ring.solve-∀ xr xi yr yi)
      (Ring.solve-∀ xr xi yr yi))

sameSpinRotationIntertwiner : ∀ v →
  apply spinCoherent (T v) ≡ T (companion v)
sameSpinRotationIntertwiner
    (spinor2 (CD.complex xr xi) (CD.complex yr yi)) =
  spinor2Ext
    (CD.complexExt
      (Ring.solve-∀ xr xi yr yi)
      (Ring.solve-∀ xr xi yr yi))
    (CD.complexExt
      (Ring.solve-∀ xr xi yr yi)
      (Ring.solve-∀ xr xi yr yi))

companionCubeIsIdentity : ∀ v →
  companion (companion (companion v)) ≡ v
companionCubeIsIdentity
    (spinor2 (CD.complex xr xi) (CD.complex yr yi)) =
  spinor2Ext
    (CD.complexExt
      (Ring.solve-∀ xr xi yr yi)
      (Ring.solve-∀ xr xi yr yi))
    (CD.complexExt
      (Ring.solve-∀ xr xi yr yi)
      (Ring.solve-∀ xr xi yr yi))

-- This is the honest existing-Q(i)-to-cyclotomic bridge.
-- It does not turn a characteristic-3 fixed line into a
-- physical zero-frequency Dirac state.
