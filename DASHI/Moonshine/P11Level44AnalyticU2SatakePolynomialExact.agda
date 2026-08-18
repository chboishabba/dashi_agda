module DASHI.Moonshine.P11Level44AnalyticU2SatakePolynomialExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Fred Diamond and Jerry Shurman,
-- "A First Course in Modular Forms", GTM 228, Springer, 2005.
-- DOI: 10.1007/978-0-387-27226-9.
--
-- William Casselman,
-- "On some results of Atkin and Lehner", Math. Ann. 201 (1973), 301--314.
-- DOI: 10.1007/BF01428197.
--
-- For the level-11 weight-two newform, a_2=-2.  The unramified local Satake
-- polynomial at 2 is therefore
--
--   X^2 - a_2 X + 2 = X^2 + 2 X + 2.
--
-- On the p^2-oldspace with coordinates (f,V_2 f,V_4 f), the classical U2 is
-- already constructed in P11Level44BadPrimeOperatorSeparationExact:
--
--   U2(x1,x2,x4) = (-2 x1+x2, -2 x1+x4, 0).
--
-- DASHI CONTRIBUTION
--
-- Prove the exact operator polynomial
--
--   U2 (U2^2 + 2 U2 + 2 I) = 0
--
-- on the WHOLE integral Old3 carrier, and show that the Satake quadratic
-- applied to the deepest degeneracy vector e4 is exactly the known kernel
-- vector (1,2,2).
--
-- We also classify the kernel exactly:
--
--   ker(U2) = Z * (1,2,2).
--
-- This produces the source-native local invariant the principal-level-2 side
-- must eventually transport.  It is stronger than dimension or away-from-2
-- Hecke agreement and immediately excludes the internal positive marked R2.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Integer using (ℤ; +_; -[1+_])
  renaming (_+_ to _+ℤ_; _*_ to _*ℤ_)
import Data.Integer.Tactic.RingSolver as ℤRing

import DASHI.Moonshine.P11MarkedLevel44PermutationIntertwinerExact as Old
import DASHI.Moonshine.P11Level44BadPrimeOperatorSeparationExact as Bad

old3Ext :
  (u v : Old.Old3) →
  Old.x1 u ≡ Old.x1 v →
  Old.x2 u ≡ Old.x2 v →
  Old.x4 u ≡ Old.x4 v →
  u ≡ v
old3Ext
  (Old.old3 a b c)
  (Old.old3 a' b' c')
  refl refl refl = refl

------------------------------------------------------------------------
-- Satake quadratic Q(U)=U^2+2U+2I.
------------------------------------------------------------------------

satakeQuadraticU2 : Old.Old3 → Old.Old3
satakeQuadraticU2 v =
  Old.addOld3
    (Bad.analyticU2 (Bad.analyticU2 v))
    (Old.addOld3
      (Old.scaleOld3 (+ 2) (Bad.analyticU2 v))
      (Old.scaleOld3 (+ 2) v))

satakeQuadraticFormula :
  (v : Old.Old3) →
  satakeQuadraticU2 v
  ≡ Old.old3
      (Old.x4 v)
      ((+ 2) *ℤ Old.x4 v)
      ((+ 2) *ℤ Old.x4 v)
satakeQuadraticFormula (Old.old3 x y z) =
  old3Ext _ _
    (ℤRing.solve (x ∷ y ∷ z ∷ []))
    (ℤRing.solve (x ∷ y ∷ z ∷ []))
    (ℤRing.solve (x ∷ y ∷ z ∷ []))

satakeQuadraticLandsInKernel :
  (v : Old.Old3) →
  Bad.analyticU2 (satakeQuadraticU2 v) ≡ Bad.zeroOld3
satakeQuadraticLandsInKernel (Old.old3 x y z) =
  old3Ext _ _
    (ℤRing.solve (x ∷ y ∷ z ∷ []))
    (ℤRing.solve (x ∷ y ∷ z ∷ []))
    (ℤRing.solve (x ∷ y ∷ z ∷ []))

analyticU2CubicSatakeIdentity :
  (v : Old.Old3) →
  Bad.analyticU2
    (Old.addOld3
      (Bad.analyticU2 (Bad.analyticU2 v))
      (Old.addOld3
        (Old.scaleOld3 (+ 2) (Bad.analyticU2 v))
        (Old.scaleOld3 (+ 2) v)))
  ≡ Bad.zeroOld3
analyticU2CubicSatakeIdentity = satakeQuadraticLandsInKernel

------------------------------------------------------------------------
-- The deepest oldvector produces the explicit kernel generator under Q(U2).
------------------------------------------------------------------------

satakeQuadraticAtDeepestDegeneracy :
  satakeQuadraticU2 Old.oldBasis4 ≡ Bad.analyticU2KernelVector
satakeQuadraticAtDeepestDegeneracy = refl

------------------------------------------------------------------------
-- Exact kernel classification ker(U2)=Z*(1,2,2).
------------------------------------------------------------------------

kernelGenerator : Old.Old3
kernelGenerator = Bad.analyticU2KernelVector

kernelMultiple : ℤ → Old.Old3
kernelMultiple a = Old.scaleOld3 a kernelGenerator

kernelMultipleKilled :
  (a : ℤ) → Bad.analyticU2 (kernelMultiple a) ≡ Bad.zeroOld3
kernelMultipleKilled a =
  old3Ext _ _
    (ℤRing.solve (a ∷ []))
    (ℤRing.solve (a ∷ []))
    (ℤRing.solve (a ∷ []))

firstKernelEquationForcesX2 :
  (x y : ℤ) →
  ((-[1+ 1 ]) *ℤ x +ℤ y) ≡ (+ 0) →
  y ≡ (+ 2) *ℤ x
firstKernelEquationForcesX2 x y equation =
  trans
    (ℤRing.solve (x ∷ y ∷ []))
    (trans
      (cong (λ t → ((+ 2) *ℤ x) +ℤ t) equation)
      (ℤRing.solve (x ∷ [])))

secondKernelEquationForcesX4 :
  (x z : ℤ) →
  ((-[1+ 1 ]) *ℤ x +ℤ z) ≡ (+ 0) →
  z ≡ (+ 2) *ℤ x
secondKernelEquationForcesX4 x z equation =
  trans
    (ℤRing.solve (x ∷ z ∷ []))
    (trans
      (cong (λ t → ((+ 2) *ℤ x) +ℤ t) equation)
      (ℤRing.solve (x ∷ [])))

kernelVectorIsUniqueMultiple :
  (v : Old.Old3) →
  Bad.analyticU2 v ≡ Bad.zeroOld3 →
  v ≡ kernelMultiple (Old.x1 v)
kernelVectorIsUniqueMultiple
  v@(Old.old3 x y z) equation =
  let
    eq1 : ((-[1+ 1 ]) *ℤ x +ℤ y) ≡ (+ 0)
    eq1 = cong Old.x1 equation

    eq2 : ((-[1+ 1 ]) *ℤ x +ℤ z) ≡ (+ 0)
    eq2 = cong Old.x2 equation

    yEq : y ≡ (+ 2) *ℤ x
    yEq = firstKernelEquationForcesX2 x y eq1

    zEq : z ≡ (+ 2) *ℤ x
    zEq = secondKernelEquationForcesX4 x z eq2
  in
  old3Ext _ _
    (ℤRing.solve (x ∷ []))
    (trans yEq (ℤRing.solve (x ∷ [])))
    (trans zEq (ℤRing.solve (x ∷ [])))

------------------------------------------------------------------------
-- The deepest coordinate is literally the coefficient of the Satake residual.
------------------------------------------------------------------------

satakeResidualIsKernelMultipleOfDeepestCoordinate :
  (v : Old.Old3) →
  satakeQuadraticU2 v ≡ kernelMultiple (Old.x4 v)
satakeResidualIsKernelMultipleOfDeepestCoordinate v =
  trans
    (satakeQuadraticFormula v)
    (old3Ext _ _
      (ℤRing.solve (Old.x4 v ∷ []))
      (ℤRing.solve (Old.x4 v ∷ []))
      (ℤRing.solve (Old.x4 v ∷ [])))

record P11Level44AnalyticU2SatakePolynomialBoundary : Set where
  field
    analyticSatakeQuadraticConstructed : Bool
    cubicOperatorIdentityDerived : Bool
    deepestDegeneracyProducesKernelGenerator : Bool
    kernelClassifiedAsOneIntegralLine : Bool
    residualCoefficientIsDeepestCoordinate : Bool
    dimensionOnlyUsed : Bool
    principalLevel2TransportedOperatorConstructedHere : Bool

canonicalP11Level44AnalyticU2SatakePolynomialBoundary :
  P11Level44AnalyticU2SatakePolynomialBoundary
canonicalP11Level44AnalyticU2SatakePolynomialBoundary = record
  { analyticSatakeQuadraticConstructed = true
  ; cubicOperatorIdentityDerived = true
  ; deepestDegeneracyProducesKernelGenerator = true
  ; kernelClassifiedAsOneIntegralLine = true
  ; residualCoefficientIsDeepestCoordinate = true
  ; dimensionOnlyUsed = false
  ; principalLevel2TransportedOperatorConstructedHere = false
  }
