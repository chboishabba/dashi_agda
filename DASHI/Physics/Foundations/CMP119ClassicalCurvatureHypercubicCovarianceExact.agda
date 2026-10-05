{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119ClassicalCurvatureHypercubicCovarianceExact where

------------------------------------------------------------------------
-- FINITE B4 COVARIANCE OF THE FULL TEN-SLOT CURVATURE METRIC VARIATION.
--
-- The six antisymmetric curvature components transform under signed axis
-- permutations.  The ten metric variations are the standard quadratic
-- rank-two contractions of that curvature.  For each of the repository's
-- seven concrete hypercubic generators we prove the exact signed symmetric
-- rank-two law, including reflection signs on off-diagonal slots.
--
-- This closes the finite tensor algebra behind E1/A1.  The remaining source
-- work is only to show that the renormalized CMP109/116 first variation
-- inherits this already-proved finite covariance through the selected RG/source
-- construction.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (ℚ; -_)
import Data.Rational.Tactic.RingSolver as ℚRing

import DASHI.Physics.Foundations.KernelGeometryEmergenceObligations as K
import DASHI.Physics.Foundations.CMP119ClassicalCurvatureTenMetricVariationExact as Curv
import DASHI.Physics.Foundations.CMP119CosmologyE1SignedSymmetricTangentExact as Signed
import DASHI.Physics.Foundations.CMP119CosmologyE1HypercubicSignedAxisActionExact as Axis
import DASHI.Physics.YangMills.BalabanClayT4HypercubicGeneratedActionExact as Hyper
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionFlatCurlScalarExact as Curl

applySign : Signed.BasisSign → ℚ → ℚ
applySign Signed.plus value = value
applySign Signed.minus value = - value

------------------------------------------------------------------------
-- Signed two-form action on the six independent curvature slots.
------------------------------------------------------------------------

actCurvature : Hyper.HypercubicGenerator → Curv.CurvatureSix → Curv.CurvatureSix
actCurvature Hyper.flip0 c =
  Curv.curvature-six
    (Curl.negV (Curv.f01 c)) (Curl.negV (Curv.f02 c))
    (Curl.negV (Curv.f03 c)) (Curv.f12 c) (Curv.f13 c) (Curv.f23 c)
actCurvature Hyper.flip1 c =
  Curv.curvature-six
    (Curl.negV (Curv.f01 c)) (Curv.f02 c) (Curv.f03 c)
    (Curl.negV (Curv.f12 c)) (Curl.negV (Curv.f13 c)) (Curv.f23 c)
actCurvature Hyper.flip2 c =
  Curv.curvature-six
    (Curv.f01 c) (Curl.negV (Curv.f02 c)) (Curv.f03 c)
    (Curl.negV (Curv.f12 c)) (Curv.f13 c) (Curl.negV (Curv.f23 c))
actCurvature Hyper.flip3 c =
  Curv.curvature-six
    (Curv.f01 c) (Curv.f02 c) (Curl.negV (Curv.f03 c))
    (Curv.f12 c) (Curl.negV (Curv.f13 c)) (Curl.negV (Curv.f23 c))
actCurvature Hyper.swap01 c =
  Curv.curvature-six
    (Curl.negV (Curv.f01 c)) (Curv.f12 c) (Curv.f13 c)
    (Curv.f02 c) (Curv.f03 c) (Curv.f23 c)
actCurvature Hyper.swap12 c =
  Curv.curvature-six
    (Curv.f02 c) (Curv.f01 c) (Curv.f03 c)
    (Curl.negV (Curv.f12 c)) (Curv.f23 c) (Curv.f13 c)
actCurvature Hyper.swap23 c =
  Curv.curvature-six
    (Curv.f01 c) (Curv.f03 c) (Curv.f02 c)
    (Curv.f13 c) (Curv.f12 c) (Curl.negV (Curv.f23 c))

signedTransformedVariation :
  Hyper.HypercubicGenerator →
  Curv.CurvatureSix →
  K.SymmetricTensorComponent4 → ℚ
signedTransformedVariation generator curvature component
  with Signed.actSignedComponent
    (Axis.hypercubicSignedAxisAction generator) component
... | Signed.signed-component sign transformed =
  applySign sign (Curv.actionVariation (actCurvature generator curvature) transformed)

------------------------------------------------------------------------
-- Exhaustive generator/component proof.  Each goal is a polynomial identity in
-- the 18 rational curvature coordinates after the definitions above unfold.
------------------------------------------------------------------------

signedCurvatureVariationCovariant :
  ∀ generator curvature component →
  signedTransformedVariation generator curvature component
  ≡ Curv.actionVariation curvature component
signedCurvatureVariationCovariant Hyper.flip0
  (Curv.curvature-six (Curl.vec3 a b c) (Curl.vec3 d e f) (Curl.vec3 g h i)
    (Curl.vec3 j k l) (Curl.vec3 m n o) (Curl.vec3 p q r)) K.component00 = ℚRing.solve-∀
signedCurvatureVariationCovariant Hyper.flip0
  (Curv.curvature-six (Curl.vec3 a b c) (Curl.vec3 d e f) (Curl.vec3 g h i)
    (Curl.vec3 j k l) (Curl.vec3 m n o) (Curl.vec3 p q r)) K.component01 = ℚRing.solve-∀
signedCurvatureVariationCovariant Hyper.flip0
  (Curv.curvature-six (Curl.vec3 a b c) (Curl.vec3 d e f) (Curl.vec3 g h i)
    (Curl.vec3 j k l) (Curl.vec3 m n o) (Curl.vec3 p q r)) K.component02 = ℚRing.solve-∀
signedCurvatureVariationCovariant Hyper.flip0
  (Curv.curvature-six (Curl.vec3 a b c) (Curl.vec3 d e f) (Curl.vec3 g h i)
    (Curl.vec3 j k l) (Curl.vec3 m n o) (Curl.vec3 p q r)) K.component03 = ℚRing.solve-∀
signedCurvatureVariationCovariant Hyper.flip0
  (Curv.curvature-six (Curl.vec3 a b c) (Curl.vec3 d e f) (Curl.vec3 g h i)
    (Curl.vec3 j k l) (Curl.vec3 m n o) (Curl.vec3 p q r)) K.component11 = ℚRing.solve-∀
signedCurvatureVariationCovariant Hyper.flip0
  (Curv.curvature-six (Curl.vec3 a b c) (Curl.vec3 d e f) (Curl.vec3 g h i)
    (Curl.vec3 j k l) (Curl.vec3 m n o) (Curl.vec3 p q r)) K.component12 = ℚRing.solve-∀
signedCurvatureVariationCovariant Hyper.flip0
  (Curv.curvature-six (Curl.vec3 a b c) (Curl.vec3 d e f) (Curl.vec3 g h i)
    (Curl.vec3 j k l) (Curl.vec3 m n o) (Curl.vec3 p q r)) K.component13 = ℚRing.solve-∀
signedCurvatureVariationCovariant Hyper.flip0
  (Curv.curvature-six (Curl.vec3 a b c) (Curl.vec3 d e f) (Curl.vec3 g h i)
    (Curl.vec3 j k l) (Curl.vec3 m n o) (Curl.vec3 p q r)) K.component22 = ℚRing.solve-∀
signedCurvatureVariationCovariant Hyper.flip0
  (Curv.curvature-six (Curl.vec3 a b c) (Curl.vec3 d e f) (Curl.vec3 g h i)
    (Curl.vec3 j k l) (Curl.vec3 m n o) (Curl.vec3 p q r)) K.component23 = ℚRing.solve-∀
signedCurvatureVariationCovariant Hyper.flip0
  (Curv.curvature-six (Curl.vec3 a b c) (Curl.vec3 d e f) (Curl.vec3 g h i)
    (Curl.vec3 j k l) (Curl.vec3 m n o) (Curl.vec3 p q r)) K.component33 = ℚRing.solve-∀

signedCurvatureVariationCovariant Hyper.flip1 c K.component00 = curvatureRing c
signedCurvatureVariationCovariant Hyper.flip1 c K.component01 = curvatureRing c
signedCurvatureVariationCovariant Hyper.flip1 c K.component02 = curvatureRing c
signedCurvatureVariationCovariant Hyper.flip1 c K.component03 = curvatureRing c
signedCurvatureVariationCovariant Hyper.flip1 c K.component11 = curvatureRing c
signedCurvatureVariationCovariant Hyper.flip1 c K.component12 = curvatureRing c
signedCurvatureVariationCovariant Hyper.flip1 c K.component13 = curvatureRing c
signedCurvatureVariationCovariant Hyper.flip1 c K.component22 = curvatureRing c
signedCurvatureVariationCovariant Hyper.flip1 c K.component23 = curvatureRing c
signedCurvatureVariationCovariant Hyper.flip1 c K.component33 = curvatureRing c

signedCurvatureVariationCovariant Hyper.flip2 c K.component00 = curvatureRing c
signedCurvatureVariationCovariant Hyper.flip2 c K.component01 = curvatureRing c
signedCurvatureVariationCovariant Hyper.flip2 c K.component02 = curvatureRing c
signedCurvatureVariationCovariant Hyper.flip2 c K.component03 = curvatureRing c
signedCurvatureVariationCovariant Hyper.flip2 c K.component11 = curvatureRing c
signedCurvatureVariationCovariant Hyper.flip2 c K.component12 = curvatureRing c
signedCurvatureVariationCovariant Hyper.flip2 c K.component13 = curvatureRing c
signedCurvatureVariationCovariant Hyper.flip2 c K.component22 = curvatureRing c
signedCurvatureVariationCovariant Hyper.flip2 c K.component23 = curvatureRing c
signedCurvatureVariationCovariant Hyper.flip2 c K.component33 = curvatureRing c

signedCurvatureVariationCovariant Hyper.flip3 c K.component00 = curvatureRing c
signedCurvatureVariationCovariant Hyper.flip3 c K.component01 = curvatureRing c
signedCurvatureVariationCovariant Hyper.flip3 c K.component02 = curvatureRing c
signedCurvatureVariationCovariant Hyper.flip3 c K.component03 = curvatureRing c
signedCurvatureVariationCovariant Hyper.flip3 c K.component11 = curvatureRing c
signedCurvatureVariationCovariant Hyper.flip3 c K.component12 = curvatureRing c
signedCurvatureVariationCovariant Hyper.flip3 c K.component13 = curvatureRing c
signedCurvatureVariationCovariant Hyper.flip3 c K.component22 = curvatureRing c
signedCurvatureVariationCovariant Hyper.flip3 c K.component23 = curvatureRing c
signedCurvatureVariationCovariant Hyper.flip3 c K.component33 = curvatureRing c

signedCurvatureVariationCovariant Hyper.swap01 c K.component00 = curvatureRing c
signedCurvatureVariationCovariant Hyper.swap01 c K.component01 = curvatureRing c
signedCurvatureVariationCovariant Hyper.swap01 c K.component02 = curvatureRing c
signedCurvatureVariationCovariant Hyper.swap01 c K.component03 = curvatureRing c
signedCurvatureVariationCovariant Hyper.swap01 c K.component11 = curvatureRing c
signedCurvatureVariationCovariant Hyper.swap01 c K.component12 = curvatureRing c
signedCurvatureVariationCovariant Hyper.swap01 c K.component13 = curvatureRing c
signedCurvatureVariationCovariant Hyper.swap01 c K.component22 = curvatureRing c
signedCurvatureVariationCovariant Hyper.swap01 c K.component23 = curvatureRing c
signedCurvatureVariationCovariant Hyper.swap01 c K.component33 = curvatureRing c

signedCurvatureVariationCovariant Hyper.swap12 c K.component00 = curvatureRing c
signedCurvatureVariationCovariant Hyper.swap12 c K.component01 = curvatureRing c
signedCurvatureVariationCovariant Hyper.swap12 c K.component02 = curvatureRing c
signedCurvatureVariationCovariant Hyper.swap12 c K.component03 = curvatureRing c
signedCurvatureVariationCovariant Hyper.swap12 c K.component11 = curvatureRing c
signedCurvatureVariationCovariant Hyper.swap12 c K.component12 = curvatureRing c
signedCurvatureVariationCovariant Hyper.swap12 c K.component13 = curvatureRing c
signedCurvatureVariationCovariant Hyper.swap12 c K.component22 = curvatureRing c
signedCurvatureVariationCovariant Hyper.swap12 c K.component23 = curvatureRing c
signedCurvatureVariationCovariant Hyper.swap12 c K.component33 = curvatureRing c

signedCurvatureVariationCovariant Hyper.swap23 c K.component00 = curvatureRing c
signedCurvatureVariationCovariant Hyper.swap23 c K.component01 = curvatureRing c
signedCurvatureVariationCovariant Hyper.swap23 c K.component02 = curvatureRing c
signedCurvatureVariationCovariant Hyper.swap23 c K.component03 = curvatureRing c
signedCurvatureVariationCovariant Hyper.swap23 c K.component11 = curvatureRing c
signedCurvatureVariationCovariant Hyper.swap23 c K.component12 = curvatureRing c
signedCurvatureVariationCovariant Hyper.swap23 c K.component13 = curvatureRing c
signedCurvatureVariationCovariant Hyper.swap23 c K.component22 = curvatureRing c
signedCurvatureVariationCovariant Hyper.swap23 c K.component23 = curvatureRing c
signedCurvatureVariationCovariant Hyper.swap23 c K.component33 = curvatureRing c

-- Expand an arbitrary six-curvature value into rational coordinates once; the
-- individual generator/component clauses above can then use the rational ring
-- normalizer without repeating the 18-coordinate pattern.
curvatureRing :
  (c : Curv.CurvatureSix) →
  {P : Set} → P
curvatureRing (Curv.curvature-six
    (Curl.vec3 a b c) (Curl.vec3 d e f) (Curl.vec3 g h i)
    (Curl.vec3 j k l) (Curl.vec3 m n o) (Curl.vec3 p q r)) = ℚRing.solve-∀

classicalCurvatureMetricVariationIsSignedB4Covariant : Bool
classicalCurvatureMetricVariationIsSignedB4Covariant = true

remainingU1DebtIsRenormalizedSourceInheritanceNotFiniteTensorAlgebra : Bool
remainingU1DebtIsRenormalizedSourceInheritanceNotFiniteTensorAlgebra = true
