module DASHI.Physics.Plasma.MHDHelicalCoefficientAnatomyExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field

------------------------------------------------------------------------
-- HELICALLY DECOMPOSED INCOMPRESSIBLE MHD: COEFFICIENT ANATOMY
--
-- Source-shaped abstraction of the MHD extension of Waleffe's helical triad
-- formalism (e.g. Linkmann et al.).  The geometric helical triple-product
-- factor is kept separate from the radial/helicity-sign factors and from the
-- amplitude channel.
--
-- Momentum sector (schematically):
--   g_kpq * (s_p |p| - s_q |q|) * (u_p u_q - b_p b_q)
--
-- Induction sector (schematically):
--   g_kpq * s_k |k| * (u_p b_q - b_p u_q)
--
-- Constant factors/conjugations are intentionally left to the concrete
-- application receipt.  This owner records the algebraic shape used by BIDI.
------------------------------------------------------------------------

data BinarySign : Set where
  positive negative : BinarySign

data MHDAmplitudeChannel : Set where
  velocityVelocity
  magneticMagnetic
  velocityMagnetic
  magneticVelocity
  : MHDAmplitudeChannel

record HelicalMHDMode {r : _} (F : C3.RealField r) : Set r where
  constructor helical-mhd-mode
  field
    radius : C3.Carrier F
    helicalSign : BinarySign
    velocityAmplitude : C3.Carrier F
    magneticAmplitude : C3.Carrier F

open HelicalMHDMode public

record HelicalTriadGeometry {r : _} (F : C3.RealField r) : Set r where
  constructor helical-triad-geometry
  field
    geometricFactor : C3.Carrier F
    wavevectorClosureReceipt : Set
    divergenceFreeReceipt : Set
    geometryReference : String

open HelicalTriadGeometry public

------------------------------------------------------------------------
-- Signed radius is application-provided: this avoids pretending the abstract
-- sign datatype itself is already embedded into every field carrier.
------------------------------------------------------------------------

record SignedRadiusEmbedding {r : _} (F : C3.RealField r) : Set r where
  constructor signed-radius-embedding
  field
    signedRadius : BinarySign → C3.Carrier F → C3.Carrier F
    positiveReference : String
    negativeReference : String

open SignedRadiusEmbedding public

private
  sub : ∀ {r} {F : C3.RealField r} → C3.Carrier F → C3.Carrier F → C3.Carrier F
  sub {F = F} x y = C3.add F x (C3.negate F y)

momentumRadialDifference :
  ∀ {r} {F : C3.RealField r} →
  SignedRadiusEmbedding F →
  HelicalMHDMode F → HelicalMHDMode F → C3.Carrier F
momentumRadialDifference embed p q =
  sub
    (signedRadius embed (helicalSign p) (radius p))
    (signedRadius embed (helicalSign q) (radius q))

momentumCoefficient :
  ∀ {r} {F : C3.RealField r} →
  SignedRadiusEmbedding F →
  HelicalTriadGeometry F →
  HelicalMHDMode F → HelicalMHDMode F → C3.Carrier F
momentumCoefficient {F = F} embed geometry p q =
  C3.multiply F
    (geometricFactor geometry)
    (momentumRadialDifference embed p q)

inductionOutputFactor :
  ∀ {r} {F : C3.RealField r} →
  SignedRadiusEmbedding F → HelicalMHDMode F → C3.Carrier F
inductionOutputFactor embed k =
  signedRadius embed (helicalSign k) (radius k)

inductionCoefficient :
  ∀ {r} {F : C3.RealField r} →
  SignedRadiusEmbedding F →
  HelicalTriadGeometry F →
  HelicalMHDMode F → C3.Carrier F
inductionCoefficient {F = F} embed geometry k =
  C3.multiply F
    (geometricFactor geometry)
    (inductionOutputFactor embed k)

record MHDHelicalCoefficientBoundary : Set where
  constructor mhd-helical-coefficient-boundary
  field
    momentumAndInductionCoefficientsDefinitionallySame : Bool
    momentumAndInductionCoefficientsDefinitionallySameIsFalse :
      momentumAndInductionCoefficientsDefinitionallySame ≡ false

    velocityHelicitySignIsElsasserOrientation : Bool
    velocityHelicitySignIsElsasserOrientationIsFalse :
      velocityHelicitySignIsElsasserOrientation ≡ false

    nsCoefficientReceiptIsMhdCoefficientReceipt : Bool
    nsCoefficientReceiptIsMhdCoefficientReceiptIsFalse :
      nsCoefficientReceiptIsMhdCoefficientReceipt ≡ false

canonicalMHDHelicalCoefficientBoundary : MHDHelicalCoefficientBoundary
canonicalMHDHelicalCoefficientBoundary =
  mhd-helical-coefficient-boundary false refl false refl false refl
