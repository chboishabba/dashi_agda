module DASHI.Physics.Closure.NSAncientVortexStretchingMaximumPrincipleNoGoExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: A. J. Majda; A. L. Bertozzi.
-- Title: "Vorticity and Incompressible Flow".
-- DOI: 10.1017/CBO9780511613203.
--
-- Authors: J. T. Beale; T. Kato; A. Majda.
-- Title: "Remarks on the breakdown of smooth solutions for the 3-D Euler
--         equations".
-- DOI: 10.1007/BF01212349.
--
-- RELATION TO THE UPLOADED LIOUVILLE PAPERS
-- Lei-Ren-Zhang and Lei-Zhang-Zhao exploit the scalar axisymmetric quantity
-- Gamma = r v_theta, whose equation has no vortex-stretching source and hence
-- admits maximum-principle/Nash-Moser technology.  For general 3-D vorticity,
--
--   (d_t + u.grad - Delta) omega = (omega.grad)u,
--
-- and the magnitude equation contains omega^T (grad u) omega.  The theorem
-- below proves that incompressibility (trace grad u = 0) alone gives this
-- quadratic form no sign: an explicit trace-free diagonal strain produces
-- both +1 and -1 on the same vorticity direction.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; -_; _+_; _*_)

record DiagonalStrain : Set where
  constructor strain
  field
    s1 s2 s3 : ℚ

open DiagonalStrain public

trace : DiagonalStrain → ℚ
trace S = s1 S + s2 S + s3 S

record Vorticity3 : Set where
  constructor omega
  field
    w1 w2 w3 : ℚ

open Vorticity3 public

stretchingQuadratic : DiagonalStrain → Vorticity3 → ℚ
stretchingQuadratic S w =
  s1 S * (w1 w * w1 w)
  + s2 S * (w2 w * w2 w)
  + s3 S * (w3 w * w3 w)

positiveTraceFreeStrain : DiagonalStrain
positiveTraceFreeStrain = strain 1ℚ (- 1ℚ) 0ℚ

negativeTraceFreeStrain : DiagonalStrain
negativeTraceFreeStrain = strain (- 1ℚ) 1ℚ 0ℚ

unitVorticityX : Vorticity3
unitVorticityX = omega 1ℚ 0ℚ 0ℚ

positiveStrainIsIncompressible : trace positiveTraceFreeStrain ≡ 0ℚ
positiveStrainIsIncompressible = refl

negativeStrainIsIncompressible : trace negativeTraceFreeStrain ≡ 0ℚ
negativeStrainIsIncompressible = refl

positiveStretchingWitness :
  stretchingQuadratic positiveTraceFreeStrain unitVorticityX ≡ 1ℚ
positiveStretchingWitness = refl

negativeStretchingWitness :
  stretchingQuadratic negativeTraceFreeStrain unitVorticityX ≡ - 1ℚ
negativeStretchingWitness = refl

-- Thus divergence-free structure by itself cannot turn the 3-D vorticity
-- equation into the source-free scalar parabolic equation used by the
-- axisymmetric Liouville proofs.  Any successful generalization must provide
-- an additional depletion/alignment/cancellation mechanism for stretching,
-- or use a different scalar/vector quantity altogether.
