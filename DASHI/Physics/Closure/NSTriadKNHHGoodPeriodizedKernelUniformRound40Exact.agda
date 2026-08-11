module DASHI.Physics.Closure.NSTriadKNHHGoodPeriodizedKernelUniformRound40Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier--Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- DASHI CONTRIBUTION
--
-- Connect the exact finite HH-good weighted-Cauchy theorem to the *correct*
-- shell-localized strain-kernel authority.  The repository's existing
-- `PeriodizedDyadicKernelL1Theorem` is for Luo's scalar radial low-pass cutoff;
-- it must NOT be silently identified with the matrix-valued order-zero strain
-- multiplier.  Round 40 therefore makes the required standard annular
-- multiplier theorem explicit instead of hiding a false same-object equality.
--
-- For the shell-localized strain symbol
--
--   phi_q(k) |k|^{-2} S_ang(k),
--
-- the angular factor is homogeneous of degree zero away from k=0 and phi_q is
-- smooth annular.  Standard Fourier multiplier/scaling theory gives a fixed
-- Euclidean master kernel L1 norm, and periodization preserves a shell-uniform
-- torus L1 bound.  That imported analytic theorem is represented below by
-- `PeriodizedAnnularStrainKernelL1Theorem`.
--
-- The only DASHI same-object seam is then honest:
--
--   finite sample mass = literal strain-shell kernel L1 norm.
--
-- Once supplied, the already-proved finite Cauchy theorem yields
--
--   |good shell stretching|^2
--     <= C_strain * delta * weightedLocalMass
--
-- uniformly in shell.  The remaining physical/PDE work is constructing this
-- standard annular strain-kernel realization on the literal torus carrier and
-- feeding the weighted local mass into time/dissipation absorption.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _*_; _≤_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNLuoBadCoherenceWeightedMarkovExact as Threshold
import DASHI.Physics.Closure.NSTriadKNHHGoodFiniteKernelCauchyRound40Exact as Good

record PeriodizedAnnularStrainKernelL1Theorem
    {st : Level}
    (TorusPoint : Set st) : Set (lsuc st) where
  field
    strainShellKernelL1Norm : Nat → ℚ
    masterAnnularStrainKernelL1Norm : ℚ

    masterAnnularStrainKernelL1Nonnegative :
      0ℚ ≤ masterAnnularStrainKernelL1Norm

    periodizedStrainKernelL1BoundUniformInShell :
      (shell : Nat) →
      strainShellKernelL1Norm shell ≤ masterAnnularStrainKernelL1Norm

    AnnularCutoffSmoothAndCompactlySupportedAwayFromZero : Set st
    annularCutoffSmoothAndCompactlySupportedAwayFromZero :
      AnnularCutoffSmoothAndCompactlySupportedAwayFromZero

    StrainAngularMultiplierHomogeneousDegreeZero : Set st
    strainAngularMultiplierHomogeneousDegreeZero :
      StrainAngularMultiplierHomogeneousDegreeZero

    MasterAnnularStrainKernelIsL1 : Set st
    masterAnnularStrainKernelIsL1 : MasterAnnularStrainKernelIsL1

    PeriodizationFormulaIsCanonical : Set st
    periodizationFormulaIsCanonical : PeriodizationFormulaIsCanonical

open PeriodizedAnnularStrainKernelL1Theorem public

record PhysicalStrainShellKernelMassIdentification
    {st : Level}
    {TorusPoint : Set st}
    (kernelTheorem : PeriodizedAnnularStrainKernelL1Theorem TorusPoint)
    (shell : Nat)
    (parameter : Threshold.PositiveThreshold)
    (samples : List (Good.HHGoodKernelSample parameter)) : Set where
  field
    sampleMassIsPhysicalPeriodizedStrainKernelL1 :
      Good.kernelMass samples
      ≡ strainShellKernelL1Norm kernelTheorem shell

open PhysicalStrainShellKernelMassIdentification public

uniformCertificateFromPeriodizedStrainKernel :
  ∀ {st} {TorusPoint : Set st}
    {kernelTheorem : PeriodizedAnnularStrainKernelL1Theorem TorusPoint}
    {shell parameter samples} →
  PhysicalStrainShellKernelMassIdentification
    kernelTheorem shell parameter samples →
  Good.UniformShellKernelMassCertificate samples
uniformCertificateFromPeriodizedStrainKernel
    {kernelTheorem = kernelTheorem} {shell = shell} identification = record
  { uniformKernelConstant = masterAnnularStrainKernelL1Norm kernelTheorem
  ; uniformKernelConstantNonnegative =
      masterAnnularStrainKernelL1Nonnegative kernelTheorem
  ; kernelMassBelowUniformConstant =
      subst
        (λ left → left ≤ masterAnnularStrainKernelL1Norm kernelTheorem)
        (sym (sampleMassIsPhysicalPeriodizedStrainKernelL1 identification))
        (periodizedStrainKernelL1BoundUniformInShell kernelTheorem shell)
  }

periodizedHHGoodShellBound :
  ∀ {st} {TorusPoint : Set st}
    {kernelTheorem : PeriodizedAnnularStrainKernelL1Theorem TorusPoint}
    {shell parameter samples} →
  (identification : PhysicalStrainShellKernelMassIdentification
    kernelTheorem shell parameter samples) →
  L2.square (Good.weightedStretch samples)
  ≤ masterAnnularStrainKernelL1Norm kernelTheorem
      * (Threshold.threshold parameter * Good.weightedLocalMass samples)
periodizedHHGoodShellBound identification =
  Good.finiteHHGoodUniformKernelBound
    (uniformCertificateFromPeriodizedStrainKernel identification)

hhGoodPeriodizedKernelUniformBridgeClosed : Bool
hhGoodPeriodizedKernelUniformBridgeClosed = true

physicalAnnularStrainKernelL1TheoremConstructed : Bool
physicalAnnularStrainKernelL1TheoremConstructed = false

physicalStrainShellKernelMassIdentificationConstructed : Bool
physicalStrainShellKernelMassIdentificationConstructed = false

hhGoodPeriodizedKernelUniformBridgeClosedIsTrue :
  hhGoodPeriodizedKernelUniformBridgeClosed ≡ true
hhGoodPeriodizedKernelUniformBridgeClosedIsTrue = refl
