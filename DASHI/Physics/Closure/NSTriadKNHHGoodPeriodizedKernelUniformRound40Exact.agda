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
-- Connect the exact finite HH-good weighted-Cauchy theorem to the repository's
-- already selected standard periodized dyadic-kernel L1 authority.  The only
-- same-object seam retained here is the literal equality between the finite
-- sample mass used by the stretching calculation and the physical periodized
-- strain-shell kernel L1 norm.
--
-- Once that equality is supplied, the cutoff/shell-independent constant is
-- not a new assumption: it is exactly the Euclidean inverse-transform L1 norm
-- from the periodization theorem.  Therefore
--
--   |shell good stretching|^2
--     <= C_kernel * delta * weightedLocalMass
--
-- with C_kernel independent of shell.
------------------------------------------------------------------------

open import Agda.Primitive using (Level)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _*_; _≤_)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNLuoBadCoherenceWeightedMarkovExact as Threshold
import DASHI.Physics.Closure.NSTriadKNLuoConcreteRadialMultiplierKernelExact as Kernel
import DASHI.Physics.Closure.NSTriadKNHHGoodFiniteKernelCauchyRound40Exact as Good

record PhysicalStrainShellKernelMassIdentification
    {st : Level}
    {TorusPoint : Set st}
    (kernelTheorem : Kernel.PeriodizedDyadicKernelL1Theorem TorusPoint)
    (shell : Nat)
    (parameter : Threshold.PositiveThreshold)
    (samples : List (Good.HHGoodKernelSample parameter)) : Set where
  field
    sampleMassIsPhysicalPeriodizedKernelL1 :
      Good.kernelMass samples
      ≡ Kernel.periodicKernelL1Norm kernelTheorem shell

open PhysicalStrainShellKernelMassIdentification public

uniformCertificateFromPeriodizedKernel :
  ∀ {st} {TorusPoint : Set st}
    {kernelTheorem : Kernel.PeriodizedDyadicKernelL1Theorem TorusPoint}
    {shell parameter samples} →
  PhysicalStrainShellKernelMassIdentification
    kernelTheorem shell parameter samples →
  Good.UniformShellKernelMassCertificate samples
uniformCertificateFromPeriodizedKernel {kernelTheorem = kernelTheorem}
    {shell = shell} identification = record
  { uniformKernelConstant =
      Kernel.euclideanInverseTransformL1Norm kernelTheorem
  ; uniformKernelConstantNonnegative =
      Kernel.euclideanInverseTransformL1Nonnegative kernelTheorem
  ; kernelMassBelowUniformConstant =
      subst
        (λ left →
          left ≤ Kernel.euclideanInverseTransformL1Norm kernelTheorem)
        (symmetry
          (sampleMassIsPhysicalPeriodizedKernelL1 identification))
        (Kernel.periodizedKernelL1BoundUniformInShell kernelTheorem shell)
  }
  where
  symmetry : ∀ {a b : ℚ} → a ≡ b → b ≡ a
  symmetry refl = refl

periodizedHHGoodShellBound :
  ∀ {st} {TorusPoint : Set st}
    {kernelTheorem : Kernel.PeriodizedDyadicKernelL1Theorem TorusPoint}
    {shell parameter samples} →
  (identification : PhysicalStrainShellKernelMassIdentification
    kernelTheorem shell parameter samples) →
  L2.square (Good.weightedStretch samples)
  ≤ Kernel.euclideanInverseTransformL1Norm kernelTheorem
      * (Threshold.threshold parameter * Good.weightedLocalMass samples)
periodizedHHGoodShellBound identification =
  Good.finiteHHGoodUniformKernelBound
    (uniformCertificateFromPeriodizedKernel identification)

hhGoodPeriodizedKernelUniformBridgeClosed : Bool
hhGoodPeriodizedKernelUniformBridgeClosed = true

physicalStrainShellKernelMassIdentificationConstructed : Bool
physicalStrainShellKernelMassIdentificationConstructed = false

hhGoodPeriodizedKernelUniformBridgeClosedIsTrue :
  hhGoodPeriodizedKernelUniformBridgeClosed ≡ true
hhGoodPeriodizedKernelUniformBridgeClosedIsTrue = refl
