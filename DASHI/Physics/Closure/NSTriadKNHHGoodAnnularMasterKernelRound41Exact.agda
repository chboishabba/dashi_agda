module DASHI.Physics.Closure.NSTriadKNHHGoodAnnularMasterKernelRound41Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- Springer, 2011.
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier-Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- DASHI CONTRIBUTION
--
-- Round 40 correctly isolated the remaining HH-good kernel theorem as the
-- matrix-valued smooth annular strain multiplier, not Luo's scalar radial
-- low-pass kernel.  This file decomposes that theorem into the three exact
-- same-object-sensitive steps suggested by the continuation analysis:
--
--   (1) annular shell kernel = scaled master kernel;
--   (2) Euclidean L1 mass is invariant under K_q(x)=r^3 K(r x);
--   (3) canonical periodization cannot increase L1 mass.
--
-- The finite algebra underlying (2) and (3) is proved here rather than stored
-- as prose.  The only remaining analytic authority is the continuum
-- identification of the literal inverse Fourier transform with this master
-- kernel/change-of-variables package.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; trans)

import DASHI.Physics.Closure.NSTriadKNLuoBadCoherenceWeightedMarkovExact as Threshold
import DASHI.Physics.Closure.NSTriadKNHHGoodPeriodizedKernelUniformRound40Exact as Periodized

------------------------------------------------------------------------
-- Exact Jacobian cancellation for an order-zero annular master kernel.
------------------------------------------------------------------------

scaledKernelJacobianMass : Threshold.PositiveThreshold → ℚ → ℚ
scaledKernelJacobianMass scale mass =
  Threshold.threshold scale
  * Threshold.threshold scale
  * Threshold.threshold scale
  * mass
  * Threshold.thresholdInverse scale
  * Threshold.thresholdInverse scale
  * Threshold.thresholdInverse scale

scaledKernelJacobianMassInvariant :
  ∀ scale mass → scaledKernelJacobianMass scale mass ≡ mass
scaledKernelJacobianMassInvariant scale mass =
  let
    r = Threshold.threshold scale
    rinv = Threshold.thresholdInverse scale

    regroup :
      r * r * r * mass * rinv * rinv * rinv
      ≡ mass * (rinv * r) * (rinv * r) * (rinv * r)
    regroup = solve (r ∷ rinv ∷ mass ∷ [])
  in
  trans regroup
    (trans
      (cong
        (λ reciprocal → mass * reciprocal * reciprocal * reciprocal)
        (Threshold.inverseMeaning scale))
      (solve (mass ∷ [])))

sumMass : List ℚ → ℚ
sumMass [] = 0ℚ
sumMass (mass ∷ rest) = mass + sumMass rest

scaledMasses : Threshold.PositiveThreshold → List ℚ → List ℚ
scaledMasses scale [] = []
scaledMasses scale (mass ∷ rest) =
  scaledKernelJacobianMass scale mass ∷ scaledMasses scale rest

finiteScaledKernelMassInvariant :
  ∀ scale masses → sumMass (scaledMasses scale masses) ≡ sumMass masses
finiteScaledKernelMassInvariant scale [] = refl
finiteScaledKernelMassInvariant scale (mass ∷ rest)
  rewrite scaledKernelJacobianMassInvariant scale mass
        | finiteScaledKernelMassInvariant scale rest = refl

------------------------------------------------------------------------
-- Finite periodization triangle theorem.
------------------------------------------------------------------------

record FinitePeriodizationCell : Set where
  field
    torusMagnitude : ℚ
    liftMagnitudes : List ℚ
    torusMagnitudeNonnegative : 0ℚ ≤ torusMagnitude
    liftMassNonnegative : 0ℚ ≤ sumMass liftMagnitudes
    torusBelowLiftMass : torusMagnitude ≤ sumMass liftMagnitudes

open FinitePeriodizationCell public

finiteTorusMass finiteLiftMass : List FinitePeriodizationCell → ℚ
finiteTorusMass [] = 0ℚ
finiteTorusMass (cell ∷ rest) =
  torusMagnitude cell + finiteTorusMass rest

finiteLiftMass [] = 0ℚ
finiteLiftMass (cell ∷ rest) =
  sumMass (liftMagnitudes cell) + finiteLiftMass rest

finitePeriodizationL1Contraction :
  ∀ cells → finiteTorusMass cells ≤ finiteLiftMass cells
finitePeriodizationL1Contraction [] = ℚP.≤-refl
finitePeriodizationL1Contraction (cell ∷ rest) =
  ℚP.+-mono-≤
    (torusBelowLiftMass cell)
    (finitePeriodizationL1Contraction rest)

------------------------------------------------------------------------
-- Exact decomposition of the Round-40 analytic authority.
------------------------------------------------------------------------

record AnnularMasterKernelL1Package
    {st : Level}
    (TorusPoint : Set st) : Set (lsuc st) where
  field
    euclideanShellL1Norm : Nat → ℚ
    torusShellL1Norm : Nat → ℚ
    masterL1Norm : ℚ

    masterL1Nonnegative : 0ℚ ≤ masterL1Norm

    shellIsScaledMaster : (shell : Nat) →
      euclideanShellL1Norm shell ≡ masterL1Norm

    periodizationContraction : (shell : Nat) →
      torusShellL1Norm shell ≤ euclideanShellL1Norm shell

    AnnularMultiplierIsLiteralStrainMultiplier : Set st
    annularMultiplierIsLiteralStrainMultiplier :
      AnnularMultiplierIsLiteralStrainMultiplier

    MasterKernelIsInverseFourierTransform : Set st
    masterKernelIsInverseFourierTransform : MasterKernelIsInverseFourierTransform

    AnnularCutoffSmoothCompactAwayFromZero : Set st
    annularCutoffSmoothCompactAwayFromZero :
      AnnularCutoffSmoothCompactAwayFromZero

    MasterKernelL1BySchwartzDecay : Set st
    masterKernelL1BySchwartzDecay : MasterKernelL1BySchwartzDecay

    CanonicalTorusPeriodization : Set st
    canonicalTorusPeriodization : CanonicalTorusPeriodization

open AnnularMasterKernelL1Package public

periodizedBoundFromMasterPackage :
  ∀ {st} {TorusPoint : Set st}
    (package : AnnularMasterKernelL1Package TorusPoint) →
  (shell : Nat) →
  torusShellL1Norm package shell ≤ masterL1Norm package
periodizedBoundFromMasterPackage package shell =
  ℚP.≤-trans
    (periodizationContraction package shell)
    (subst
      (λ upper → euclideanShellL1Norm package shell ≤ upper)
      (shellIsScaledMaster package shell)
      ℚP.≤-refl)

round40KernelTheoremFromMasterPackage :
  ∀ {st} {TorusPoint : Set st} →
  AnnularMasterKernelL1Package TorusPoint →
  Periodized.PeriodizedAnnularStrainKernelL1Theorem TorusPoint
round40KernelTheoremFromMasterPackage package = record
  { strainShellKernelL1Norm = torusShellL1Norm package
  ; masterAnnularStrainKernelL1Norm = masterL1Norm package
  ; masterAnnularStrainKernelL1Nonnegative = masterL1Nonnegative package
  ; periodizedStrainKernelL1BoundUniformInShell =
      periodizedBoundFromMasterPackage package
  ; AnnularCutoffSmoothAndCompactlySupportedAwayFromZero =
      AnnularCutoffSmoothCompactAwayFromZero package
  ; annularCutoffSmoothAndCompactlySupportedAwayFromZero =
      annularCutoffSmoothCompactAwayFromZero package
  ; MasterAnnularStrainKernelIsL1 = MasterKernelL1BySchwartzDecay package
  ; masterAnnularStrainKernelIsL1 = masterKernelL1BySchwartzDecay package
  ; PeriodizationFormulaIsCanonical = CanonicalTorusPeriodization package
  ; periodizationFormulaIsCanonical = canonicalTorusPeriodization package
  }

annularMasterKernelScalingAlgebraClosed : Bool
annularMasterKernelScalingAlgebraClosed = true

finitePeriodizationL1ContractionClosed : Bool
finitePeriodizationL1ContractionClosed = true

physicalAnnularMasterKernelSameObjectPackageConstructed : Bool
physicalAnnularMasterKernelSameObjectPackageConstructed = false

annularMasterKernelScalingAlgebraClosedIsTrue :
  annularMasterKernelScalingAlgebraClosed ≡ true
annularMasterKernelScalingAlgebraClosedIsTrue = refl

finitePeriodizationL1ContractionClosedIsTrue :
  finitePeriodizationL1ContractionClosed ≡ true
finitePeriodizationL1ContractionClosedIsTrue = refl
