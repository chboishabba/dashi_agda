module DASHI.Physics.Closure.NSTriadKNEigenpacketRadialTransferCoherenceRound101Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- Springer, 2011.
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- AMS Chelsea Publishing, 2001 reprint.
-- DOI: 10.1090/chel/343.
--
-- ROUND101 / EXACT RADIAL TRANSFER-COHERENCE FACTORIZATION
--
-- Round101 exposed that exact-eigenvalue relative-growth estimates do not
-- recombine automatically.  This module identifies the obstruction exactly.
--
-- For two radii set
--
--   E = E1+E2,
--   q = q1+q2,
--   D = lambda1 E1 + lambda2 E2,
--   L = lambda1 q1 + lambda2 q2.
--
-- The quantity
--
--   C = D q - E L
--
-- measures failure of the transfer density q/E to be coherent across radii
-- without ever dividing by E.  It factorizes as
--
--   C = (lambda1-lambda2)(E1 q2 - E2 q1).
--
-- Hence the only cross-radius obstruction is simultaneously radial and
-- transfer-density noncoherence.  If
--
--   E1 q2 = E2 q1,
--
-- then C=0 for arbitrary eigenvalues.
--
-- More importantly, if
--
--   R = qdot D - 2 q L
--
-- is the recombined relative-growth numerator, then
--
--   E R = D (E qdot - 2 q^2) + 2 q C.
--
-- Therefore radial transfer coherence gives the exact division-free descent
--
--   E R = D (E qdot - 2 q^2).
--
-- This is stronger and more useful than saying "Parseval should recombine".
-- It names the exact theorem that would make eigenpacket recombination safe.
-- No positivity, estimate, continuum passage, or PDE receipt is assumed here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field

private
  two : ∀ {r} (F : C3.RealField r) → C3.Carrier F
  two F = C3.add F (C3.one F) (C3.one F)

  sub : ∀ {r} {F : C3.RealField r} →
    C3.Carrier F → C3.Carrier F → C3.Carrier F
  sub {F = F} x y = C3.add F x (C3.negate F y)

record TwoRadiusTransferData {r} (F : C3.RealField r) : Set r where
  field
    lambda1 lambda2 : C3.Carrier F
    energy1 energy2 : C3.Carrier F
    transfer1 transfer2 : C3.Carrier F
    transferTangent : C3.Carrier F

open TwoRadiusTransferData public

totalEnergy : ∀ {r} {F : C3.RealField r} → TwoRadiusTransferData F → C3.Carrier F
totalEnergy {F = F} D = C3.add F (energy1 D) (energy2 D)

totalTransfer : ∀ {r} {F : C3.RealField r} → TwoRadiusTransferData F → C3.Carrier F
totalTransfer {F = F} D = C3.add F (transfer1 D) (transfer2 D)

weightedEnergy : ∀ {r} {F : C3.RealField r} → TwoRadiusTransferData F → C3.Carrier F
weightedEnergy {F = F} D =
  C3.add F
    (C3.multiply F (lambda1 D) (energy1 D))
    (C3.multiply F (lambda2 D) (energy2 D))

weightedTransfer : ∀ {r} {F : C3.RealField r} → TwoRadiusTransferData F → C3.Carrier F
weightedTransfer {F = F} D =
  C3.add F
    (C3.multiply F (lambda1 D) (transfer1 D))
    (C3.multiply F (lambda2 D) (transfer2 D))

radialTransferCoherenceDefect :
  ∀ {r} {F : C3.RealField r} → TwoRadiusTransferData F → C3.Carrier F
radialTransferCoherenceDefect {F = F} D =
  sub
    (C3.multiply F (weightedEnergy D) (totalTransfer D))
    (C3.multiply F (totalEnergy D) (weightedTransfer D))

crossTransferDensityMinor :
  ∀ {r} {F : C3.RealField r} → TwoRadiusTransferData F → C3.Carrier F
crossTransferDensityMinor {F = F} D =
  sub
    (C3.multiply F (energy1 D) (transfer2 D))
    (C3.multiply F (energy2 D) (transfer1 D))

radialTransferCoherenceDefectFactorization :
  ∀ {r} {F : C3.RealField r} (D : TwoRadiusTransferData F) →
  radialTransferCoherenceDefect D
  ≡ C3.multiply F
      (sub (lambda1 D) (lambda2 D))
      (crossTransferDensityMinor D)
radialTransferCoherenceDefectFactorization {F = F} D =
  P.R.solve 6
    (λ l1 l2 e1 e2 q1 q2 →
      ((((l1 P.R.⊗ e1) P.R.⊕ (l2 P.R.⊗ e2)) P.R.⊗ (q1 P.R.⊕ q2))
        P.R.⊕ P.R.⊝
          ((e1 P.R.⊕ e2) P.R.⊗ ((l1 P.R.⊗ q1) P.R.⊕ (l2 P.R.⊗ q2))))
      P.R.⊜
      ((l1 P.R.⊕ P.R.⊝ l2)
        P.R.⊗ ((e1 P.R.⊗ q2) P.R.⊕ P.R.⊝ (e2 P.R.⊗ q1))))
    refl
    (lambda1 D) (lambda2 D)
    (energy1 D) (energy2 D)
    (transfer1 D) (transfer2 D)
  where module P = Field.Polynomial F

recombinedRelativeGrowth :
  ∀ {r} {F : C3.RealField r} → TwoRadiusTransferData F → C3.Carrier F
recombinedRelativeGrowth {F = F} D =
  sub
    (C3.multiply F (transferTangent D) (weightedEnergy D))
    (C3.multiply F
      (two F)
      (C3.multiply F (totalTransfer D) (weightedTransfer D)))

unweightedRelativeGrowth :
  ∀ {r} {F : C3.RealField r} → TwoRadiusTransferData F → C3.Carrier F
unweightedRelativeGrowth {F = F} D =
  sub
    (C3.multiply F (totalEnergy D) (transferTangent D))
    (C3.multiply F
      (two F)
      (C3.multiply F (totalTransfer D) (totalTransfer D)))

relativeGrowthRecombinationIdentity :
  ∀ {r} {F : C3.RealField r} (D : TwoRadiusTransferData F) →
  C3.multiply F (totalEnergy D) (recombinedRelativeGrowth D)
  ≡ C3.add F
      (C3.multiply F (weightedEnergy D) (unweightedRelativeGrowth D))
      (C3.multiply F
        (two F)
        (C3.multiply F
          (totalTransfer D)
          (radialTransferCoherenceDefect D)))
relativeGrowthRecombinationIdentity {F = F} D =
  P.R.solve 5
    (λ e q d qdot l →
      (e P.R.⊗ ((qdot P.R.⊗ d) P.R.⊕ P.R.⊝ ((P.R.K (two F)) P.R.⊗ (q P.R.⊗ l))))
      P.R.⊜
      ((d P.R.⊗ ((e P.R.⊗ qdot) P.R.⊕ P.R.⊝ ((P.R.K (two F)) P.R.⊗ (q P.R.⊗ q))))
        P.R.⊕
        ((P.R.K (two F)) P.R.⊗ (q P.R.⊗ ((d P.R.⊗ q) P.R.⊕ P.R.⊝ (e P.R.⊗ l)))))
    refl
    (totalEnergy D)
    (totalTransfer D)
    (weightedEnergy D)
    (transferTangent D)
    (weightedTransfer D)
  where module P = Field.Polynomial F

transferDensityCoherent :
  ∀ {r} {F : C3.RealField r} → TwoRadiusTransferData F → Set
transferDensityCoherent {F = F} D =
  C3.multiply F (energy1 D) (transfer2 D)
  ≡ C3.multiply F (energy2 D) (transfer1 D)

coherentTransferDensityKillsRadialDefect :
  ∀ {r} {F : C3.RealField r} (D : TwoRadiusTransferData F) →
  transferDensityCoherent D →
  radialTransferCoherenceDefect D ≡ C3.zero F
coherentTransferDensityKillsRadialDefect {F = F} D coherent
  rewrite radialTransferCoherenceDefectFactorization D
        | coherent =
  P.R.solve 2
    (λ delta z → delta P.R.⊗ (z P.R.⊕ P.R.⊝ z) P.R.⊜ P.R.K (C3.zero F))
    refl
    (sub (lambda1 D) (lambda2 D))
    (C3.multiply F (energy2 D) (transfer1 D))
  where module P = Field.Polynomial F

coherentTransferDensityGivesExactRecombination :
  ∀ {r} {F : C3.RealField r} (D : TwoRadiusTransferData F) →
  transferDensityCoherent D →
  C3.multiply F (totalEnergy D) (recombinedRelativeGrowth D)
  ≡ C3.multiply F (weightedEnergy D) (unweightedRelativeGrowth D)
coherentTransferDensityGivesExactRecombination {F = F} D coherent
  rewrite relativeGrowthRecombinationIdentity D
        | coherentTransferDensityKillsRadialDefect D coherent =
  P.R.solve 2
    (λ main q →
      (main P.R.⊕ ((P.R.K (two F)) P.R.⊗ (q P.R.⊗ P.R.K (C3.zero F))))
      P.R.⊜ main)
    refl
    (C3.multiply F (weightedEnergy D) (unweightedRelativeGrowth D))
    (totalTransfer D)
  where module P = Field.Polynomial F

round101CrossRadiusObstructionFactorsThroughTransferDensityMinor : Bool
round101CrossRadiusObstructionFactorsThroughTransferDensityMinor = true

round101RadialTransferCoherenceRestoresExactRecombination : Bool
round101RadialTransferCoherenceRestoresExactRecombination = true

round101ParsevalAloneRestoresExactRecombination : Bool
round101ParsevalAloneRestoresExactRecombination = false

round101RadialTransferCoherenceRestoresExactRecombinationIsTrue :
  round101RadialTransferCoherenceRestoresExactRecombination ≡ true
round101RadialTransferCoherenceRestoresExactRecombinationIsTrue = refl
