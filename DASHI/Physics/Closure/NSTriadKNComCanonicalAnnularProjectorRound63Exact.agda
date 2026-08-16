module DASHI.Physics.Closure.NSTriadKNComCanonicalAnnularProjectorRound63Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean-Michel Bony.
-- Title: "Calcul symbolique et propagation des singularites pour les
-- equations aux derivees partielles non lineaires".
-- DOI: 10.24033/asens.1404.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator Estimates and the Euler and Navier-Stokes Equations".
-- DOI: 10.1002/cpa.3160410704.
--
-- ROUND 63 / B0
--
-- Construct the annular/hatted projector that Round62 proved was necessary.
-- On the canonical hard-shell selector, low-pass membership is
--
--     chi_{<=s}(j) = [j <= s]
--
-- while annular membership is
--
--     delta_s(j) = [j = s].
--
-- In the exact Fourier scalar carrier we prove
--
--     P_{<=0} = Delta_0,
--     P_{<=s+1} - P_{<=s} = Delta_{s+1}.
--
-- Thus the hatted pieces are not an abstract support certificate: they are the
-- literal successive differences of the nested hard low-pass projectors.  The
-- remaining B0 step is to apply these masks to the centered transport
-- commutator/output fibre and prove its post-localization common-hat support.
------------------------------------------------------------------------

open import Agda.Primitive using (Level)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComLiteralOddPQCommutatorIdentityRound62Exact as Comm

annularGrade :
  ∀ {r} (F : C3.RealField r) → Nat → Nat → C3.Complex F
annularGrade F shell modeShell =
  Comm.projectorGrade F (Output.natEqual modeShell shell)

lowGrade :
  ∀ {r} (F : C3.RealField r) → Nat → Nat → C3.Complex F
lowGrade F cutoff modeShell =
  Comm.projectorGrade F (Physical.natLeBool modeShell cutoff)

baseLowPassIsZeroAnnulus :
  ∀ {r} (F : C3.RealField r) (modeShell : Nat) →
  lowGrade F zero modeShell ≡ annularGrade F zero modeShell
baseLowPassIsZeroAnnulus F zero = refl
baseLowPassIsZeroAnnulus F (suc modeShell) = refl

successiveLowPassDifferenceIsAnnulus :
  ∀ {r} (F : C3.RealField r) (modeShell cutoff : Nat) →
  C3.complexSubtract
    (lowGrade F (suc cutoff) modeShell)
    (lowGrade F cutoff modeShell)
  ≡ annularGrade F (suc cutoff) modeShell
successiveLowPassDifferenceIsAnnulus F zero zero = Comm.oneMinusOne
successiveLowPassDifferenceIsAnnulus F zero (suc cutoff) = Comm.oneMinusOne
successiveLowPassDifferenceIsAnnulus F (suc zero) zero = Comm.oneMinusZero
successiveLowPassDifferenceIsAnnulus F (suc (suc modeShell)) zero =
  Comm.zeroMinusZero
successiveLowPassDifferenceIsAnnulus F (suc modeShell) (suc cutoff) =
  successiveLowPassDifferenceIsAnnulus F modeShell cutoff

annularGradeOnOwnShell :
  ∀ {r} (F : C3.RealField r) (shell : Nat) →
  annularGrade F shell shell ≡ C3.complexOne F
annularGradeOnOwnShell F zero = refl
annularGradeOnOwnShell F (suc shell) = annularGradeOnOwnShell F shell

annularGradeBelowShellZero :
  ∀ {r} (F : C3.RealField r) (lower : Nat) →
  annularGrade F (suc lower) zero ≡ C3.complexZero F
annularGradeBelowShellZero F lower = refl

round63CanonicalAnnularProjectorConstructedFromLowPassDifferences : Bool
round63CanonicalAnnularProjectorConstructedFromLowPassDifferences = true

round63CanonicalAnnularProjectorConstructedFromLowPassDifferencesIsTrue :
  round63CanonicalAnnularProjectorConstructedFromLowPassDifferences ≡ true
round63CanonicalAnnularProjectorConstructedFromLowPassDifferencesIsTrue = refl
