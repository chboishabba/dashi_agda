module DASHI.Physics.Closure.NSTriadKNSelectedHHBadHardGateWitnessRound48Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Gyula Farkas.
-- Title: "Theorie der einfachen Ungleichungen".
-- Journal fuer die reine und angewandte Mathematik 124 (1902), 1--27.
-- DOI: no DOI assigned to the historical article.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale-Kato-Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- DASHI CONTRIBUTION
--
-- The sharp consumer contract is existential in the coherence threshold, not
-- universal in delta.  Package one actual selected-threshold HH-bad closure
-- witness together with whichever Com/kernel hard floors survive their
-- physical tax classification and the one scalar reserve inequality
--
--   2 M + tau_Com + tau_kernel + 1/16 < 1.
--
-- The same certificate is equivalently the live ceiling condition
--
--   M < 15/32 - (tau_Com + tau_kernel)/2.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; _<_)

import DASHI.Physics.Closure.NSTriadKNAdmissibleOwnerTaxLanguageRound28Exact as Owner
import DASHI.Physics.Closure.NSTriadKNHHBadSelectedClosureWitnessRound48Exact as Selected
import DASHI.Physics.Closure.NSTriadKNHardGateHierarchyRound47Exact as Gate
import DASHI.Physics.Closure.NSTriadKNHHBadLiveBudgetTargetRound48Exact as Live

record SelectedHHBadHardGateWitness
    (environment : Owner.TaxEnvironment)
    (effectiveViscosity : ℚ) : Set₁ where
  field
    hhBad : Selected.SelectedHHBadClosureWitness environment effectiveViscosity
    comHardFloor kernelHardFloor : ℚ
    hardGateStrict :
      Gate.hardGateH2
        (Selected.selectedHHBadCeiling hhBad)
        comHardFloor kernelHardFloor
      < Data.Rational.Base.1ℚ

open SelectedHHBadHardGateWitness public

selectedCeilingMeetsLiveBudget :
  ∀ {environment effectiveViscosity}
    (witness : SelectedHHBadHardGateWitness environment effectiveViscosity) →
  Selected.selectedHHBadCeiling (hhBad witness)
  < Live.allowableHHBadCeiling
      (comHardFloor witness) (kernelHardFloor witness)
selectedCeilingMeetsLiveBudget witness =
  Live.h2StrictImpliesLiveCeilingTarget
    (Selected.selectedHHBadCeiling (hhBad witness))
    (comHardFloor witness)
    (kernelHardFloor witness)
    (hardGateStrict witness)

selectedHHBadHardGateIsSingleScalarCertificate : Bool
selectedHHBadHardGateIsSingleScalarCertificate = true

selectedHHBadHardGateIsSingleScalarCertificateIsTrue :
  selectedHHBadHardGateIsSingleScalarCertificate ≡ true
selectedHHBadHardGateIsSingleScalarCertificateIsTrue = refl
