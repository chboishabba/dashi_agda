module DASHI.Physics.Closure.NSTriadKNNineOwnerExactGoNoGoRound43Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCE / CONTEXT
--
-- Author: Gyula Farkas.
-- Title: "Theorie der einfachen Ungleichungen".
-- Journal fuer die reine und angewandte Mathematik 124 (1902), 1--27.
-- DOI: no DOI assigned to the historical article.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- DASHI CONTRIBUTION
--
-- Make the owner-reserve architecture gate executable at the theorem level.
-- The primal and dual lanes previously used different carriers: the physical
-- family stores nine AdmissibleOwnerEstimate values, while the Farkas theorem
-- uses a NineVector.  This file proves the exact carrier identification and
-- then proves that an applicable dual no-go certificate and a strict physical
-- owner budget cannot coexist.
--
-- Thus the prescribed decision is now literal:
--
--   primal strict budget  => continue;
--   exact dual certificate applicable to the same eta vector => redesign.
--
-- A numerical optimizer is neither trusted nor required by this theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (1ℚ; _<_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym)
open import Relation.Nullary.Negation using (¬_)

import DASHI.Physics.Closure.NSTriadKNAdmissibleOwnerTaxLanguageRound28Exact as Owner
import DASHI.Physics.Closure.NSTriadKNNineOwnerDualNoGoRound39Exact as Dual

familyEtaVector :
  ∀ {environment} →
  Owner.NineOwnerEstimateFamily environment → Dual.NineVector
familyEtaVector family = Dual.nine-vector
  (Owner.eta (Owner.hhGood family))
  (Owner.eta (Owner.hhBad family))
  (Owner.eta (Owner.lh family))
  (Owner.eta (Owner.hl family))
  (Owner.eta (Owner.cc family))
  (Owner.eta (Owner.com family))
  (Owner.eta (Owner.kernel family))
  (Owner.eta (Owner.tail family))
  (Owner.eta (Owner.boundary family))

familyEtaTotalMatchesOwnerList :
  ∀ {environment}
    (family : Owner.NineOwnerEstimateFamily environment) →
  Dual.etaTotal (familyEtaVector family)
  ≡ Owner.sumEta (Owner.nineOwnerList family)
familyEtaTotalMatchesOwnerList family =
  solve
    ( Owner.eta (Owner.hhGood family)
    ∷ Owner.eta (Owner.hhBad family)
    ∷ Owner.eta (Owner.lh family)
    ∷ Owner.eta (Owner.hl family)
    ∷ Owner.eta (Owner.cc family)
    ∷ Owner.eta (Owner.com family)
    ∷ Owner.eta (Owner.kernel family)
    ∷ Owner.eta (Owner.tail family)
    ∷ Owner.eta (Owner.boundary family)
    ∷ [])

strictBudgetGivesEtaVectorStrict :
  ∀ {environment}
    (family : Owner.NineOwnerEstimateFamily environment) →
  Owner.StrictAdmissibleOwnerBudget (Owner.nineOwnerList family) →
  Dual.etaTotal (familyEtaVector family) < 1ℚ
strictBudgetGivesEtaVectorStrict family budget =
  subst
    (λ total → total < 1ℚ)
    (sym (familyEtaTotalMatchesOwnerList family))
    (Owner.totalEtaStrict budget)

dualNoGoRefutesStrictPhysicalBudget :
  ∀ {environment}
    (family : Owner.NineOwnerEstimateFamily environment) →
  (certificate : Dual.NineOwnerDualNoGoCertificate) →
  Dual.SatisfiesDualCells
    (familyEtaVector family) (Dual.cells certificate) →
  ¬ Owner.StrictAdmissibleOwnerBudget (Owner.nineOwnerList family)
dualNoGoRefutesStrictPhysicalBudget family certificate feasible budget =
  let
    lower : 1ℚ ≤ Dual.etaTotal (familyEtaVector family)
    lower = Dual.dualCertificateForcesEtaTotalAtLeastOne
      certificate (familyEtaVector family) feasible

    strict : Dual.etaTotal (familyEtaVector family) < 1ℚ
    strict = strictBudgetGivesEtaVectorStrict family budget

    impossible : 1ℚ < 1ℚ
    impossible = ℚP.≤-<-trans lower strict
  in
  ℚP.<-irrefl refl impossible
  where
  open import Data.Rational.Base using (_≤_)

nineOwnerPrimalDualCarrierIdentificationClosed : Bool
nineOwnerPrimalDualCarrierIdentificationClosed = true

exactNineOwnerGoNoGoGateClosed : Bool
exactNineOwnerGoNoGoGateClosed = true

nineOwnerPrimalDualCarrierIdentificationClosedIsTrue :
  nineOwnerPrimalDualCarrierIdentificationClosed ≡ true
nineOwnerPrimalDualCarrierIdentificationClosedIsTrue = refl

exactNineOwnerGoNoGoGateClosedIsTrue :
  exactNineOwnerGoNoGoGateClosed ≡ true
exactNineOwnerGoNoGoGateClosedIsTrue = refl
