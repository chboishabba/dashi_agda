module DASHI.Physics.YangMills.BalabanSelectedFlatGaugeGreenAbsoluteMassExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- J. M. Combes and L. Thomas,
-- "Asymptotic Behaviour of Eigenfunctions for Multiparticle Schrödinger
-- Operators", Communications in Mathematical Physics 34 (1973), 251--270.
-- DOI: 10.1007/BF01646473.
--
-- DASHI CONTRIBUTION
--
-- Evaluate, rather than estimate abstractly, the absolute l1 mass of the exact
-- 256-site Fourier Green kernel already used by the selected flat gauge Gram:
--
--   sum_x |G_0(x)| = 74077 / 71680 < 17/16.
--
-- This is a useful quantitative fact for the next literal `G_0 E_A` route:
-- the flat Green has only about 3.34 percent absolute-row overhead on the
-- configured side-four torus.  The equality is checked by closed rational
-- computation over all 256 offsets, using the same proof-bearing finite
-- enumeration as the Green equation itself.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational using (ℚ; 0ℚ; _-_; _≤_; _/_; ∣_∣)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
import Relation.Nullary.Decidable.Core as StdDec
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanConfiguredSide4PeriodicReindexingExact as Reindex
import DASHI.Physics.YangMills.BalabanSide4ScalarGreenKernelComputed as Kernel

scalarGreenAbsoluteMass : ℚ
scalarGreenAbsoluteMass =
  Reindex.siteSum4 (λ offset → ∣ Kernel.scalarGreenKernel offset ∣)

scalarGreenAbsoluteMassExactValue : ℚ
scalarGreenAbsoluteMassExactValue = + 74077 / 71680

scalarGreenAbsoluteMassDecision :
  StdDec.Dec (scalarGreenAbsoluteMass ≡ scalarGreenAbsoluteMassExactValue)
scalarGreenAbsoluteMassDecision =
  ℚP._≟_ scalarGreenAbsoluteMass scalarGreenAbsoluteMassExactValue

scalarGreenAbsoluteMassDecisionIsYes :
  Kernel.IsYes scalarGreenAbsoluteMassDecision
scalarGreenAbsoluteMassDecisionIsYes = Kernel.isYes

scalarGreenAbsoluteMassExact :
  scalarGreenAbsoluteMass ≡ scalarGreenAbsoluteMassExactValue
scalarGreenAbsoluteMassExact =
  Kernel.extractYes
    scalarGreenAbsoluteMassDecision
    scalarGreenAbsoluteMassDecisionIsYes

seventeenSixteenths : ℚ
seventeenSixteenths = + 17 / 16

scalarGreenAbsoluteMassExactValueBelowSeventeenSixteenths :
  scalarGreenAbsoluteMassExactValue ≤ seventeenSixteenths
scalarGreenAbsoluteMassExactValueBelowSeventeenSixteenths =
  Norm.nonnegativeDifferenceImpliesBelow
    (subst
      (λ difference → 0ℚ ≤ difference)
      (sym
        (ℚRing.solve [] :
          seventeenSixteenths - scalarGreenAbsoluteMassExactValue
          ≡ + 2083 / 71680))
      (ℚP.nonNegative⁻¹ (+ 2083 / 71680)))

scalarGreenAbsoluteMassBelowSeventeenSixteenths :
  scalarGreenAbsoluteMass ≤ seventeenSixteenths
scalarGreenAbsoluteMassBelowSeventeenSixteenths =
  subst
    (λ mass → mass ≤ seventeenSixteenths)
    (sym scalarGreenAbsoluteMassExact)
    scalarGreenAbsoluteMassExactValueBelowSeventeenSixteenths

selectedFlatGaugeGreenAbsoluteMassComputedLevel : ProofLevel
selectedFlatGaugeGreenAbsoluteMassComputedLevel = machineChecked

selectedFlatGaugeGreenAbsoluteMassBoundLevel : ProofLevel
selectedFlatGaugeGreenAbsoluteMassBoundLevel = machineChecked
