module DASHI.Physics.YangMills.BalabanP33InverseLinkRadiusDoesNotImplyWLocalExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Kenneth G. Wilson,
-- "Confinement of Quarks", Physical Review D 10 (1974), 2445--2459.
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DASHI COUNTER-AUDIT
--
-- The selected-background theorem may use substantially more structure than a
-- bondwise radius.  This distinction is essential: the relaxed inverse-link
-- radius by itself does NOT imply the proposed local Wilson allocation
--
--   defect_p >= -(rho/36) C_p -(rho/144) q_p.
--
-- The present module gives an exact rational four-link Wilson counterexample.
-- One link is the rational unit quaternion obtained from the stereographic
-- parameter t=1/16384, the other links are the identity, and two orthogonal
-- insertion vectors occupy the first two positive links.  It proves:
--
--   N(U^-1-1) = 4/268435457 <= 4 rho^2,
--   q_p = 2,
--   C_p = 6,
--   H_W(U;h)-H_W(1;h) = -65540/268435457,
--
-- while the proposed local budget is only 13/589824.  The exact positive
-- violation gap is
--
--   -defect_p - budget_p
--     = 35167404019/158329674989568 > 0.
--
-- Consequently A2 cannot be discharged from A1 alone.  A correct proof must
-- exploit additional selected-background correlations (plaquette curvature,
-- variational equations, gauge conditions, or a stronger radius) and expose
-- them explicitly.  This module prevents a false radius-only bridge from being
-- installed in the physical proof chain.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _-_; _*_; -_; _≤_; _<_; _/_; Positive)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Q
import DASHI.Physics.YangMills.BalabanP33LiteralGaugeConstraintSecondVariationExact as Jets
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeParameterizedYoungExact as Relaxed

------------------------------------------------------------------------
-- Exact rational unit link and tangent insertions.
------------------------------------------------------------------------

stereographicDenominator : ℚ
stereographicDenominator = + 268435457 / 1

counterLink : Q.RationalQuaternion
counterLink = Q.quat
  (+ 268435455 / 268435457)
  (+ 32768 / 268435457)
  0ℚ 0ℚ

counterLinkInverse : Q.RationalQuaternion
counterLinkInverse = Q.quat
  (+ 268435455 / 268435457)
  (- (+ 32768 / 268435457))
  0ℚ 0ℚ

counterLinkUnitNorm :
  Norm.normSq counterLink ≡ + 1 / 1
counterLinkUnitNorm = ℚRing.solve []

counterLinkInverseUnitNorm :
  Norm.normSq counterLinkInverse ≡ + 1 / 1
counterLinkInverseUnitNorm = ℚRing.solve []

counterInsertion0 counterInsertion1 : Q.RationalQuaternion
counterInsertion0 = Q.quat 0ℚ 0ℚ (+ 1 / 1) 0ℚ
counterInsertion1 = Q.quat 0ℚ 0ℚ 0ℚ (- (+ 1 / 1))

zeroInsertion : Q.RationalQuaternion
zeroInsertion = Q.zeroQ

positiveJet : Q.RationalQuaternion → Q.RationalQuaternion → Q.QuaternionFactorJet
positiveJet background insertion = Q.factorJet
  background
  (background Q.*q insertion)
  (background Q.*q (insertion Q.*q insertion))

zeroIdentityJet : Q.QuaternionFactorJet
zeroIdentityJet = Q.factorJet Q.oneQ Q.zeroQ Q.zeroQ

counterPlaquetteJet : Jets.PlaquetteSecondJet
counterPlaquetteJet = Jets.plaquetteJet
  (positiveJet counterLink counterInsertion0)
  (positiveJet Q.oneQ counterInsertion1)
  zeroIdentityJet
  zeroIdentityJet

flatCounterPlaquetteJet : Jets.PlaquetteSecondJet
flatCounterPlaquetteJet = Jets.plaquetteJet
  (positiveJet Q.oneQ counterInsertion0)
  (positiveJet Q.oneQ counterInsertion1)
  zeroIdentityJet
  zeroIdentityJet

------------------------------------------------------------------------
-- Radius, local charges, and exact Wilson defect.
------------------------------------------------------------------------

counterInverseLinkDefect : Q.RationalQuaternion
counterInverseLinkDefect =
  counterLinkInverse Q.+q Q.negQ Q.oneQ

counterInverseLinkDefectSq : ℚ
counterInverseLinkDefectSq = Norm.normSq counterInverseLinkDefect

counterInverseLinkDefectSqExact :
  counterInverseLinkDefectSq ≡ + 4 / 268435457
counterInverseLinkDefectSqExact = ℚRing.solve []

relaxedRadiusSquare : ℚ
relaxedRadiusSquare = (+ 4 / 1) * Relaxed.rho * Relaxed.rho

relaxedRadiusSlack : ℚ
relaxedRadiusSlack =
  relaxedRadiusSquare - counterInverseLinkDefectSq

relaxedRadiusSlackExact :
  relaxedRadiusSlack ≡ + 201326593 / 4503599644147712
relaxedRadiusSlackExact = ℚRing.solve []

relaxedRadiusSlackNonnegative : 0ℚ ≤ relaxedRadiusSlack
relaxedRadiusSlackNonnegative =
  subst
    (λ selected → 0ℚ ≤ selected)
    (sym relaxedRadiusSlackExact)
    (ℚP.nonNegative⁻¹ (+ 201326593 / 4503599644147712))

counterSatisfiesRelaxedInverseLinkRadius :
  counterInverseLinkDefectSq ≤ relaxedRadiusSquare
counterSatisfiesRelaxedInverseLinkRadius =
  Norm.nonnegativeDifferenceImpliesBelow relaxedRadiusSlackNonnegative

counterDiagonalCharge : ℚ
counterDiagonalCharge = + 2 / 1

counterCrossCharge : ℚ
counterCrossCharge = + 6 / 1

counterWilsonBackgroundValue : ℚ
counterWilsonBackgroundValue =
  Jets.plaquetteWilsonSecondVariation counterPlaquetteJet

counterWilsonFlatValue : ℚ
counterWilsonFlatValue =
  Jets.plaquetteWilsonSecondVariation flatCounterPlaquetteJet

counterWilsonBackgroundValueExact :
  counterWilsonBackgroundValue ≡ + 536805374 / 268435457
counterWilsonBackgroundValueExact = ℚRing.solve []

counterWilsonFlatValueExact :
  counterWilsonFlatValue ≡ + 2 / 1
counterWilsonFlatValueExact = ℚRing.solve []

counterWilsonDefect : ℚ
counterWilsonDefect =
  counterWilsonBackgroundValue - counterWilsonFlatValue

counterWilsonDefectExact :
  counterWilsonDefect ≡ - (+ 65540 / 268435457)
counterWilsonDefectExact =
  trans
    (ℚRing.solve-∀ counterWilsonBackgroundValue counterWilsonFlatValue)
    (subst
      (λ backgroundValue →
        backgroundValue - counterWilsonFlatValue
        ≡ - (+ 65540 / 268435457))
      (sym counterWilsonBackgroundValueExact)
      (subst
        (λ flatValue →
          (+ 536805374 / 268435457) - flatValue
          ≡ - (+ 65540 / 268435457))
        (sym counterWilsonFlatValueExact)
        (ℚRing.solve [])))

counterProposedLocalBudget : ℚ
counterProposedLocalBudget =
  (+ 1 / 36) * Relaxed.rho * counterCrossCharge
  + (+ 1 / 144) * Relaxed.rho * counterDiagonalCharge

counterProposedLocalBudgetExact :
  counterProposedLocalBudget ≡ + 13 / 589824
counterProposedLocalBudgetExact = ℚRing.solve []

counterWLocalViolationGap : ℚ
counterWLocalViolationGap =
  - counterWilsonDefect - counterProposedLocalBudget

counterWLocalViolationGapExact :
  counterWLocalViolationGap
  ≡ + 35167404019 / 158329674989568
counterWLocalViolationGapExact =
  subst
    (λ defectValue →
      - defectValue - counterProposedLocalBudget
      ≡ + 35167404019 / 158329674989568)
    (sym counterWilsonDefectExact)
    (subst
      (λ budgetValue →
        - (- (+ 65540 / 268435457)) - budgetValue
        ≡ + 35167404019 / 158329674989568)
      (sym counterProposedLocalBudgetExact)
      (ℚRing.solve []))

counterWLocalViolationGapPositive :
  0ℚ < counterWLocalViolationGap
counterWLocalViolationGapPositive =
  let
    instance
      gapPositive : Positive (+ 35167404019 / 158329674989568)
      gapPositive = ℚP.normalize-pos
        35167404019 158329674989568
  in
  subst
    (λ selected → 0ℚ < selected)
    (sym counterWLocalViolationGapExact)
    (ℚP.positive⁻¹ (+ 35167404019 / 158329674989568))

radiusOnlyWLocalCounterexampleLevel : ProofLevel
radiusOnlyWLocalCounterexampleLevel = machineChecked

selectedBackgroundExtraStructureRequiredLevel : ProofLevel
selectedBackgroundExtraStructureRequiredLevel = machineChecked
