module DASHI.Physics.YangMills.BalabanP33CovariantCurlRadiusStressTestExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer, 2015.
-- DOI: 10.1007/978-3-319-13467-3.
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
-- DASHI CONTRIBUTION
--
-- Give an exact rational adversarial test before attempting the selected-
-- background curvature estimate.  A stereographic rational unit quaternion
-- lies strictly inside the configured inverse-link radius, while two
-- insertions which cancel at the flat background acquire a nonzero covariant
-- curl after transport by that link.
--
-- This does not refute the desired variational theorem: the witness does not
-- satisfy Bałaban's selected-background Euler--Lagrange equation.  It proves
-- instead that the forthcoming rho/36 estimate must use that correlated
-- equation/curvature information; radius plus flat cancellation is still not
-- enough.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_; _<_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Q
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanP33QuaternionFourFactorTelescopeExact as Telescope
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeParameterizedYoungExact as Relaxed
import DASHI.Physics.YangMills.BalabanP33PhysicalWilsonSignedGlobalExact as WilsonGlobal
import DASHI.Physics.YangMills.BalabanP33PhysicalCovariantPlaquetteCurlExact as Curl

stressCos stressSin : ℚ
stressCos = + 67108863 / 67108865
stressSin = + 16384 / 67108865

stressTurn : Q.RationalQuaternion
stressTurn = Q.quat stressCos stressSin 0ℚ 0ℚ

stressTurnUnitNorm : Physical.quaternionNormSq stressTurn ≡ 1ℚ
stressTurnUnitNorm = ℚRing.solve []

stressTurnInverseDefect : ℚ
stressTurnInverseDefect =
  Norm.normSq
    (Telescope._-q_
      (Physical.quaternionConjugate stressTurn) Q.oneQ)

stressTurnInverseDefectExact :
  stressTurnInverseDefect ≡ + 4 / 67108865
stressTurnInverseDefectExact = ℚRing.solve []

stressRadiusSlack : ℚ
stressRadiusSlack = + 1 / 1125899923619840

stressRadiusSlackNonnegative : 0ℚ ≤ stressRadiusSlack
stressRadiusSlackNonnegative = ℚP.nonNegative⁻¹ stressRadiusSlack

stressDefectPlusSlackIsConfiguredRadius :
  stressTurnInverseDefect + stressRadiusSlack
  ≡ Relaxed.fourRhoSquare
stressDefectPlusSlackIsConfiguredRadius = ℚRing.solve []

stressTurnInsideConfiguredRadius :
  stressTurnInverseDefect ≤ Relaxed.fourRhoSquare
stressTurnInsideConfiguredRadius =
  subst
    (λ upper → stressTurnInverseDefect ≤ upper)
    stressDefectPlusSlackIsConfiguredRadius
    (subst
      (λ lower → lower ≤ stressTurnInverseDefect + stressRadiusSlack)
      (ℚP.+-identityʳ stressTurnInverseDefect)
      (ℚP.+-mono-≤ ℚP.≤-refl stressRadiusSlackNonnegative))

stressY : Q.RationalQuaternion
stressY = Q.pureQuaternion (Q.vec3 0ℚ 1ℚ 0ℚ)

stressMinusY : Q.RationalQuaternion
stressMinusY = Q.negQ stressY

flatCancellingCurl : Q.RationalQuaternion
flatCancellingCurl =
  Curl.covariantPlaquetteCurl
    Q.oneQ Q.oneQ Q.oneQ
    stressY stressMinusY Q.zeroQ Q.zeroQ

flatCancellingCurlExact : flatCancellingCurl ≡ Q.zeroQ
flatCancellingCurlExact =
  Q.quaternionExt
    (ℚRing.solve []) (ℚRing.solve [])
    (ℚRing.solve []) (ℚRing.solve [])

stressCovariantCurl : Q.RationalQuaternion
stressCovariantCurl =
  Curl.covariantPlaquetteCurl
    Q.oneQ stressTurn Q.oneQ
    stressY stressMinusY Q.zeroQ Q.zeroQ

stressCovariantCurlCoordinatesExact :
  stressCovariantCurl
  ≡ Q.quat
      0ℚ 0ℚ
      (+ 536870912 / 4503599761588225)
      (- (+ 2199023222784 / 4503599761588225))
stressCovariantCurlCoordinatesExact =
  Q.quaternionExt
    (ℚRing.solve []) (ℚRing.solve [])
    (ℚRing.solve []) (ℚRing.solve [])

stressCovariantCurlNormSqExact :
  Norm.normSq stressCovariantCurl
  ≡ + 1073741824 / 4503599761588225
stressCovariantCurlNormSqExact = ℚRing.solve []

stressCrossCharge : ℚ
stressCrossCharge = + 6 / 1

stressLinearBudget : ℚ
stressLinearBudget = WilsonGlobal.rhoOverThirtySix * stressCrossCharge

stressLinearBudgetExact : stressLinearBudget ≡ + 1 / 49152
stressLinearBudgetExact = ℚRing.solve []

stressBudgetDominanceGap : ℚ
stressBudgetDominanceGap =
  + 2589569785603817471 / 10880332700790838158950400

stressBudgetDominanceGapPositive : 0ℚ < stressBudgetDominanceGap
stressBudgetDominanceGapPositive =
  ℚP.positive⁻¹ stressBudgetDominanceGap

stressBudgetSquarePlusGapIsCurlNormSq :
  stressLinearBudget * stressLinearBudget
    + stressBudgetDominanceGap
  ≡ Norm.normSq stressCovariantCurl
stressBudgetSquarePlusGapIsCurlNormSq = ℚRing.solve []

record CorrelatedCurvatureStressConclusion : Set where
  field
    radiusSatisfied :
      stressTurnInverseDefect ≤ Relaxed.fourRhoSquare
    flatClosureExact : flatCancellingCurl ≡ Q.zeroQ
    transportedCurlNormExact :
      Norm.normSq stressCovariantCurl
      ≡ + 1073741824 / 4503599761588225
    targetBudgetSquareHasPositiveDeficit :
      stressLinearBudget * stressLinearBudget
        + stressBudgetDominanceGap
      ≡ Norm.normSq stressCovariantCurl
    deficitPositive : 0ℚ < stressBudgetDominanceGap

correlatedCurvatureStressConclusion : CorrelatedCurvatureStressConclusion
correlatedCurvatureStressConclusion = record
  { radiusSatisfied = stressTurnInsideConfiguredRadius
  ; flatClosureExact = flatCancellingCurlExact
  ; transportedCurlNormExact = stressCovariantCurlNormSqExact
  ; targetBudgetSquareHasPositiveDeficit =
      stressBudgetSquarePlusGapIsCurlNormSq
  ; deficitPositive = stressBudgetDominanceGapPositive
  }

covariantCurlRadiusStressLevel : ProofLevel
covariantCurlRadiusStressLevel = machineChecked

selectedEulerLagrangeCorrelationStillRequiredLevel : ProofLevel
selectedEulerLagrangeCorrelationStillRequiredLevel = conditional
