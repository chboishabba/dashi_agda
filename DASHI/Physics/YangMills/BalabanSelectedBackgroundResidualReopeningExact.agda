module DASHI.Physics.YangMills.BalabanSelectedBackgroundResidualReopeningExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- J. M. Combes and L. Thomas,
-- "Asymptotic Behaviour of Eigenfunctions for Multiparticle Schrödinger
-- Operators", Communications in Mathematical Physics 34 (1973), 251--270.
-- DOI: 10.1007/BF01646473.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- DASHI CONTRIBUTION
--
-- Consume the literal selected residual estimates as reopening equations,
-- rather than defining an inverse by an infinite Neumann sum over Q.
--
-- Unweighted:
--
--   x + R_A x = y,  ||R_A x||_1 <= (1/10)||x||_1
--
-- implies
--
--   ||x||_1 <= (10/9)||y||_1.
--
-- With the already-constructed rational Combes--Thomas conjugation:
--
--   x + (D R_A D^-1)x = y,
--   ||(D R_A D^-1)x||_1 <= (1/6)||x||_1
--
-- implies
--
--   ||x||_1 <= (6/5)||y||_1.
--
-- The corresponding homogeneous equations have zero l1 norm.  Thus both
-- reopenings have explicit positive slack before any finite-dimensional
-- inverse theorem is invoked.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (cong; subst; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanFiniteMatrixL1ContractionExact as L1
import DASHI.Physics.YangMills.BalabanFiniteStrictContractionReopeningExact as Reopen
import DASHI.Physics.YangMills.BalabanSelectedBackgroundFlatGreenPerturbationContractionExact as Contraction
import DASHI.Physics.YangMills.BalabanSelectedBackgroundResidualPowerDecayExact as Residual
import DASHI.Physics.YangMills.BalabanSelectedBackgroundRationalWeightedPowerDecayExact as Weighted
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeParameterizedYoungExact as Relaxed

GaugeVector : Set
GaugeVector = Contraction.GaugeRow → ℚ

unweightedIdentityPlusResidualApply :
  Physical.RationalSU2Background4 → GaugeVector → GaugeVector
unweightedIdentityPlusResidualApply background vector row =
  vector row + Residual.residualApply background vector row

UnweightedReopeningEquation :
  Physical.RationalSU2Background4 → GaugeVector → GaugeVector → Set
UnweightedReopeningEquation background solution source =
  ∀ row → unweightedIdentityPlusResidualApply background solution row
    ≡ source row

unweightedSlack tenNinths : ℚ
unweightedSlack = + 9 / 10
tenNinths = + 10 / 9

unweightedSlackExact :
  Contraction.oneTenth + unweightedSlack ≡ 1ℚ
unweightedSlackExact = ℚRing.solve []

selectedBackgroundResidualReopeningTenNinths :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  ∀ solution source →
  UnweightedReopeningEquation background solution source →
  L1.vectorL1 Contraction.gaugeRows solution
  ≤ tenNinths * L1.vectorL1 Contraction.gaugeRows source
selectedBackgroundResidualReopeningTenNinths
    background radius solution source equation =
  let
    xNorm = L1.vectorL1 Contraction.gaugeRows solution
    yNorm = L1.vectorL1 Contraction.gaugeRows source
    rNorm = L1.vectorL1 Contraction.gaugeRows
      (Residual.residualApply background solution)

    triangle : xNorm ≤ yNorm + rNorm
    triangle = Reopen.solutionL1ReopeningUpper
      Contraction.gaugeRows
      (Residual.residualApply background)
      solution source equation

    contraction : rNorm ≤ Contraction.oneTenth * xNorm
    contraction = Residual.residualOneStepL1Contraction
      background radius solution

    replaceResidual :
      yNorm + rNorm ≤ yNorm + Contraction.oneTenth * xNorm
    replaceResidual = ℚP.+-monoʳ-≤ yNorm contraction

    beforeGap :
      xNorm ≤ yNorm + Contraction.oneTenth * xNorm
    beforeGap = ℚP.≤-trans triangle replaceResidual

    gapRaw :
      (1ℚ - Contraction.oneTenth) * xNorm ≤ yNorm
    gapRaw = Reopen.reopeningGapBound
      xNorm yNorm Contraction.oneTenth beforeGap

    gap : unweightedSlack * xNorm ≤ yNorm
    gap = subst
      (λ lower → lower ≤ yNorm)
      (cong (_* xNorm)
        (ℚRing.solve [] : 1ℚ - Contraction.oneTenth ≡ unweightedSlack))
      gapRaw

    scaled :
      tenNinths * (unweightedSlack * xNorm)
      ≤ tenNinths * yNorm
    scaled = Norm.scaleNonnegative tenNinths
      (ℚP.nonNegative⁻¹ tenNinths) gap

    leftExact :
      tenNinths * (unweightedSlack * xNorm) ≡ xNorm
    leftExact = ℚRing.solve-∀ xNorm
  in
  subst
    (λ lower → lower ≤ tenNinths * yNorm)
    leftExact scaled

weightedIdentityPlusResidualApply :
  Contraction.GaugeRow → Physical.RationalSU2Background4 →
  GaugeVector → GaugeVector
weightedIdentityPlusResidualApply root background vector row =
  vector row + Weighted.weightedResidualApply root background vector row

WeightedReopeningEquation :
  Contraction.GaugeRow → Physical.RationalSU2Background4 →
  GaugeVector → GaugeVector → Set
WeightedReopeningEquation root background solution source =
  ∀ row → weightedIdentityPlusResidualApply root background solution row
    ≡ source row

weightedSlack : ℚ
weightedSlack = + 5 / 6

weightedSlackExact :
  Reopen.oneSixth + weightedSlack ≡ 1ℚ
weightedSlackExact = ℚRing.solve []

selectedBackgroundWeightedResidualReopeningSixFifths :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  ∀ root solution source →
  WeightedReopeningEquation root background solution source →
  L1.vectorL1 Contraction.gaugeRows solution
  ≤ Reopen.sixFifths * L1.vectorL1 Contraction.gaugeRows source
selectedBackgroundWeightedResidualReopeningSixFifths
    background radius root solution source equation =
  Reopen.oneSixthReopeningBound
    Contraction.gaugeRows
    (Weighted.weightedResidualApply root background)
    solution source equation
    (Weighted.weightedResidualOneStepL1Contraction
      background radius root solution)

selectedBackgroundWeightedResidualHomogeneousZeroNorm :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  ∀ root solution →
  WeightedReopeningEquation
    root background solution Reopen.zeroVector →
  L1.vectorL1 Contraction.gaugeRows solution ≡ 0ℚ
selectedBackgroundWeightedResidualHomogeneousZeroNorm
    background radius root solution equation =
  Reopen.oneSixthHomogeneousReopeningZeroNorm
    Contraction.gaugeRows
    (Weighted.weightedResidualApply root background)
    solution equation
    (Weighted.weightedResidualOneStepL1Contraction
      background radius root solution)

selectedBackgroundGreenUnweightedSlackLevel : ProofLevel
selectedBackgroundGreenUnweightedSlackLevel = machineChecked

selectedBackgroundGreenWeightedSlackLevel : ProofLevel
selectedBackgroundGreenWeightedSlackLevel = machineChecked

selectedBackgroundWeightedReopeningSixFifthsLevel : ProofLevel
selectedBackgroundWeightedReopeningSixFifthsLevel = machineChecked
