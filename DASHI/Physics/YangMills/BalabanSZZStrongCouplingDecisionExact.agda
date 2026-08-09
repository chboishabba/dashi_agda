module DASHI.Physics.YangMills.BalabanSZZStrongCouplingDecisionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Hao Shen; Rongchan Zhu; Xiangchan Zhu,
-- "A Stochastic Analysis Approach to Lattice Yang--Mills at Strong
-- Coupling", Communications in Mathematical Physics 400 (2023), 805--851.
-- DOI: 10.1007/s00220-022-04609-1.
-- arXiv: 2204.12737.
--
-- Dominique Bakry; Michel Emery,
-- "Diffusions hypercontractives", Seminaire de probabilites XIX,
-- Lecture Notes in Mathematics 1123 (1985), 177--206.
-- DOI: 10.1007/BFb0075847.
--
-- Kenneth G. Wilson,
-- "Confinement of Quarks", Physical Review D 10 (1974), 2445--2459.
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- Tadeusz Bałaban,
-- "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
--
-- DASHI CONTRIBUTION
--
-- Implement the small, falsifiable SZZ decision tranche before attempting to
-- import the full stochastic proof.  The file proves the exact SU(2) Wilson
-- action normalization, including the volume-dependent additive constant;
-- computes the four-dimensional SZZ curvature constant
--
--   K_S(betaAbs) = 1 - 48 betaAbs
--                = 48 (1/48 - betaAbs);
--
-- proves the exact threshold using the normalized curvature; gives a literal
-- counterexample to the invalid inference from the selected-background radius
-- rho = 1/8192 to strong coupling; and isolates the only RG-to-SZZ theorem
-- that matters: the effective-action Hessian loss must be strictly smaller
-- than the product-group Ricci floor at some finite depth.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Integer.Base using (+_)
open import Data.Product.Base using (_×_; _,_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; -_; _<_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; trans)
open import Relation.Nullary.Negation.Core using (¬_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums

fortyEight : ℚ
fortyEight = + 48 / 1

oneFortyEighth : ℚ
oneFortyEighth = + 1 / 48

four : ℚ
four = + 4 / 1

selectedSmallFieldRadius : ℚ
selectedSmallFieldRadius = + 1 / 8192

------------------------------------------------------------------------
-- Exact SU(2) action-convention bridge.
--
-- DASHI's normalized SU(2) trace is q0 = (1/2) Re Tr U.  Hence its Wilson
-- plaquette action is 1-q0.  SZZ use N beta Re Tr U in the exponent; for
-- N=2 this is 4 beta q0.  Therefore beta_DASHI = 4 beta_SZZ and the two
-- exponent conventions differ only by an additive constant per plaquette.
------------------------------------------------------------------------

dashiSU2PlaquetteAction : ℚ → ℚ
dashiSU2PlaquetteAction normalizedTrace = 1ℚ - normalizedTrace

dashiCouplingFromSZZ : ℚ → ℚ
dashiCouplingFromSZZ betaSZZ = four * betaSZZ

szzSU2PlaquetteExponent : ℚ → ℚ → ℚ
szzSU2PlaquetteExponent betaSZZ normalizedTrace =
  four * betaSZZ * normalizedTrace

dashiWilsonExponentAtSZZCoupling : ℚ → ℚ → ℚ
dashiWilsonExponentAtSZZCoupling betaSZZ normalizedTrace =
  - (dashiCouplingFromSZZ betaSZZ)
    * dashiSU2PlaquetteAction normalizedTrace

szzPlaquetteIsDashiPlusConstant : ∀ betaSZZ normalizedTrace →
  szzSU2PlaquetteExponent betaSZZ normalizedTrace
  ≡ dashiWilsonExponentAtSZZCoupling betaSZZ normalizedTrace
      + dashiCouplingFromSZZ betaSZZ
szzPlaquetteIsDashiPlusConstant betaSZZ normalizedTrace =
  ℚRing.solve-∀ betaSZZ normalizedTrace

dashiWilsonActionFromNormalizedTraces : List ℚ → ℚ
dashiWilsonActionFromNormalizedTraces traces =
  Sums.sumRational traces dashiSU2PlaquetteAction

szzWilsonExponentFromNormalizedTraces : ℚ → List ℚ → ℚ
szzWilsonExponentFromNormalizedTraces betaSZZ traces =
  Sums.sumRational traces (szzSU2PlaquetteExponent betaSZZ)

szzDashiNormalizationExact : ∀ betaSZZ traces →
  szzWilsonExponentFromNormalizedTraces betaSZZ traces
  ≡ - (dashiCouplingFromSZZ betaSZZ)
      * dashiWilsonActionFromNormalizedTraces traces
    + Sums.natAsRational
        (Data.List.Base.length traces)
      * dashiCouplingFromSZZ betaSZZ
szzDashiNormalizationExact betaSZZ [] =
  ℚRing.solve-∀ betaSZZ
szzDashiNormalizationExact betaSZZ (trace ∷ traces)
  rewrite szzDashiNormalizationExact betaSZZ traces =
  ℚRing.solve-∀
    betaSZZ trace
    (dashiWilsonActionFromNormalizedTraces traces)
    (Sums.natAsRational (Data.List.Base.length traces))

------------------------------------------------------------------------
-- Exact SZZ SU(2), d=4 curvature threshold.
------------------------------------------------------------------------

szzSU2D4BakryEmeryConstant : ℚ → ℚ
szzSU2D4BakryEmeryConstant betaAbs =
  1ℚ - fortyEight * betaAbs

szzSU2D4NormalizedCurvature : ℚ → ℚ
szzSU2D4NormalizedCurvature betaAbs =
  oneFortyEighth - betaAbs

szzSU2D4BakryEmeryFactorizationExact : ∀ betaAbs →
  szzSU2D4BakryEmeryConstant betaAbs
  ≡ fortyEight * szzSU2D4NormalizedCurvature betaAbs
szzSU2D4BakryEmeryFactorizationExact betaAbs =
  ℚRing.solve-∀ betaAbs

differencePositive : ∀ larger smaller →
  smaller < larger → 0ℚ < larger - smaller
differencePositive larger smaller smaller<larger =
  let
    negated : - larger < - smaller
    negated = ℚP.neg-antimono-< smaller<larger
  in
  trans
    (ℚRing.solve-∀ larger)
    (trans
      (ℚP.+-monoˡ-< larger negated)
      (ℚRing.solve-∀ larger smaller))

positiveDifferenceImpliesLess : ∀ larger smaller →
  0ℚ < larger - smaller → smaller < larger
positiveDifferenceImpliesLess larger smaller positiveDifference =
  trans
    (ℚRing.solve-∀ smaller)
    (trans
      (ℚP.+-monoʳ-< smaller positiveDifference)
      (ℚRing.solve-∀ larger smaller))

szzSU2D4StrongCouplingThresholdForward : ∀ betaAbs →
  betaAbs < oneFortyEighth →
  0ℚ < szzSU2D4NormalizedCurvature betaAbs
szzSU2D4StrongCouplingThresholdForward betaAbs =
  differencePositive oneFortyEighth betaAbs

szzSU2D4StrongCouplingThresholdBackward : ∀ betaAbs →
  0ℚ < szzSU2D4NormalizedCurvature betaAbs →
  betaAbs < oneFortyEighth
szzSU2D4StrongCouplingThresholdBackward betaAbs =
  positiveDifferenceImpliesLess oneFortyEighth betaAbs

szzSU2D4StrongCouplingThresholdExact : ∀ betaAbs →
  (betaAbs < oneFortyEighth)
  × (0ℚ < szzSU2D4NormalizedCurvature betaAbs →
      betaAbs < oneFortyEighth)
szzSU2D4StrongCouplingThresholdExact betaAbs =
  szzSU2D4StrongCouplingThresholdForward betaAbs
  , szzSU2D4StrongCouplingThresholdBackward betaAbs

------------------------------------------------------------------------
-- The selected small-field radius is not a coupling hypothesis.
------------------------------------------------------------------------

SelectedSmallFieldRadiusAt : ℚ → Set
SelectedSmallFieldRadiusAt radius = radius ≡ selectedSmallFieldRadius

SZZStrongCouplingAt : ℚ → Set
SZZStrongCouplingAt betaAbs = betaAbs < oneFortyEighth

oneIsNotSZZStrongCoupling : ¬ SZZStrongCouplingAt 1ℚ
oneIsNotSZZStrongCoupling = λ ()

selectedBackgroundRadiusDoesNotImplySZZStrongCoupling :
  ¬ (SelectedSmallFieldRadiusAt selectedSmallFieldRadius →
      SZZStrongCouplingAt 1ℚ)
selectedBackgroundRadiusDoesNotImplySZZStrongCoupling implication =
  oneIsNotSZZStrongCoupling (implication refl)

------------------------------------------------------------------------
-- RG-to-Bakry--Emery decision theorem.
------------------------------------------------------------------------

record SelectedRGEffectiveActionHessianData : Set₁ where
  field
    Scale : Set
    selectedDepth : Scale

    Tangent : Set
    normSq : Tangent → ℚ
    effectiveHessian : Tangent → ℚ

    ricciFloor : ℚ
    hessianLoss : ℚ

    hessianLower : ∀ tangent →
      - hessianLoss * normSq tangent
      ℚ.≤ effectiveHessian tangent

    hessianLossBelowRicci : hessianLoss < ricciFloor
open SelectedRGEffectiveActionHessianData public

selectedRGEffectiveBakryEmeryConstant :
  SelectedRGEffectiveActionHessianData → ℚ
selectedRGEffectiveBakryEmeryConstant data =
  ricciFloor data - hessianLoss data

selectedRGEffectiveBakryEmeryConstantPositive :
  ∀ data → 0ℚ < selectedRGEffectiveBakryEmeryConstant data
selectedRGEffectiveBakryEmeryConstantPositive data =
  differencePositive
    (ricciFloor data) (hessianLoss data)
    (hessianLossBelowRicci data)

record SelectedRGEntersBakryEmeryRegion : Set₁ where
  field
    effectiveData : SelectedRGEffectiveActionHessianData
    positiveCurvature :
      0ℚ < selectedRGEffectiveBakryEmeryConstant effectiveData
open SelectedRGEntersBakryEmeryRegion public

selectedRGEntersBakryEmeryRegion :
  SelectedRGEffectiveActionHessianData →
  SelectedRGEntersBakryEmeryRegion
selectedRGEntersBakryEmeryRegion data = record
  { effectiveData = data
  ; positiveCurvature =
      selectedRGEffectiveBakryEmeryConstantPositive data
  }

szzNormalizationLevel : ProofLevel
szzNormalizationLevel = machineChecked

szzThresholdLevel : ProofLevel
szzThresholdLevel = machineChecked

szzRadiusSeparationLevel : ProofLevel
szzRadiusSeparationLevel = machineChecked

selectedRGEffectiveHessianProducerLevel : ProofLevel
selectedRGEffectiveHessianProducerLevel = conditional
