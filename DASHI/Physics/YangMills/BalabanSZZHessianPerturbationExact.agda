module DASHI.Physics.YangMills.BalabanSZZHessianPerturbationExact where

------------------------------------------------------------------------
-- ROUND68: EXACT HESSIAN PERTURBATION OF A BAKRY--EMERY MARGIN
--
-- PRIMARY SOURCES / CALIBRATION
--
-- Hao Shen, Rongchan Zhu and Xiangchan Zhu,
-- "A Stochastic Analysis Approach to Lattice Yang--Mills at Strong Coupling",
-- Communications in Mathematical Physics 400 (2023), 805--851.
-- DOI: 10.1007/s00220-022-04609-1.
--
-- Dominique Bakry, Ivan Gentil and Michel Ledoux,
-- "Analysis and Geometry of Markov Diffusion Operators",
-- Springer, 2014. DOI: 10.1007/978-3-319-00227-9.
--
-- DASHI CONTRIBUTION
--
-- SZZ prove positivity of Ric - Hess S_W for the Wilson action in a strong-
-- coupling window.  A Balaban effective density at a coarse scale is not
-- literally pure Wilson: it contains an irrelevant/polymer remainder R.
--
-- The correct handoff is perturbative at the QUADRATIC-FORM level.  For every
-- tangent vector v, if
--
--   K_W q(v) <= Ric(v,v) - Hess S_W(v,v)
--   Hess R(v,v) <= rho q(v),
--
-- then, using Hess(S_W+R)=Hess S_W+Hess R,
--
--   (K_W-rho) q(v)
--      <= Ric(v,v) - Hess(S_W+R)(v,v).
--
-- No spectral theorem, Poincare theorem, or stochastic dynamics is assumed in
-- this algebraic module.  The physical work is to obtain the two quadratic-form
-- bounds on the SAME effective density from the source-native RG norm.
------------------------------------------------------------------------

open import Data.Rational.Base as ℚ using (ℚ; _+_; _-_; _*_; _≤_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel

record WilsonPlusRemainderHessianData (Tangent : Set) : Set₁ where
  field
    quadraticMass : Tangent → ℚ
    ricciForm : Tangent → ℚ
    wilsonHessian remainderHessian effectiveHessian : Tangent → ℚ

    wilsonMargin remainderCost : ℚ

    effectiveHessianExact : ∀ v →
      effectiveHessian v ≡ wilsonHessian v + remainderHessian v

    wilsonBakryEmeryLower : ∀ v →
      wilsonMargin * quadraticMass v
      ≤ ricciForm v - wilsonHessian v

    remainderHessianUpper : ∀ v →
      remainderHessian v ≤ remainderCost * quadraticMass v

open WilsonPlusRemainderHessianData public

effectiveBakryEmeryMargin :
  ∀ {Tangent} → WilsonPlusRemainderHessianData Tangent → ℚ
effectiveBakryEmeryMargin dataSet =
  wilsonMargin dataSet - remainderCost dataSet

effectiveBakryEmeryLower :
  ∀ {Tangent}
    (dataSet : WilsonPlusRemainderHessianData Tangent) →
    ∀ v →
  effectiveBakryEmeryMargin dataSet * quadraticMass dataSet v
  ≤ ricciForm dataSet v - effectiveHessian dataSet v
effectiveBakryEmeryLower dataSet v =
  let
    wilson = wilsonBakryEmeryLower dataSet v
    remainder = remainderHessianUpper dataSet v
    signed = ℚP.+-mono-≤ wilson (ℚP.neg-mono-≤ remainder)

    lowerNormal :
      wilsonMargin dataSet * quadraticMass dataSet v
        + (- (remainderCost dataSet * quadraticMass dataSet v))
      ≡ effectiveBakryEmeryMargin dataSet * quadraticMass dataSet v
    lowerNormal = ℚRing.solve-∀
      (wilsonMargin dataSet)
      (remainderCost dataSet)
      (quadraticMass dataSet v)

    upperBeforeEffective :
      (ricciForm dataSet v - wilsonHessian dataSet v)
        + (- remainderHessian dataSet v)
      ≡ ricciForm dataSet v
        - (wilsonHessian dataSet v + remainderHessian dataSet v)
    upperBeforeEffective = ℚRing.solve-∀
      (ricciForm dataSet v)
      (wilsonHessian dataSet v)
      (remainderHessian dataSet v)
  in
  subst
    (λ lower → lower ≤ ricciForm dataSet v - effectiveHessian dataSet v)
    lowerNormal
    (subst
      (λ upper →
        wilsonMargin dataSet * quadraticMass dataSet v
          + (- (remainderCost dataSet * quadraticMass dataSet v))
        ≤ upper)
      upperBeforeEffective
      (subst
        (λ upper →
          wilsonMargin dataSet * quadraticMass dataSet v
            + (- (remainderCost dataSet * quadraticMass dataSet v))
          ≤ ricciForm dataSet v - upper)
        (effectiveHessianExact dataSet v)
        signed))

hessianPerturbationBakryEmeryLevel : ProofLevel
hessianPerturbationBakryEmeryLevel = machineChecked

-- Physical producer: instantiate the remainder Hessian upper bound from the
-- SAME unified polymer/Schwinger norm used for the continuum Cauchy theorem.
physicalUnifiedNormControlsEffectiveHessianLevel : ProofLevel
physicalUnifiedNormControlsEffectiveHessianLevel = conditional
