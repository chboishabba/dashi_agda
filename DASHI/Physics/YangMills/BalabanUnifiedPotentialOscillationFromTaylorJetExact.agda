module DASHI.Physics.YangMills.BalabanUnifiedPotentialOscillationFromTaylorJetExact where

------------------------------------------------------------------------
-- ROUND69: WHEN DOES HESSIAN CONTROL REALLY GIVE HOLLEY--STROOCK OSCILLATION?
--
-- PRIMARY SOURCES / CALIBRATION
--
-- Richard Holley and Daniel Stroock,
-- "Logarithmic Sobolev Inequalities and Stochastic Ising Models",
-- Journal of Statistical Physics 46 (1987), 1159--1194.
-- DOI: 10.1007/BF01011161.
--
-- Dominique Bakry and Michel Emery,
-- "Diffusions hypercontractives",
-- Seminaire de Probabilites XIX, Lecture Notes in Mathematics 1123 (1985),
-- 177--206. DOI: 10.1007/BFb0075847.
--
-- DASHI CONTRIBUTION
--
-- A uniform Hessian bound by itself does NOT imply a uniform oscillation bound:
-- an affine component has zero second derivative and arbitrarily large
-- oscillation.  Therefore the proposed L7 -> Holley--Stroock route needs one
-- additional first-order/anchoring datum.
--
-- The correct finite quantitative bridge is Taylor's inequality along a path:
--
--   |Phi(x)-Phi(x0)|
--      <= G d(x,x0) + (rho/2) d(x,x0)^2.
--
-- If d <= D uniformly, then every pair satisfies
--
--   |Phi(x)-Phi(y)| <= 2 G D + rho D^2.
--
-- Thus the unified RG norm can feed Holley--Stroock provided it controls:
--
--   * a base-point gradient cost G (often killed by choosing a stationary
--     background/minimizer),
--   * the Hessian remainder cost rho,
--   * a volume-uniform physical/orbit diameter D or an equivalent path bound.
--
-- This is strictly sharper than saying "Hessian control implies oscillation".
------------------------------------------------------------------------

open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _*_; _≤_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm

half : ℚ
half = + 1 / 2

record AnchoredTaylorOscillationData (Point : Set) : Set₁ where
  field
    basePoint : Point
    distance : Point → Point → ℚ
    potentialDifferenceMagnitude : Point → Point → ℚ

    baseGradientCost hessianCost diameter : ℚ
    baseGradientCostNonnegative : 0ℚ ≤ baseGradientCost
    hessianCostNonnegative : 0ℚ ≤ hessianCost
    diameterNonnegative : 0ℚ ≤ diameter

    distanceNonnegative : ∀ x y → 0ℚ ≤ distance x y
    distanceBelowDiameter : ∀ x y → distance x y ≤ diameter
    distanceSquareBelowDiameterSquare : ∀ x y →
      distance x y * distance x y ≤ diameter * diameter

    -- This is the actual second-order analytic estimate that the physical RG
    -- norm must prove on the same effective potential.
    anchoredTaylorBound : ∀ x →
      potentialDifferenceMagnitude x basePoint
      ≤ baseGradientCost * distance x basePoint
        + half * hessianCost *
            (distance x basePoint * distance x basePoint)

    differenceSymmetric : ∀ x y →
      potentialDifferenceMagnitude x y
      ≡ potentialDifferenceMagnitude y x

    differenceTriangleViaBase : ∀ x y →
      potentialDifferenceMagnitude x y
      ≤ potentialDifferenceMagnitude x basePoint
        + potentialDifferenceMagnitude basePoint y

open AnchoredTaylorOscillationData public

anchoredPointwiseOscillationMajorant :
  ∀ {Point} (dataSet : AnchoredTaylorOscillationData Point) x →
  potentialDifferenceMagnitude dataSet x (basePoint dataSet)
  ≤ baseGradientCost dataSet * diameter dataSet
    + half * hessianCost dataSet * (diameter dataSet * diameter dataSet)
anchoredPointwiseOscillationMajorant dataSet x =
  let
    linear = Norm.scaleNonnegative
      (baseGradientCost dataSet)
      (baseGradientCostNonnegative dataSet)
      (distanceBelowDiameter dataSet x (basePoint dataSet))

    halfRhoNonnegative : 0ℚ ≤ half * hessianCost dataSet
    halfRhoNonnegative =
      let
        instance halfNN : ℚ.NonNegative half
        halfNN = ℚ.nonNegative (ℚP.nonNegative⁻¹ half)
        instance rhoNN : ℚ.NonNegative (hessianCost dataSet)
        rhoNN = ℚ.nonNegative (hessianCostNonnegative dataSet)
      in ℚP.nonNegative⁻¹ (half * hessianCost dataSet)

    quadratic = Norm.scaleNonnegative
      (half * hessianCost dataSet)
      halfRhoNonnegative
      (distanceSquareBelowDiameterSquare dataSet x (basePoint dataSet))

    combined = ℚP.+-mono-≤ linear quadratic
  in
  ℚP.≤-trans (anchoredTaylorBound dataSet x) combined

uniformPairOscillationMajorant :
  ∀ {Point} (dataSet : AnchoredTaylorOscillationData Point) x y →
  potentialDifferenceMagnitude dataSet x y
  ≤ (+ 2 / 1) * baseGradientCost dataSet * diameter dataSet
    + hessianCost dataSet * (diameter dataSet * diameter dataSet)
uniformPairOscillationMajorant dataSet x y =
  let
    xBound = anchoredPointwiseOscillationMajorant dataSet x
    yBoundForward = anchoredPointwiseOscillationMajorant dataSet y
    yBound :
      potentialDifferenceMagnitude dataSet (basePoint dataSet) y
      ≤ baseGradientCost dataSet * diameter dataSet
        + half * hessianCost dataSet * (diameter dataSet * diameter dataSet)
    yBound = subst
      (λ left → left ≤
        baseGradientCost dataSet * diameter dataSet
          + half * hessianCost dataSet * (diameter dataSet * diameter dataSet))
      (differenceSymmetric dataSet y (basePoint dataSet))
      yBoundForward

    paired = ℚP.+-mono-≤ xBound yBound
    triangle = differenceTriangleViaBase dataSet x y
  in
  ℚP.≤-trans triangle
    (subst
      (λ right →
        potentialDifferenceMagnitude dataSet x (basePoint dataSet)
          + potentialDifferenceMagnitude dataSet (basePoint dataSet) y
        ≤ right)
      (ℚRing.solve-∀
        (baseGradientCost dataSet)
        (hessianCost dataSet)
        (diameter dataSet))
      paired)

stationaryBaseOscillationMajorant :
  ∀ {Point} (dataSet : AnchoredTaylorOscillationData Point) →
  baseGradientCost dataSet ≡ 0ℚ →
  ∀ x y →
  potentialDifferenceMagnitude dataSet x y
  ≤ hessianCost dataSet * (diameter dataSet * diameter dataSet)
stationaryBaseOscillationMajorant dataSet stationary x y =
  subst
    (λ gradient →
      potentialDifferenceMagnitude dataSet x y
      ≤ (+ 2 / 1) * gradient * diameter dataSet
        + hessianCost dataSet * (diameter dataSet * diameter dataSet))
    stationary
    (uniformPairOscillationMajorant dataSet x y)

------------------------------------------------------------------------
-- Exact falsifier: second-order/Hessian information alone cannot control
-- oscillation because affine functions lie in the Hessian kernel.
------------------------------------------------------------------------

data ThreePoint : Set where
  left centre right : ThreePoint

affinePotential : ℚ → ThreePoint → ℚ
affinePotential slope left = 0ℚ
affinePotential slope centre = slope
affinePotential slope right = slope + slope

discreteSecondDifference : (ThreePoint → ℚ) → ℚ
discreteSecondDifference f = f left + f right + (+ -2 / 1) * f centre

affineSecondDifferenceZero : ∀ slope →
  discreteSecondDifference (affinePotential slope) ≡ 0ℚ
affineSecondDifferenceZero slope = ℚRing.solve-∀ slope

affineEndpointOscillation : ∀ slope →
  affinePotential slope right
  ≡ affinePotential slope left + (+ 2 / 1) * slope
affineEndpointOscillation slope = ℚRing.solve-∀ slope

hessianAloneCannotControlOscillationLevel : ProofLevel
hessianAloneCannotControlOscillationLevel = machineChecked

anchoredTaylorToUniformOscillationLevel : ProofLevel
anchoredTaylorToUniformOscillationLevel = machineChecked

-- Physical L7 strengthening: instantiate the anchored Taylor estimate and a
-- volume-uniform diameter/path bound on the ACTUAL quotient/effective-potential
-- carrier.  At a stationary selected background the gradient term disappears,
-- leaving osc(Phi) <= rho D^2.
physicalUnifiedNormToUniformPotentialOscillationLevel : ProofLevel
physicalUnifiedNormToUniformPotentialOscillationLevel = conditional
