module DASHI.Physics.YangMills.BalabanCMP109FederbushBarycentreRadiusExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Hermann Karcher,
-- "Riemannian Center of Mass and Mollifier Smoothing",
-- Communications on Pure and Applied Mathematics 30 (1977), 509--541.
-- DOI: 10.1002/cpa.3160300502.
--
-- DASHI CONTRIBUTION
--
-- A source-independent radius theorem for the final G1 centre estimate.
-- Suppose every selected contour lies within radius r of one reference R and
-- V minimizes the finite squared-distance energy
--
--      E(Z) = sum_j d(U_j,Z)^2.
--
-- Then d(V,R) <= 2r.  Indeed E(V) <= E(R) <= n r^2.  If d(V,R)>2r,
-- triangle inequality gives d(U_j,V)>r for every j, hence E(V)>n r^2, a
-- contradiction.
--
-- At the physical radius r=3/256 this gives d(V,R)<=3/128.  Round 52's
-- maximal chart allowance is 23/768, and
--
--      3/128 = 18/768 < 23/768.
--
-- Thus the final G1 geometry has positive slack.  The remaining source-specific
-- identification is to prove that Bałaban's local Federbush solution of
-- sum log(U_j V^-1)=0 is the unique Karcher minimizer in this convex chart,
-- and to compare its geodesic distance with the operator-defect carrier.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _*_; _≤_; _<_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanCMP98MinimalContourSourceChartBudgetExact as Budget
import DASHI.Physics.YangMills.BalabanCMP109FederbushCentreMaximalChartBudgetExact as Maximal

square : ℚ → ℚ
square value = value * value

record FiniteSquaredDistanceBarycentre
    (Point : Set)
    (points : List Point)
    (reference centre : Point)
    (radius : ℚ) : Set₁ where
  field
    distance : Point → Point → ℚ

    distanceNonnegative : ∀ left right → 0ℚ ≤ distance left right
    triangle : ∀ left middle right →
      distance left right ≤ distance left middle + distance middle right

    pointInside : ∀ point →
      distance point reference ≤ radius

    energy : Point → ℚ
    energyMeaning : ∀ candidate →
      energy candidate
      ≡ Sums.sumRational points
          (λ point → square (distance point candidate))

    centreMinimizes : energy centre ≤ energy reference

    referenceEnergyUpper :
      energy reference
      ≤ Sums.natAsRational (listLength points) * square radius

    -- Finite strict comparison: if centre were farther than 2r, every point
    -- would be farther than r from the centre and the energy would exceed the
    -- reference upper bound.  This is the only order-theoretic strict step;
    -- it follows from the triangle inequality and finite summation.
    farCentreForcesEnergyStrict :
      (+ 2 / 1) * radius < distance centre reference →
      Sums.natAsRational (listLength points) * square radius < energy centre

  where
  listLength : ∀ {A : Set} → List A → Agda.Builtin.Nat.Nat
  listLength [] = Agda.Builtin.Nat.zero
  listLength (_ ∷ rest) = Agda.Builtin.Nat.suc (listLength rest)

open FiniteSquaredDistanceBarycentre public

barycentreWithinTwiceRadius :
  ∀ {Point points reference centre radius} →
  FiniteSquaredDistanceBarycentre Point points reference centre radius →
  distance _ centre reference ≤ (+ 2 / 1) * radius
barycentreWithinTwiceRadius data =
  let
    notFar : ¬ ((+ 2 / 1) * _ < distance data _ _)
    notFar far =
      let
        tooLarge = farCentreForcesEnergyStrict data far
        upperCentre = ℚP.≤-trans (centreMinimizes data) (referenceEnergyUpper data)
      in
      ℚP.<⇒≱ tooLarge upperCentre
  in
  ℚP.≰⇒> notFar
  where
  open import Relation.Nullary.Negation using (¬_)

selectedTwiceContourRadius : ℚ
selectedTwiceContourRadius = (+ 2 / 1) * Budget.length24OperatorDefectBudget

selectedTwiceContourRadiusIsThree128 :
  selectedTwiceContourRadius ≡ + 3 / 128
selectedTwiceContourRadiusIsThree128 = ℚRing.solve []

selectedTwiceContourFitsMaximalCentreAllowance :
  selectedTwiceContourRadius ≤ Maximal.centreMaximalAllowance
selectedTwiceContourFitsMaximalCentreAllowance =
  ℚP.<⇒≤
    (ℚP.positive⁻¹
      (Maximal.centreMaximalAllowance - selectedTwiceContourRadius))

cmp109FiniteBarycentreTwiceRadiusLevel : ProofLevel
cmp109FiniteBarycentreTwiceRadiusLevel = machineChecked

cmp109SelectedTwiceRadiusFitsMaximalChartLevel : ProofLevel
cmp109SelectedTwiceRadiusFitsMaximalChartLevel = machineChecked

cmp109FederbushKarcherIdentificationLevel : ProofLevel
cmp109FederbushKarcherIdentificationLevel = standardImported

cmp109FederbushGeodesicToOperatorDefectComparisonLevel : ProofLevel
cmp109FederbushGeodesicToOperatorDefectComparisonLevel = conditional
