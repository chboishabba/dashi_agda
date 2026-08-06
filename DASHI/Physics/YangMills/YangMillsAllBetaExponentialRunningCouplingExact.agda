module DASHI.Physics.YangMills.YangMillsAllBetaExponentialRunningCouplingExact where

------------------------------------------------------------------------
-- PRIMARY CONTEXT
--
-- Arthur Jaffe and Edward Witten,
-- "Quantum Yang--Mills Theory", official Clay Mathematics Institute problem
-- description.  No DOI assigned.
--
-- DASHI CONTRIBUTION
--
-- Analyze exactly what an all-finite-beta estimate of schematic form
--
--   Delta_latt(beta) >= c exp(-C beta)
--
-- would have to do along a logarithmically running inverse coupling.  On a
-- geometric cutoff sequence a_n=q^n, such an estimate becomes a geometric
-- lower bound r^n.  In physical units the corresponding lower bound is
--
--   a_n^{-1} r^n = (r/q)^n.
--
-- Thus pointwise positivity r^n>0 is not enough: scale compatibility requires
-- control of r/q.  The exact matched case r=q gives a constant physical lower
-- bound, while the quadratic case r=q^2 gives the decaying physical lower
-- bound q^n.  This module proves those identities over exact rationals.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base using (ℚ; 1ℚ; _*_; _/_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (trans)

import DASHI.Physics.YangMills.YangMillsLatticeGapScaleCompatibilityExact as Scale

geometricPhysicalGapLower : ℚ → ℚ → Nat → ℚ
geometricPhysicalGapLower inverseSpacingBase gapBase depth =
  Scale.pow inverseSpacingBase depth * Scale.pow gapBase depth

rescaledGeometricGapIsRatioPower :
  ∀ inverseSpacingBase gapBase depth →
  geometricPhysicalGapLower inverseSpacingBase gapBase depth
  ≡ Scale.pow (inverseSpacingBase * gapBase) depth
rescaledGeometricGapIsRatioPower
    inverseSpacingBase gapBase depth =
  let
    product = Scale.powProduct inverseSpacingBase gapBase depth
  in
  trans
    (solve
      (Scale.pow inverseSpacingBase depth
      ∷ Scale.pow gapBase depth
      ∷ []))
    (solve
      (Scale.pow inverseSpacingBase depth
      ∷ Scale.pow gapBase depth
      ∷ Scale.pow (inverseSpacingBase * gapBase) depth
      ∷ []))

-- The previous theorem is also available directly by symmetry of powProduct;
-- this separately named proof makes the physical interpretation explicit.
rescaledGeometricGapRatioExact :
  ∀ inverseSpacingBase gapBase depth →
  Scale.pow (inverseSpacingBase * gapBase) depth
  ≡ geometricPhysicalGapLower inverseSpacingBase gapBase depth
rescaledGeometricGapRatioExact inverseSpacingBase gapBase depth =
  Scale.powProduct inverseSpacingBase gapBase depth

matchedPhysicalGapLowerExact :
  ∀ spacingBase inverseSpacingBase depth →
  inverseSpacingBase * spacingBase ≡ 1ℚ →
  geometricPhysicalGapLower
    inverseSpacingBase spacingBase depth
  ≡ 1ℚ
matchedPhysicalGapLowerExact
    spacingBase inverseSpacingBase zero inverseLaw = solve []
matchedPhysicalGapLowerExact
    spacingBase inverseSpacingBase (suc depth) inverseLaw
  rewrite matchedPhysicalGapLowerExact
    spacingBase inverseSpacingBase depth inverseLaw
        | inverseLaw =
  solve (spacingBase ∷ inverseSpacingBase ∷ [])

quadraticPhysicalGapLowerExact :
  ∀ spacingBase inverseSpacingBase depth →
  inverseSpacingBase * spacingBase ≡ 1ℚ →
  geometricPhysicalGapLower
    inverseSpacingBase (spacingBase * spacingBase) depth
  ≡ Scale.pow spacingBase depth
quadraticPhysicalGapLowerExact
    spacingBase inverseSpacingBase zero inverseLaw = solve []
quadraticPhysicalGapLowerExact
    spacingBase inverseSpacingBase (suc depth) inverseLaw
  rewrite quadraticPhysicalGapLowerExact
    spacingBase inverseSpacingBase depth inverseLaw
        | inverseLaw =
  solve (spacingBase ∷ inverseSpacingBase ∷ Scale.pow spacingBase depth ∷ [])

configuredSpacingBase : ℚ
configuredSpacingBase = + 1 / 2

configuredInverseSpacingBase : ℚ
configuredInverseSpacingBase = + 2 / 1

configuredInverseSpacingLaw :
  configuredInverseSpacingBase * configuredSpacingBase ≡ 1ℚ
configuredInverseSpacingLaw = solve []

configuredMatchedPhysicalGapExact :
  ∀ depth →
  geometricPhysicalGapLower
    configuredInverseSpacingBase configuredSpacingBase depth
  ≡ 1ℚ
configuredMatchedPhysicalGapExact depth =
  matchedPhysicalGapLowerExact
    configuredSpacingBase configuredInverseSpacingBase depth
    configuredInverseSpacingLaw

configuredQuadraticPhysicalGapExact :
  ∀ depth →
  geometricPhysicalGapLower
    configuredInverseSpacingBase
    (configuredSpacingBase * configuredSpacingBase)
    depth
  ≡ Scale.pow configuredSpacingBase depth
configuredQuadraticPhysicalGapExact depth =
  quadraticPhysicalGapLowerExact
    configuredSpacingBase configuredInverseSpacingBase depth
    configuredInverseSpacingLaw

record ExponentialAllBetaToClayScaleBridge : Set₁ where
  field
    spacingBase : ℚ
    inverseSpacingBase : ℚ
    latticeGapBase : ℚ
    inverseSpacingLaw : inverseSpacingBase * spacingBase ≡ 1ℚ

    -- The load-bearing comparison.  Pointwise positivity of latticeGapBase is
    -- not a substitute for this cross-scale relation.
    gapToSpacingRatioControlled : Set
    continuumSchwingerCompatibility : Set
    physicalMassLowerSurvivesCutoff : Set

-- No canonical inhabitant is supplied by an all-finite-beta proof sketch.
