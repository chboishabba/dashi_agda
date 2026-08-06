module DASHI.Physics.YangMills.YangMillsLatticeGapScaleCompatibilityExact where

------------------------------------------------------------------------
-- PRIMARY CONTEXT
--
-- Arthur Jaffe and Edward Witten,
-- "Quantum Yang--Mills Theory", official Clay Mathematics Institute problem
-- description, published in The Millennium Prize Problems.  No DOI assigned.
--
-- Kenneth G. Wilson,
-- "Confinement of Quarks".
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- DASHI CONTRIBUTION
--
-- Make the cutoff-scale obstruction literal.  Positivity of a lattice gap at
-- every finite inverse coupling is weaker than a positive physical mass after
-- lattice spacing a tends to zero.  The required estimate is
--
--   m_* a <= Delta_latt(beta(a))
--
-- with m_*>0 independent of a.
--
-- A geometric exact model isolates the issue.  If a_n=q^n and the lattice gap
-- is also q^n, the physical scale is matched.  If the gap is q^(2n), every
-- finite-n gap is nonzero for positive q, but the rescaled gap is q^n and can
-- vanish along cutoff removal.  The module proves the finite algebra and keeps
-- the analytic limit theorem as a separate obligation.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _*_; _≤_; _<_; _/_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; trans)

pow : ℚ → Nat → ℚ
pow base zero = 1ℚ
pow base (suc depth) = base * pow base depth

spacingAt : ℚ → Nat → ℚ
spacingAt spacingBase depth = pow spacingBase depth

latticeGapAt : ℚ → Nat → ℚ
latticeGapAt gapBase depth = pow gapBase depth

powProduct :
  ∀ left right depth →
  pow (left * right) depth ≡ pow left depth * pow right depth
powProduct left right zero = solve []
powProduct left right (suc depth)
  rewrite powProduct left right depth =
  solve (left ∷ right ∷ pow left depth ∷ pow right depth ∷ [])

matchedGeometricGapExact :
  ∀ base depth →
  latticeGapAt base depth ≡ spacingAt base depth
matchedGeometricGapExact base depth = refl

quadraticGapIsSpacingSquared :
  ∀ spacingBase depth →
  latticeGapAt (spacingBase * spacingBase) depth
  ≡ spacingAt spacingBase depth * spacingAt spacingBase depth
quadraticGapIsSpacingSquared spacingBase depth =
  powProduct spacingBase spacingBase depth

record LatticeGapScaleCompatibility
    (SpacingIndex : Set)
    (spacing : SpacingIndex → ℚ)
    (gap : SpacingIndex → ℚ) : Set₁ where
  field
    physicalMass : ℚ
    physicalMassPositive : 0ℚ < physicalMass
    uniformScaleLower :
      ∀ index → physicalMass * spacing index ≤ gap index

record PointwiseFiniteCouplingGap (Beta : Set) : Set₁ where
  field
    gapAtBeta : Beta → ℚ
    gapPositiveAtEachBeta : ∀ beta → 0ℚ < gapAtBeta beta

record RunningCouplingScaleBridge (SpacingIndex Beta : Set) : Set₁ where
  field
    spacing : SpacingIndex → ℚ
    runningBeta : SpacingIndex → Beta
    latticeGap : Beta → ℚ
    physicalMass : ℚ
    physicalMassPositive : 0ℚ < physicalMass
    latticeGapScaleCompatibility :
      ∀ index →
      physicalMass * spacing index
      ≤ latticeGap (runningBeta index)

configuredSpacingBase : ℚ
configuredSpacingBase = + 1 / 2

configuredQuadraticGapBase : ℚ
configuredQuadraticGapBase = + 1 / 4

configuredFirstSpacingExact :
  spacingAt configuredSpacingBase (suc zero) ≡ + 1 / 2
configuredFirstSpacingExact = solve []

configuredFirstQuadraticGapExact :
  latticeGapAt configuredQuadraticGapBase (suc zero) ≡ + 1 / 4
configuredFirstQuadraticGapExact = solve []

configuredFirstGapIsHalfSpacing :
  (+ 2 / 1)
    * latticeGapAt configuredQuadraticGapBase (suc zero)
  ≡ spacingAt configuredSpacingBase (suc zero)
configuredFirstGapIsHalfSpacing = solve []

configuredQuadraticGapAtDepthExact :
  ∀ depth →
  latticeGapAt configuredQuadraticGapBase depth
  ≡ spacingAt configuredSpacingBase depth
    * spacingAt configuredSpacingBase depth
configuredQuadraticGapAtDepthExact depth =
  trans
    (cong
      (λ selected → pow selected depth)
      (solve []))
    (quadraticGapIsSpacingSquared configuredSpacingBase depth)

physicalRescaledGap : ℚ → ℚ → ℚ
physicalRescaledGap inverseSpacing latticeGap =
  inverseSpacing * latticeGap

quadraticGapRescalesToSpacing :
  ∀ spacing gap inverseSpacing →
  gap ≡ spacing * spacing →
  inverseSpacing * spacing ≡ 1ℚ →
  physicalRescaledGap inverseSpacing gap ≡ spacing
quadraticGapRescalesToSpacing
    spacing .(spacing * spacing) inverseSpacing refl inverseLaw =
  trans
    (solve (spacing ∷ inverseSpacing ∷ []))
    (trans
      (cong (λ selected → selected * spacing) inverseLaw)
      (solve (spacing ∷ [])))

record ContinuumScaleBoundary : Set₁ where
  field
    allFiniteBetaGapEstablished : Set
    runningCouplingEstablished : Set
    latticeGapScaleCompatibilityEstablished : Set
    crossSpacingSchwingerCauchyEstablished : Set
    continuumOSLimitEstablished : Set
    reconstructedHamiltonianGapEstablished : Set

-- The fields are deliberately distinct: even an all-beta lattice theorem does
-- not fill the physical scale, continuum, or spectral fields automatically.
