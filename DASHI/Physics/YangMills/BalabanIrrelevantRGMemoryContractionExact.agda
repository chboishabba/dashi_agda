module DASHI.Physics.YangMills.BalabanIrrelevantRGMemoryContractionExact where

------------------------------------------------------------------------
-- ROUND84: CONTRACTIVE IRRELEVANT RG COORDINATE -> GEOMETRIC BETA MEMORY
--
-- PRIMARY SOURCES / CALIBRATION
--
-- Stefan Banach,
-- "Sur les operations dans les ensembles abstraits et leur application aux
-- equations integrales", Fundamenta Mathematicae 3 (1922), 133--181.
-- DOI: 10.4064/fm-3-1-133-181.
--
-- Tadeusz Bałaban,
-- "Convergent Renormalization Expansions for Lattice Gauge Theories",
-- Communications in Mathematical Physics 119 (1988), 243--285.
-- DOI: 10.1007/BF01217741.
--
-- David C. Brydges, John Dimock and Thomas R. Hurd,
-- "Estimates on Renormalization Group Transformations",
-- Canadian Journal of Mathematics 50 (1998), 756--793.
-- DOI: 10.4153/CJM-1998-041-5.
--
-- IMPORTANT SEMANTIC BOUNDARY
--
-- This theorem concerns ONLY an irrelevant/polymer coordinate after all declared
-- marginal/relevant coordinates (in particular the current running coupling) are
-- held fixed.  It does not assert exponential forgetting of g_{j-1}; CMP109 says
-- that dependence is important.
--
-- DASHI CONTRIBUTION
--
-- Suppose two admissible histories differ in one irrelevant coordinate by D_0,
-- and the active RG map contracts that coordinate by q<=1/2 at every subsequent
-- step.  If the beta correction extracted from that irrelevant coordinate is
-- L-Lipschitz, then after d steps
--
--       D_d <= D_0 2^{-d},
--       |delta beta_d| <= L D_0 2^{-d}.
--
-- Hence the geometric beta-memory shell is not an additional gauge-theory
-- localization theorem once the source-native nonlinear RG contraction and the
-- same-object Lipschitz beta projection are identified.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _*_; _≤_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact as Geo
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm

record ContractiveIrrelevantMemory : Set₁ where
  field
    contraction : ℚ
    contractionNonnegative : 0ℚ ≤ contraction
    contractionAtMostHalf : contraction ≤ Geo.half

    initialDistance : ℚ
    initialDistanceNonnegative : 0ℚ ≤ initialDistance

    distanceAtDepth : Nat → ℚ
    distanceNonnegative : ∀ depth → 0ℚ ≤ distanceAtDepth depth
    distanceAtZero : distanceAtDepth zero ≤ initialDistance
    oneStepContraction : ∀ depth →
      distanceAtDepth (suc depth)
      ≤ contraction * distanceAtDepth depth

open ContractiveIrrelevantMemory public

distanceBelowDyadic :
  (dataSet : ContractiveIrrelevantMemory) → ∀ depth →
  distanceAtDepth dataSet depth
  ≤ initialDistance dataSet * Geo.halfPower depth
distanceBelowDyadic dataSet zero =
  subst
    (λ upper → distanceAtDepth dataSet zero ≤ upper)
    (ℚRing.solve-∀ (initialDistance dataSet))
    (distanceAtZero dataSet)
distanceBelowDyadic dataSet (suc depth) =
  let
    d = distanceAtDepth dataSet depth
    D = initialDistance dataSet
    q = contraction dataSet
    induction = distanceBelowDyadic dataSet depth

    qdBelowHalfD : q * d ≤ Geo.half * (D * Geo.halfPower depth)
    qdBelowHalfD =
      ℚP.*-mono-≤
        (contractionNonnegative dataSet)
        (contractionAtMostHalf dataSet)
        (distanceNonnegative dataSet depth)
        induction

    step = ℚP.≤-trans (oneStepContraction dataSet depth) qdBelowHalfD
  in
  subst
    (λ upper → distanceAtDepth dataSet (suc depth) ≤ upper)
    (ℚRing.solve-∀ D Geo.half (Geo.halfPower depth))
    step

record LipschitzIrrelevantBetaProjection
    (memory : ContractiveIrrelevantMemory) : Set₁ where
  field
    lipschitzConstant : ℚ
    lipschitzNonnegative : 0ℚ ≤ lipschitzConstant
    betaDifference : Nat → ℚ
    betaDifferenceNonnegative : ∀ depth → 0ℚ ≤ betaDifference depth
    betaDifferenceBelowDistance : ∀ depth →
      betaDifference depth
      ≤ lipschitzConstant * distanceAtDepth memory depth

open LipschitzIrrelevantBetaProjection public

betaIrrelevantMemoryBelowDyadic :
  ∀ {memory}
    (projection : LipschitzIrrelevantBetaProjection memory) depth →
  betaDifference projection depth
  ≤ (lipschitzConstant projection * initialDistance memory)
      * Geo.halfPower depth
betaIrrelevantMemoryBelowDyadic {memory} projection depth =
  let
    L = lipschitzConstant projection
    D = initialDistance memory
    scaled = Norm.scaleNonnegative
      L (lipschitzNonnegative projection)
      (distanceBelowDyadic memory depth)
    chained = ℚP.≤-trans
      (betaDifferenceBelowDistance projection depth)
      scaled
  in
  subst
    (λ upper → betaDifference projection depth ≤ upper)
    (ℚRing.solve-∀ L D (Geo.halfPower depth))
    chained

irrelevantRGMemoryContractionCompilerLevel : ProofLevel
irrelevantRGMemoryContractionCompilerLevel = machineChecked

irrelevantRGToBetaLipschitzCompilerLevel : ProofLevel
irrelevantRGToBetaLipschitzCompilerLevel = machineChecked

-- Physical seam: identify the literal source-native irrelevant/polymer coordinate
-- with the contractive RG coordinate, and prove the literal beta correction is a
-- uniformly Lipschitz projection on the SAME common analytic domain.
physicalIrrelevantCoordinateAndBetaLipschitzIdentificationLevel : ProofLevel
physicalIrrelevantCoordinateAndBetaLipschitzIdentificationLevel = conditional
