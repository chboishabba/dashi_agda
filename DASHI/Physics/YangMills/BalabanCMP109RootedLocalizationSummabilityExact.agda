module DASHI.Physics.YangMills.BalabanCMP109RootedLocalizationSummabilityExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- DIRECT LOCATOR
--
-- Equations (0.24)--(0.27), pp. 257--258. Localization domains X belong to D_j,
-- the connected finite unions of M-cubes, and d_j(X) is their normalized
-- shortest spanning-tree length. After assuming exponential d_j-decay with a
-- sufficiently large decay constant, equation (0.26) performs the localization
-- domain sum and obtains an O(1) rooted/local contribution. Equation (0.27)
-- explicitly spends only part of that decay and retains a positive exponential
-- tree-size factor.
--
-- CMP119 uses the same D_j localization classes for R^(j)(X), with the stronger
-- bound (2.31) and a decay constant which may be chosen arbitrarily large after
-- fixing the other constructive parameters. Thus the rooted tree-decay
-- summability is primary-source geometry, not an R-specific combinatorial
-- invention.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _≤_)

open import DASHI.Physics.YangMills.CompactLieProofLevel

sumDecay : ∀ {A : Set} → List A → (A → ℚ) → ℚ
sumDecay [] term = 0ℚ
sumDecay (value ∷ rest) term = term value + sumDecay rest term

record RootedLocalizationSummability
    (Scale Root Domain : Set) : Set₁ where
  field
    rootedDomains : Scale → Root → List Domain
    residualDecay : Scale → Root → Domain → ℚ
    rootedSummabilityConstant : Scale → ℚ

    residualDecayNonnegative : ∀ scale root domain →
      0ℚ ≤ residualDecay scale root domain

    rootedDecaySummable : ∀ scale root →
      sumDecay (rootedDomains scale root) (residualDecay scale root)
      ≤ rootedSummabilityConstant scale

open RootedLocalizationSummability public

rootedDecaySum :
  ∀ {Scale Root Domain} →
  RootedLocalizationSummability Scale Root Domain →
  Scale → Root → ℚ
rootedDecaySum dataSet scale root =
  sumDecay (rootedDomains dataSet scale root)
    (residualDecay dataSet scale root)

rootedDecaySumBound :
  ∀ {Scale Root Domain}
    (dataSet : RootedLocalizationSummability Scale Root Domain)
    scale root →
  rootedDecaySum dataSet scale root
  ≤ rootedSummabilityConstant dataSet scale
rootedDecaySumBound dataSet = rootedDecaySummable dataSet

cmp109Equation026RootedSummabilityLevel : ProofLevel
cmp109Equation026RootedSummabilityLevel = standardImported

cmp109Equation027DecaySplittingLevel : ProofLevel
cmp109Equation027DecaySplittingLevel = standardImported

cmp109RootedLocalizationRepositoryCarrierLevel : ProofLevel
cmp109RootedLocalizationRepositoryCarrierLevel = conditional
