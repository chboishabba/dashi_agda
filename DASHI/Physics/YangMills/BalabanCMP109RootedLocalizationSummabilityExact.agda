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
-- Equations (0.24)--(0.27), pp. 257--258.  Localization domains X belong to
-- D_j, the connected finite unions of M-cubes, and d_j(X) is their normalized
-- shortest spanning-tree length.  After assuming
--
--       |E^(j)(X,U)| <= E0 exp(-kappa d_j(X))
--
-- with kappa sufficiently large, equation (0.26) performs the localization-
-- domain sum and obtains an O(1) rooted/local contribution.  Equation (0.27)
-- then explicitly spends only part of the exponential decay for a separate
-- large-domain gain, retaining exp(-(kappa/2)d_j(X)).
--
-- SOURCE REUSE
--
-- CMP119 uses the same classes D_j for its R^(j)(X) localization domains and
-- gives the stronger R bound (2.31), with an arbitrarily large decay constant.
-- Thus the combinatorial summability of exp(-kappa d_j(X)) is not a new P06
-- theorem peculiar to the R-operation: it is already part of the primary
-- localization geometry.  A separate explicit P06 count remains useful for
-- numerical constants, but is not logically required merely to establish a
-- finite rooted R sum.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP

open import DASHI.Physics.YangMills.CompactLieProofLevel

record RootedLocalizationSummability
    (Scale Root Domain : Set) : Set₁ where
  field
    rootedDomains : Scale → Root → List Domain
    residualDecay : Scale → Root → Domain → ℚ
    rootedSummabilityConstant : Scale → ℚ

    residualDecayNonnegative : ∀ scale root domain →
      0ℚ ≤ residualDecay scale root domain

    rootedDecaySum : Scale → Root → ℚ
    rootedDecaySum scale root =
      sumDecay (rootedDomains scale root) (residualDecay scale root)

    rootedDecaySummable : ∀ scale root →
      rootedDecaySum scale root ≤ rootedSummabilityConstant scale

  where
  sumDecay : ∀ {A : Set} → List A → (A → ℚ) → ℚ
  sumDecay [] term = 0ℚ
  sumDecay (value ∷ rest) term = term value + sumDecay rest term

open RootedLocalizationSummability public

cmp109Equation026RootedSummabilityLevel : ProofLevel
cmp109Equation026RootedSummabilityLevel = standardImported

cmp109Equation027DecaySplittingLevel : ProofLevel
cmp109Equation027DecaySplittingLevel = standardImported

-- The source theorem is about the literal D_j localization family and d_j.
-- Identifying an independently encoded repository polymer family with that
-- source carrier remains a representation theorem.
cmp109RootedLocalizationRepositoryCarrierLevel : ProofLevel
cmp109RootedLocalizationRepositoryCarrierLevel = conditional
