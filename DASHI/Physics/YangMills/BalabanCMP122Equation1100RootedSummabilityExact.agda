module DASHI.Physics.YangMills.BalabanCMP122Equation1100RootedSummabilityExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Tadeusz Bałaban,
-- "Convergent Renormalization Expansions for Lattice Gauge Theories",
-- Communications in Mathematical Physics 119 (1988), 243--285.
-- DOI: 10.1007/BF01217741.
--
-- Tadeusz Bałaban,
-- "Large Field Renormalization. II. Localization, Exponentiation, and Bounds
-- for the R Operation",
-- Communications in Mathematical Physics 122 (1989), 355--392.
-- DOI: 10.1007/BF01238433.
--
-- DASHI CONTRIBUTION
--
-- CMP109 (0.26) already sums sufficiently strong exp(-kappa d_j(X)) decay over
-- the rooted localization family D_j. CMP119 uses the same D_j family for the
-- R-terms, while CMP122 (1.100) supplies the extra small factor exp(-p0(g_k)).
-- Hence, after the repository norm spends part of the R-decay,
--
--   ||R_k(X)||_weighted <= s_k r_k(X),
--   sum_{X rooted} r_k(X) <= C_root,k
--
-- imply directly
--
--   sum_{X rooted} ||R_k(X)||_weighted <= s_k C_root,k.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP109RootedLocalizationSummabilityExact as Rooted
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm

sumWeighted : ∀ {A : Set} → List A → (A → ℚ) → ℚ
sumWeighted [] term = 0ℚ
sumWeighted (value ∷ rest) term = term value + sumWeighted rest term

sumScaledResidual : ∀ {A : Set} coefficient (values : List A) residual → ℚ
sumScaledResidual coefficient values residual =
  coefficient * Rooted.sumDecay values residual

sumPointwiseScaledBelow :
  ∀ {A : Set} coefficient (values : List A) term residual →
  0ℚ ≤ coefficient →
  (∀ value → term value ≤ coefficient * residual value) →
  sumWeighted values term ≤ sumScaledResidual coefficient values residual
sumPointwiseScaledBelow coefficient [] term residual coefficientNonnegative pointwise =
  ℚP.≤-refl
sumPointwiseScaledBelow coefficient (value ∷ rest) term residual
    coefficientNonnegative pointwise =
  let
    tail = sumPointwiseScaledBelow coefficient rest term residual
      coefficientNonnegative pointwise
    added = ℚP.+-mono-≤ (pointwise value) tail
    regroup :
      coefficient * residual value
        + coefficient * Rooted.sumDecay rest residual
      ≡ coefficient * Rooted.sumDecay (value ∷ rest) residual
    regroup = sym (ℚP.*-distribˡ-+ coefficient
      (residual value) (Rooted.sumDecay rest residual))
  in
  subst
    (λ upper → sumWeighted (value ∷ rest) term ≤ upper)
    regroup
    added

record Equation1100RootedSummableData
    (Scale Root Domain : Set) : Set₁ where
  field
    rooted : Rooted.RootedLocalizationSummability Scale Root Domain

    suppression : Scale → ℚ
    weightedRNorm : Scale → Root → Domain → ℚ

    suppressionNonnegative : ∀ scale → 0ℚ ≤ suppression scale

    equation1100AfterWeightSplit : ∀ scale root domain →
      weightedRNorm scale root domain
      ≤ suppression scale * Rooted.residualDecay rooted scale root domain

open Equation1100RootedSummableData public

rootedWeightedRContribution :
  ∀ {Scale Root Domain} →
  Equation1100RootedSummableData Scale Root Domain →
  Scale → Root → ℚ
rootedWeightedRContribution dataSet scale root =
  sumWeighted
    (Rooted.rootedDomains (rooted dataSet) scale root)
    (weightedRNorm dataSet scale root)

rootedWeightedRBelowSuppressionTimesSourceConstant :
  ∀ {Scale Root Domain}
    (dataSet : Equation1100RootedSummableData Scale Root Domain)
    scale root →
  rootedWeightedRContribution dataSet scale root
  ≤ suppression dataSet scale
      * Rooted.rootedSummabilityConstant (rooted dataSet) scale
rootedWeightedRBelowSuppressionTimesSourceConstant dataSet scale root =
  let
    domains = Rooted.rootedDomains (rooted dataSet) scale root
    residual = Rooted.residualDecay (rooted dataSet) scale root
    sourceSum = Rooted.sumDecay domains residual

    pointwiseSum :
      rootedWeightedRContribution dataSet scale root
      ≤ suppression dataSet scale * sourceSum
    pointwiseSum =
      sumPointwiseScaledBelow
        (suppression dataSet scale)
        domains
        (weightedRNorm dataSet scale root)
        residual
        (suppressionNonnegative dataSet scale)
        (equation1100AfterWeightSplit dataSet scale root)

    scaleSourceBound :
      suppression dataSet scale * sourceSum
      ≤ suppression dataSet scale
          * Rooted.rootedSummabilityConstant (rooted dataSet) scale
    scaleSourceBound = Norm.scaleNonnegative
      (suppression dataSet scale)
      (suppressionNonnegative dataSet scale)
      (Rooted.rootedDecaySumBound (rooted dataSet) scale root)
  in
  ℚP.≤-trans pointwiseSum scaleSourceBound

cmp109CMP122DirectRootedRAssemblyLevel : ProofLevel
cmp109CMP122DirectRootedRAssemblyLevel = machineChecked

cmp122DirectRootedRRepresentationLevel : ProofLevel
cmp122DirectRootedRRepresentationLevel = conditional
