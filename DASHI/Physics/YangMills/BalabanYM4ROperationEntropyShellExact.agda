module DASHI.Physics.YangMills.BalabanYM4ROperationEntropyShellExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Convergent Renormalization Expansions for Lattice Gauge Theories",
-- Communications in Mathematical Physics 119 (1988), 243--285.
-- DOI: 10.1007/BF01217741.
--
-- Tadeusz Bałaban,
-- "Large Field Renormalization. II. Localization, Exponentiation, and Bounds
-- for the R Operation", Communications in Mathematical Physics 122 (1989),
-- 355--392. DOI: 10.1007/BF01238433.
--
-- Roman Kotecky and David Preiss,
-- "Cluster Expansion for Abstract Polymer Models",
-- Communications in Mathematical Physics 103 (1986), 491--498.
-- DOI: 10.1007/BF01211762.
--
-- DASHI CONTRIBUTION
--
-- Close the finite combinatorial step between pointwise R-polymer decay and
-- the rooted shell amplitude consumed by the lightweight Gate-4 shared-slack
-- theorem.  For a literal finite rooted shell S_n,
--
--      ||R(X)||_w <= b_n       for X in S_n,
--      |S_n| b_n <= a 2^{-n}
--
-- imply
--
--      sum_{X in S_n} ||R(X)||_w <= a 2^{-n}.
--
-- Hence the remaining source-specific work is precisely the pointwise
-- boundary-uniform R estimate and the rooted entropy/cardinality estimate in
-- the SAME polymer-weight convention.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.List.Base using (length)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym; trans; cong)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanYM4LargeFieldContributionSharedSlackExact as LF

infix 4 _∈_
data _∈_ {A : Set} (value : A) : List A → Set where
  here : ∀ {rest} → value ∈ (value ∷ rest)
  there : ∀ {head rest} → value ∈ rest → value ∈ (head ∷ rest)

natAsRational : Nat → ℚ
natAsRational zero = 0ℚ
natAsRational (suc n) = 1ℚ + natAsRational n

natAsRationalSuc : ∀ n → natAsRational (suc n) ≡ 1ℚ + natAsRational n
natAsRationalSuc n = refl

regroupNatAsRational : ∀ n upper →
  upper + natAsRational n * upper
  ≡ natAsRational (suc n) * upper
regroupNatAsRational n upper =
  subst
    (λ count → upper + natAsRational n * upper ≡ count * upper)
    (sym (natAsRationalSuc n))
    (trans
      (cong
        (λ first → first + natAsRational n * upper)
        (sym (ℚP.*-identityˡ upper)))
      (sym (ℚP.*-distribʳ-+ upper 1ℚ (natAsRational n))))

sumRational : ∀ {A : Set} → List A → (A → ℚ) → ℚ
sumRational [] term = 0ℚ
sumRational (value ∷ values) term = term value + sumRational values term

sumMemberwiseBelowLengthTimes :
  ∀ {A : Set} (values : List A) (term : A → ℚ) upper →
  (∀ value → value ∈ values → term value ≤ upper) →
  sumRational values term ≤ natAsRational (length values) * upper
sumMemberwiseBelowLengthTimes [] term upper pointwise =
  subst
    (λ bound → 0ℚ ≤ bound)
    (sym (ℚP.*-zeroˡ upper))
    ℚP.≤-refl
sumMemberwiseBelowLengthTimes (value ∷ values) term upper pointwise =
  let
    tailBound =
      sumMemberwiseBelowLengthTimes values term upper
        (λ tailValue member → pointwise tailValue (there member))
    added = ℚP.+-mono-≤ (pointwise value here) tailBound
    regroup :
      upper + natAsRational (length values) * upper
      ≡ natAsRational (suc (length values)) * upper
    regroup = regroupNatAsRational (length values) upper
  in
  subst
    (λ rhs → term value + sumRational values term ≤ rhs)
    regroup
    added

record ROperationRootedEntropyShell
    (Scale Volume Root Polymer : Set) : Set₁ where
  field
    shellPolymers : Scale → Volume → Root → Nat → List Polymer
    weightedRNorm : Scale → Volume → Root → Polymer → ℚ
    pointwiseEnvelope : Scale → Volume → Root → Nat → ℚ
    shellAmplitude : Scale → ℚ

    pointwiseROperationDecay : ∀ scale volume root depth polymer →
      polymer ∈ shellPolymers scale volume root depth →
      weightedRNorm scale volume root polymer
      ≤ pointwiseEnvelope scale volume root depth

    entropyTimesPointwiseFitsGeometric : ∀ scale volume root depth →
      natAsRational (length (shellPolymers scale volume root depth))
        * pointwiseEnvelope scale volume root depth
      ≤ LF.scaledShellMajorant (shellAmplitude scale) depth

open ROperationRootedEntropyShell public

rootedRActivityShell :
  ∀ {Scale Volume Root Polymer} →
  ROperationRootedEntropyShell Scale Volume Root Polymer →
  Scale → Volume → Root → Nat → ℚ
rootedRActivityShell dataSet scale volume root depth =
  sumRational
    (shellPolymers dataSet scale volume root depth)
    (weightedRNorm dataSet scale volume root)

sumShellPointwiseBound :
  ∀ {Scale Volume Root Polymer}
    (dataSet : ROperationRootedEntropyShell Scale Volume Root Polymer)
    scale volume root depth →
  rootedRActivityShell dataSet scale volume root depth
  ≤ natAsRational
      (length (shellPolymers dataSet scale volume root depth))
      * pointwiseEnvelope dataSet scale volume root depth
sumShellPointwiseBound dataSet scale volume root depth =
  sumMemberwiseBelowLengthTimes
    (shellPolymers dataSet scale volume root depth)
    (weightedRNorm dataSet scale volume root)
    (pointwiseEnvelope dataSet scale volume root depth)
    (pointwiseROperationDecay dataSet scale volume root depth)

rootedRActivityShellBelowGeometric :
  ∀ {Scale Volume Root Polymer}
    (dataSet : ROperationRootedEntropyShell Scale Volume Root Polymer)
    scale volume root depth →
  rootedRActivityShell dataSet scale volume root depth
  ≤ LF.scaledShellMajorant (shellAmplitude dataSet scale) depth
rootedRActivityShellBelowGeometric dataSet scale volume root depth =
  ℚP.≤-trans
    (sumShellPointwiseBound dataSet scale volume root depth)
    (entropyTimesPointwiseFitsGeometric dataSet scale volume root depth)

rOperationFiniteEntropyShellAssemblyLevel : ProofLevel
rOperationFiniteEntropyShellAssemblyLevel = machineChecked

rOperationPointwiseDecayPhysicalLevel : ProofLevel
rOperationPointwiseDecayPhysicalLevel = conditional

rootedPolymerEntropyTimesDecayPhysicalLevel : ProofLevel
rootedPolymerEntropyTimesDecayPhysicalLevel = conditional
