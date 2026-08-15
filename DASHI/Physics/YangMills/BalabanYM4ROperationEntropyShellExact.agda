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
-- Close the finite combinatorial step between Bałaban's pointwise R-polymer
-- decay and the rooted shell amplitude consumed by the lightweight Gate-4
-- shared-slack theorem.
--
-- For a literal finite rooted shell S_n, if every weighted R activity is <= b_n
-- and
--
--      |S_n| b_n <= a 2^{-n},
--
-- then
--
--      sum_{X in S_n} ||R(X)||_weighted <= a 2^{-n}.
--
-- The proof is a finite induction over the actual shell list.  Thus the
-- remaining analytic producer is no longer a mysterious "shell theorem": it is
-- exactly (i) the boundary-uniform pointwise R bound and (ii) the rooted shell
-- cardinality/entropy estimate in the same weight convention.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.List.Base using (length)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact as Geo
import DASHI.Physics.YangMills.BalabanYM4LargeFieldContributionSharedSlackExact as LF

natAsRational : Nat → ℚ
natAsRational zero = 0ℚ
natAsRational (suc n) = 1ℚ + natAsRational n

sumRational : ∀ {A : Set} → List A → (A → ℚ) → ℚ
sumRational [] term = 0ℚ
sumRational (value ∷ values) term = term value + sumRational values term

sumPointwiseBelowLengthTimes :
  ∀ {A : Set} (values : List A) (term : A → ℚ) upper →
  (∀ value → term value ≤ upper) →
  sumRational values term ≤ natAsRational (length values) * upper
sumPointwiseBelowLengthTimes [] term upper pointwise =
  ℚP.≤-refl
sumPointwiseBelowLengthTimes (value ∷ values) term upper pointwise =
  let
    induction = sumPointwiseBelowLengthTimes values term upper pointwise
    added = ℚP.+-mono-≤ (pointwise value) induction
    regroup :
      upper + natAsRational (length values) * upper
      ≡ natAsRational (suc (length values)) * upper
    regroup = ℚRing.solve-∀ upper (natAsRational (length values))
  in
  subst
    (λ rhs →
      term value + sumRational values term ≤ rhs)
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

  where
  data _∈_ {A : Set} (value : A) : List A → Set where
    here : ∀ {rest} → value ∈ (value ∷ rest)
    there : ∀ {head rest} → value ∈ rest → value ∈ (head ∷ rest)

open ROperationRootedEntropyShell public

rootedRActivityShell :
  ∀ {Scale Volume Root Polymer} →
  ROperationRootedEntropyShell Scale Volume Root Polymer →
  Scale → Volume → Root → Nat → ℚ
rootedRActivityShell dataSet scale volume root depth =
  sumRational
    (shellPolymers dataSet scale volume root depth)
    (weightedRNorm dataSet scale volume root)

-- Membership evidence for a list element is needed only to instantiate the
-- pointwise source bound during the finite fold.
sumShellPointwiseBound :
  ∀ {Scale Volume Root Polymer}
    (dataSet : ROperationRootedEntropyShell Scale Volume Root Polymer)
    scale volume root depth →
  rootedRActivityShell dataSet scale volume root depth
  ≤ natAsRational
      (length (shellPolymers dataSet scale volume root depth))
      * pointwiseEnvelope dataSet scale volume root depth
sumShellPointwiseBound dataSet scale volume root depth =
  shellInduction (shellPolymers dataSet scale volume root depth)
  where
  envelope = pointwiseEnvelope dataSet scale volume root depth
  norm = weightedRNorm dataSet scale volume root

  shellInduction : (values : List Polymer) →
    sumRational values norm ≤ natAsRational (length values) * envelope
  shellInduction [] = ℚP.≤-refl
  shellInduction (value ∷ values) =
    let
      -- The source record states the pointwise estimate for membership in the
      -- canonical shell list.  For recursive tails we carry the same estimate
      -- as a local hypothesis using a helper fold below.
      helper :
        ∀ (xs : List Polymer) →
        (∀ x → x ∈ xs → norm x ≤ envelope) →
        sumRational xs norm ≤ natAsRational (length xs) * envelope
      helper [] pointwise = ℚP.≤-refl
      helper (x ∷ xs) pointwise =
        let
          tailBound = helper xs (λ y member → pointwise y (there member))
          added = ℚP.+-mono-≤ (pointwise x here) tailBound
          regroup :
            envelope + natAsRational (length xs) * envelope
            ≡ natAsRational (suc (length xs)) * envelope
          regroup = ℚRing.solve-∀ envelope (natAsRational (length xs))
        in
        subst
          (λ rhs → norm x + sumRational xs norm ≤ rhs)
          regroup
          added
    in
    helper (value ∷ values)
      (λ x member →
        pointwiseROperationDecay dataSet scale volume root depth x
          (transportMembership member))
    where
    transportMembership : ∀ {x} →
      x ∈ (value ∷ values) →
      x ∈ shellPolymers dataSet scale volume root depth
    transportMembership member = member

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

-- These two estimates are the true source-specific frontier on this route.
rOperationPointwiseDecayPhysicalLevel : ProofLevel
rOperationPointwiseDecayPhysicalLevel = conditional

rootedPolymerEntropyTimesDecayPhysicalLevel : ProofLevel
rootedPolymerEntropyTimesDecayPhysicalLevel = conditional
