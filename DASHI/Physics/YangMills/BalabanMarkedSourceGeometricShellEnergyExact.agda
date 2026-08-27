module DASHI.Physics.YangMills.BalabanMarkedSourceGeometricShellEnergyExact where

------------------------------------------------------------------------
-- ROUND88: GEOMETRIC MARKED-SOURCE SHELL ENERGY -> UNIFORM COEFFICIENT CAP
--
-- PRIMARY / REUSED SOURCES
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. II.
-- Cluster Expansions", Communications in Mathematical Physics 116 (1988),
-- 1--22. DOI: 10.1007/BF01239022.
--
-- Exact finite geometric summation is reused from
-- `NSTriadKNRationalFiniteGeometricEnvelope`; the repository-specialized
-- summation theorem has no DOI.
--
-- MATHEMATICAL ROLE
--
-- CMP116 differentiated localization supplies exponential/tree-distance decay.
-- Once the ACTUAL differentiated source has been grouped into shell energies
-- E_d and one proves
--
--              E_d <= E0 r^d,
--
-- with 0 <= r < 1, there is no further Yang--Mills summability theorem.  For
-- any finite cutoff D,
--
--        sum_{d=0}^D E_d
--          <= E0 sum_{d=0}^D r^d
--          <= E0 B,
--
-- whenever (1-r)B = 1.  The second inequality is the already machine-checked
-- exact rational geometric theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_; _<_; nonNegative)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.Closure.NSTriadKNRationalFiniteGeometricEnvelope as Geometric

record GeometricMarkedShellEnergy : Set₁ where
  field
    shellEnergy : Nat → ℚ
    baseEnergy ratio geometricBound : ℚ

    baseEnergyNonnegative : 0ℚ ≤ baseEnergy
    ratioNonnegative : 0ℚ ≤ ratio
    oneMinusRatioPositive : 0ℚ < 1ℚ - ratio
    geometricBoundIdentity : (1ℚ - ratio) * geometricBound ≡ 1ℚ

    shellEnergyBound : ∀ depth →
      shellEnergy depth ≤ baseEnergy * Geometric.pow ratio depth
open GeometricMarkedShellEnergy public

shellEnergyPrefix : GeometricMarkedShellEnergy → Nat → ℚ
shellEnergyPrefix dataSet zero = shellEnergy dataSet zero
shellEnergyPrefix dataSet (suc cutoff) =
  shellEnergy dataSet (suc cutoff) + shellEnergyPrefix dataSet cutoff

envelopePrefix : GeometricMarkedShellEnergy → Nat → ℚ
envelopePrefix dataSet cutoff =
  baseEnergy dataSet * Geometric.partialSum (ratio dataSet) cutoff

shellEnergyPrefixBelowEnvelope :
  (dataSet : GeometricMarkedShellEnergy) → ∀ cutoff →
  shellEnergyPrefix dataSet cutoff ≤ envelopePrefix dataSet cutoff
shellEnergyPrefixBelowEnvelope dataSet zero =
  shellEnergyBound dataSet zero
shellEnergyPrefixBelowEnvelope dataSet (suc cutoff) =
  let
    current = shellEnergyBound dataSet (suc cutoff)
    previous = shellEnergyPrefixBelowEnvelope dataSet cutoff
    added = ℚP.+-mono-≤ current previous
    algebra :
      baseEnergy dataSet * Geometric.pow (ratio dataSet) (suc cutoff)
        + envelopePrefix dataSet cutoff
      ≡ envelopePrefix dataSet (suc cutoff)
    algebra = ℚRing.solve-∀
      (baseEnergy dataSet)
      (Geometric.pow (ratio dataSet) (suc cutoff))
      (Geometric.partialSum (ratio dataSet) cutoff)
  in
  subst
    (λ upper → shellEnergyPrefix dataSet (suc cutoff) ≤ upper)
    algebra
    added

geometricEnvelopeUniformBound :
  (dataSet : GeometricMarkedShellEnergy) → ∀ cutoff →
  envelopePrefix dataSet cutoff
  ≤ baseEnergy dataSet * geometricBound dataSet
geometricEnvelopeUniformBound dataSet cutoff =
  let
    partial = Geometric.geometricPartialSumBound
      (ratio dataSet)
      (geometricBound dataSet)
      cutoff
      (ratioNonnegative dataSet)
      (oneMinusRatioPositive dataSet)
      (geometricBoundIdentity dataSet)

    instance
      baseNonnegative = nonNegative (baseEnergyNonnegative dataSet)
  in
  ℚP.*-monoˡ-≤-nonNeg (baseEnergy dataSet) partial

markedSourceShellEnergyUniformBound :
  (dataSet : GeometricMarkedShellEnergy) → ∀ cutoff →
  shellEnergyPrefix dataSet cutoff
  ≤ baseEnergy dataSet * geometricBound dataSet
markedSourceShellEnergyUniformBound dataSet cutoff =
  ℚP.≤-trans
    (shellEnergyPrefixBelowEnvelope dataSet cutoff)
    (geometricEnvelopeUniformBound dataSet cutoff)

markedSourceGeometricShellSummationLevel : ProofLevel
markedSourceGeometricShellSummationLevel = machineChecked

markedSourceShellEnergyToUniformCoefficientCapLevel : ProofLevel
markedSourceShellEnergyToUniformCoefficientCapLevel = machineChecked

-- TRUE remaining physical B energy seam: on the literal differentiated CMP116
-- source, define the shell energies and prove one cutoff/volume/scale-uniform
-- geometric majorant E_d <= E0 r^d with r<1.  Summation and Cauchy/Hilbert
-- transport are no longer physical lemmas.
physicalCMP116GeometricDifferentiatedShellEnergyLevel : ProofLevel
physicalCMP116GeometricDifferentiatedShellEnergyLevel = conditional
