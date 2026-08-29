module DASHI.Physics.YangMills.BalabanRowBActivityEntropyToShellEnergyExact where

------------------------------------------------------------------------
-- ROW B: ACTIVITY DECAY + POLYMER ENTROPY -> GEOMETRIC SHELL ENERGY
--
-- Primary source:
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. II.
-- Cluster Expansions", Communications in Mathematical Physics 116 (1988),
-- 1--22. DOI: 10.1007/BF01239022.
--
-- If the differentiated activity in shell n is bounded by A a^n and the shell
-- multiplicity/entropy by B e^n, then
--
--             E_n <= (A B) (a e)^n.
--
-- This module also constructs the exact `GeometricMarkedShellEnergy` consumed
-- by the existing uniform summation compiler once the combined ratio has a
-- positive geometric denominator.  Thus the source-facing Row-B task is only
-- the literal CMP116 activity/entropy identification and the strict ratio gap.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _-_; _*_; _≤_; _<_; NonNegative)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (_≡_; cong; subst; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.Closure.NSTriadKNRationalFiniteGeometricEnvelope as Geometric
import DASHI.Physics.YangMills.BalabanMarkedSourceGeometricShellEnergyExact as Shell

mulNN : ∀ {left right} → 0ℚ ≤ left → 0ℚ ≤ right → 0ℚ ≤ left * right
mulNN {left} {right} leftNN rightNN =
  let
    instance
      leftNonnegative : NonNegative left
      leftNonnegative = ℚ.nonNegative leftNN
      rightNonnegative : NonNegative right
      rightNonnegative = ℚ.nonNegative rightNN
  in
  ℚP.nonNegative⁻¹ (left * right)

powProductExact : ∀ left right depth →
  Geometric.pow left depth * Geometric.pow right depth
  ≡ Geometric.pow (left * right) depth
powProductExact left right zero = ℚRing.solve-∀ left right
powProductExact left right (suc depth) =
  let
    induction = powProductExact left right depth

    reassociate :
      (left * Geometric.pow left depth)
        * (right * Geometric.pow right depth)
      ≡ (left * right)
        * (Geometric.pow left depth * Geometric.pow right depth)
    reassociate = ℚRing.solve-∀
      left right (Geometric.pow left depth) (Geometric.pow right depth)

    replaceTail :
      (left * right)
        * (Geometric.pow left depth * Geometric.pow right depth)
      ≡ (left * right) * Geometric.pow (left * right) depth
    replaceTail = cong (λ tail → (left * right) * tail) induction
  in
  trans reassociate replaceTail

record MarkedActivityEntropyShellData : Set₁ where
  field
    activity shellMultiplicity shellEnergy : Nat → ℚ

    activityScale entropyScale : ℚ
    activityRatio entropyRatio : ℚ

    activityScaleNonnegative : 0ℚ ≤ activityScale
    entropyScaleNonnegative : 0ℚ ≤ entropyScale
    activityRatioNonnegative : 0ℚ ≤ activityRatio
    entropyRatioNonnegative : 0ℚ ≤ entropyRatio

    activityNonnegative : ∀ depth → 0ℚ ≤ activity depth
    shellMultiplicityNonnegative : ∀ depth → 0ℚ ≤ shellMultiplicity depth

    activityMajorant : ∀ depth →
      activity depth ≤ activityScale * Geometric.pow activityRatio depth

    entropyMajorant : ∀ depth →
      shellMultiplicity depth ≤ entropyScale * Geometric.pow entropyRatio depth

    shellEnergyBelowMultiplicityTimesActivity : ∀ depth →
      shellEnergy depth ≤ shellMultiplicity depth * activity depth

open MarkedActivityEntropyShellData public

combinedBaseEnergy : MarkedActivityEntropyShellData → ℚ
combinedBaseEnergy dataSet = activityScale dataSet * entropyScale dataSet

combinedShellRatio : MarkedActivityEntropyShellData → ℚ
combinedShellRatio dataSet = activityRatio dataSet * entropyRatio dataSet

combinedBaseEnergyNonnegative :
  (dataSet : MarkedActivityEntropyShellData) →
  0ℚ ≤ combinedBaseEnergy dataSet
combinedBaseEnergyNonnegative dataSet =
  mulNN
    (activityScaleNonnegative dataSet)
    (entropyScaleNonnegative dataSet)

combinedShellRatioNonnegative :
  (dataSet : MarkedActivityEntropyShellData) →
  0ℚ ≤ combinedShellRatio dataSet
combinedShellRatioNonnegative dataSet =
  mulNN
    (activityRatioNonnegative dataSet)
    (entropyRatioNonnegative dataSet)

activityEntropyGiveGeometricShellEnergy :
  (dataSet : MarkedActivityEntropyShellData) → ∀ depth →
  shellEnergy dataSet depth
  ≤ combinedBaseEnergy dataSet
      * Geometric.pow (combinedShellRatio dataSet) depth
activityEntropyGiveGeometricShellEnergy dataSet depth =
  let
    count = shellMultiplicity dataSet depth
    act = activity dataSet depth
    A = activityScale dataSet
    B = entropyScale dataSet
    a = activityRatio dataSet
    e = entropyRatio dataSet

    productBound :
      count * act
      ≤ (B * Geometric.pow e depth) * (A * Geometric.pow a depth)
    productBound =
      ℚP.*-mono-≤
        (shellMultiplicityNonnegative dataSet depth)
        (entropyMajorant dataSet depth)
        (activityNonnegative dataSet depth)
        (activityMajorant dataSet depth)

    shellToRawMajorant :
      shellEnergy dataSet depth
      ≤ (B * Geometric.pow e depth) * (A * Geometric.pow a depth)
    shellToRawMajorant =
      ℚP.≤-trans
        (shellEnergyBelowMultiplicityTimesActivity dataSet depth)
        productBound

    reorder :
      (B * Geometric.pow e depth) * (A * Geometric.pow a depth)
      ≡ (A * B)
        * (Geometric.pow a depth * Geometric.pow e depth)
    reorder = ℚRing.solve-∀
      A B (Geometric.pow a depth) (Geometric.pow e depth)

    replacePower :
      (A * B)
        * (Geometric.pow a depth * Geometric.pow e depth)
      ≡ (A * B) * Geometric.pow (a * e) depth
    replacePower =
      cong (λ tail → (A * B) * tail) (powProductExact a e depth)
  in
  subst
    (λ upper → shellEnergy dataSet depth ≤ upper)
    (trans reorder replacePower)
    shellToRawMajorant

record SummableMarkedActivityEntropyShellData : Set₁ where
  field
    sourceData : MarkedActivityEntropyShellData
    geometricBound : ℚ
    oneMinusCombinedRatioPositive :
      0ℚ < 1ℚ - combinedShellRatio sourceData
    geometricBoundIdentity :
      (1ℚ - combinedShellRatio sourceData) * geometricBound ≡ 1ℚ

open SummableMarkedActivityEntropyShellData public

asGeometricMarkedShellEnergy :
  SummableMarkedActivityEntropyShellData → Shell.GeometricMarkedShellEnergy
asGeometricMarkedShellEnergy dataSet = record
  { Shell.GeometricMarkedShellEnergy.shellEnergy =
      shellEnergy (sourceData dataSet)
  ; Shell.GeometricMarkedShellEnergy.baseEnergy =
      combinedBaseEnergy (sourceData dataSet)
  ; Shell.GeometricMarkedShellEnergy.ratio =
      combinedShellRatio (sourceData dataSet)
  ; Shell.GeometricMarkedShellEnergy.geometricBound = geometricBound dataSet
  ; Shell.GeometricMarkedShellEnergy.baseEnergyNonnegative =
      combinedBaseEnergyNonnegative (sourceData dataSet)
  ; Shell.GeometricMarkedShellEnergy.ratioNonnegative =
      combinedShellRatioNonnegative (sourceData dataSet)
  ; Shell.GeometricMarkedShellEnergy.oneMinusRatioPositive =
      oneMinusCombinedRatioPositive dataSet
  ; Shell.GeometricMarkedShellEnergy.geometricBoundIdentity =
      geometricBoundIdentity dataSet
  ; Shell.GeometricMarkedShellEnergy.shellEnergyBound =
      activityEntropyGiveGeometricShellEnergy (sourceData dataSet)
  }

activityEntropyPrefixUniformBound :
  (dataSet : SummableMarkedActivityEntropyShellData) → ∀ cutoff →
  Shell.shellEnergyPrefix (asGeometricMarkedShellEnergy dataSet) cutoff
  ≤ combinedBaseEnergy (sourceData dataSet) * geometricBound dataSet
activityEntropyPrefixUniformBound dataSet =
  Shell.markedSourceShellEnergyUniformBound
    (asGeometricMarkedShellEnergy dataSet)

rowBActivityEntropyProductAlgebraLevel : ProofLevel
rowBActivityEntropyProductAlgebraLevel = machineChecked

rowBActivityEntropyToGeometricShellLevel : ProofLevel
rowBActivityEntropyToGeometricShellLevel = machineChecked

rowBActivityEntropyUniformSummationLevel : ProofLevel
rowBActivityEntropyUniformSummationLevel = machineChecked

literalCMP116DifferentiatedActivityMajorantLevel : ProofLevel
literalCMP116DifferentiatedActivityMajorantLevel = conditional

literalCMP116ShellEntropyMajorantLevel : ProofLevel
literalCMP116ShellEntropyMajorantLevel = conditional

literalCMP116CombinedShellRatioStrictlyBelowOneLevel : ProofLevel
literalCMP116CombinedShellRatioStrictlyBelowOneLevel = conditional
