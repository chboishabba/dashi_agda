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
-- The existing marked-source shell-energy compiler starts after one has already
-- produced E_n <= E0 r^n.  This module moves that boundary one step upstream.
-- If the differentiated activity in shell n is bounded by A a^n and the shell
-- multiplicity/entropy by B e^n, then the shell energy is bounded by
--
--             E_n <= (A B) (a e)^n.
--
-- Therefore the physical CMP116 task is now source-native identification of the
-- differentiated marked activity and constants with a*e<1; the multiplication
-- and geometric-shell reduction are exact algebra.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (_≡_; cong; subst; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

pow : ℚ → Nat → ℚ
pow ratio zero = 1ℚ
pow ratio (suc depth) = ratio * pow ratio depth

powProductExact : ∀ left right depth →
  pow left depth * pow right depth ≡ pow (left * right) depth
powProductExact left right zero = ℚRing.solve-∀ left right
powProductExact left right (suc depth) =
  let
    induction = powProductExact left right depth

    reassociate :
      (left * pow left depth) * (right * pow right depth)
      ≡ (left * right) * (pow left depth * pow right depth)
    reassociate = ℚRing.solve-∀
      left right (pow left depth) (pow right depth)

    replaceTail :
      (left * right) * (pow left depth * pow right depth)
      ≡ (left * right) * pow (left * right) depth
    replaceTail = cong (λ tail → (left * right) * tail) induction
  in
  trans reassociate replaceTail

record MarkedActivityEntropyShellData : Set₁ where
  field
    activity shellMultiplicity shellEnergy : Nat → ℚ

    activityScale entropyScale : ℚ
    activityRatio entropyRatio : ℚ

    activityNonnegative : ∀ depth → 0ℚ ≤ activity depth
    shellMultiplicityNonnegative : ∀ depth → 0ℚ ≤ shellMultiplicity depth

    activityMajorant : ∀ depth →
      activity depth ≤ activityScale * pow activityRatio depth

    entropyMajorant : ∀ depth →
      shellMultiplicity depth ≤ entropyScale * pow entropyRatio depth

    shellEnergyBelowMultiplicityTimesActivity : ∀ depth →
      shellEnergy depth ≤ shellMultiplicity depth * activity depth

open MarkedActivityEntropyShellData public

combinedBaseEnergy : MarkedActivityEntropyShellData → ℚ
combinedBaseEnergy dataSet = activityScale dataSet * entropyScale dataSet

combinedShellRatio : MarkedActivityEntropyShellData → ℚ
combinedShellRatio dataSet = activityRatio dataSet * entropyRatio dataSet

activityEntropyGiveGeometricShellEnergy :
  (dataSet : MarkedActivityEntropyShellData) → ∀ depth →
  shellEnergy dataSet depth
  ≤ combinedBaseEnergy dataSet * pow (combinedShellRatio dataSet) depth
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
      ≤ (B * pow e depth) * (A * pow a depth)
    productBound =
      ℚP.*-mono-≤
        (shellMultiplicityNonnegative dataSet depth)
        (entropyMajorant dataSet depth)
        (activityNonnegative dataSet depth)
        (activityMajorant dataSet depth)

    shellToRawMajorant :
      shellEnergy dataSet depth
      ≤ (B * pow e depth) * (A * pow a depth)
    shellToRawMajorant =
      ℚP.≤-trans
        (shellEnergyBelowMultiplicityTimesActivity dataSet depth)
        productBound

    reorder :
      (B * pow e depth) * (A * pow a depth)
      ≡ (A * B) * (pow a depth * pow e depth)
    reorder = ℚRing.solve-∀ A B (pow a depth) (pow e depth)

    replacePower :
      (A * B) * (pow a depth * pow e depth)
      ≡ (A * B) * pow (a * e) depth
    replacePower =
      cong (λ tail → (A * B) * tail) (powProductExact a e depth)
  in
  subst
    (λ upper → shellEnergy dataSet depth ≤ upper)
    (trans reorder replacePower)
    shellToRawMajorant

rowBActivityEntropyProductAlgebraLevel : ProofLevel
rowBActivityEntropyProductAlgebraLevel = machineChecked

rowBActivityEntropyToGeometricShellLevel : ProofLevel
rowBActivityEntropyToGeometricShellLevel = machineChecked

-- Physical CMP116 seam.  Identify the actual differentiated marked polymer
-- activity and shell multiplicity on one common source-native analytic domain,
-- prove the two pointwise majorants, and prove the combined ratio is strictly
-- below one.  No additional Yang--Mills summation theorem is needed after that.
literalCMP116DifferentiatedActivityMajorantLevel : ProofLevel
literalCMP116DifferentiatedActivityMajorantLevel = conditional

literalCMP116ShellEntropyMajorantLevel : ProofLevel
literalCMP116ShellEntropyMajorantLevel = conditional

literalCMP116CombinedShellRatioStrictlyBelowOneLevel : ProofLevel
literalCMP116CombinedShellRatioStrictlyBelowOneLevel = conditional
