module DASHI.Physics.YangMills.BalabanPath13NormalizedAxisAverageExact where

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
-- DASHI CONTRIBUTION
--
-- Instantiate the arbitrary-side normalized conditional-expectation calculus
-- at the minimal source-admissible CMP109 side L=13.  The sole normalization
-- obligation is checked exactly over the literal 13-element cyclic carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Integer.Base using (+_)
open import Data.List.Base using (length)
open import Data.Rational using (ℚ; 1ℚ; _*_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact
open import DASHI.Physics.YangMills.BalabanFourDimensionalHaloOverlapExact using
  (lengthAllCyclicIndices)
import DASHI.Physics.YangMills.BalabanNormalizedAxisAverageExact as Average

side13 : Nat
side13 = 13

oneThirteenth : ℚ
oneThirteenth = + 1 / 13

side13NormalizationExact :
  oneThirteenth * natAsRational (length (allCyclicIndices side13)) ≡ 1ℚ
side13NormalizationExact
  rewrite lengthAllCyclicIndices side13 = ℚRing.solve []

side13AverageData : Average.NormalizedAxisAverageData side13
side13AverageData = record
  { Average.NormalizedAxisAverageData.weight = oneThirteenth
  ; Average.NormalizedAxisAverageData.normalized = side13NormalizationExact
  }

path13NormalizedAxisAverageLevel : ProofLevel
path13NormalizedAxisAverageLevel = machineChecked
