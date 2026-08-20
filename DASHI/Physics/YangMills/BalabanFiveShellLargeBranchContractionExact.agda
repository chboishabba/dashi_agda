module DASHI.Physics.YangMills.BalabanFiveShellLargeBranchContractionExact where

------------------------------------------------------------------------
-- ROUND81: SOURCE EXPONENTIAL DECAY -> LARGE-BRANCH < 1/2 WITHOUT FITTED q
--
-- PRIMARY SOURCES / CALIBRATION
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99(3) (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. II.
-- Cluster Expansions", Communications in Mathematical Physics 116 (1988),
-- 1--22. DOI: 10.1007/BF01239022.
--
-- WHY THIS REPLACES THE OLD 0.231781... TARGET
--
-- The older Sprint54 number q=0.23178189475262734 came from a diagnostic
-- floating-point row q = 8 exp(a-beta*c_min) with selected beta/a/c_min.
-- Its generating script explicitly did not certify all-diameter KP or the
-- Balaban RG transfer.  It is therefore the wrong physical theorem target.
--
-- The source-native target is much weaker and cleaner.  Once the positive
-- source localization exponent has been coarsened so that ONE coarse shell
-- costs at most 1/2, a five-shell separation supplies
--
--       8 * (1/2)^5 = 1/4 < 1/2.
--
-- Thus any factor-eight local branching/entropy multiplicity is absorbed by
-- five dyadic decay shells.  No fitted beta, c_min, or decimal q is needed.
--
-- This module proves only that exact arithmetic and monotone transport.  The
-- physical source-facing input remains the SAME-object bound saying that the
-- literal unified large-activity increment is controlled by the source
-- exponential shell majorant after five chosen coarse shells.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; suc; zero)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _*_; _≤_; _<_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact as KP

five : Nat
five = suc (suc (suc (suc (suc zero))))

factorEight oneQuarter oneHalf : ℚ
factorEight = + 8 / 1
oneQuarter = + 1 / 4
oneHalf = + 1 / 2

fiveDyadicShellsExact :
  factorEight * KP.halfPower five ≡ oneQuarter
fiveDyadicShellsExact = ℚRing.solve []

quarterBelowHalf : oneQuarter < oneHalf
quarterBelowHalf = ℚP.positive⁻¹ (oneHalf ℚ.- oneQuarter)

record FiveShellLargeActivityBound : Set where
  field
    actualLargeCost : ℚ
    actualLargeCostNonnegative : 0ℚ ≤ actualLargeCost
    sourceFiveShellBound :
      actualLargeCost ≤ factorEight * KP.halfPower five

open FiveShellLargeActivityBound public

fiveShellLargeCostBelowQuarter :
  (dataSet : FiveShellLargeActivityBound) →
  actualLargeCost dataSet ≤ oneQuarter
fiveShellLargeCostBelowQuarter dataSet =
  subst
    (λ upper → actualLargeCost dataSet ≤ upper)
    fiveDyadicShellsExact
    (sourceFiveShellBound dataSet)

fiveShellLargeCostStrictlyBelowHalf :
  (dataSet : FiveShellLargeActivityBound) →
  actualLargeCost dataSet < oneHalf
fiveShellLargeCostStrictlyBelowHalf dataSet =
  ℚP.≤-<-trans (fiveShellLargeCostBelowQuarter dataSet) quarterBelowHalf

fiveShellLargeBranchArithmeticLevel : ProofLevel
fiveShellLargeBranchArithmeticLevel = machineChecked

-- Physical seam: instantiate `sourceFiveShellBound` on the literal CMP119/122
-- large-activity coordinate using the CMP99(3)/CMP109/CMP116 positive
-- exponential localization/suppression estimate after choosing a coarse shell
-- width whose one-shell source decay is <= 1/2.
physicalSourceNativeFiveShellActivityBoundLevel : ProofLevel
physicalSourceNativeFiveShellActivityBoundLevel = conditional
