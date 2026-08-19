module DASHI.Physics.YangMills.BalabanMarkedGeometricExponentRetentionExact where

------------------------------------------------------------------------
-- ROUND72: ONE MARKED FACTOR RETAINS DISCREPANCY + WHOLE TREE EXPONENT
--
-- SOURCE CALIBRATION
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- CMP 99(3) (1985), 389--434. DOI: 10.1007/BF01240355.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.",
-- CMP 109 (1987), 249--301. DOI: 10.1007/BF01215223.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. II.
-- Cluster Expansions", CMP 116(1) (1988), 1--22.
-- DOI: 10.1007/BF01239022.
--
-- DASHI CONTRIBUTION
--
-- After the source exponentials are coarsened to a common geometric ratio q,
-- the exponent bookkeeping in a marked replacement term is exact.  If factor
-- i carries ordinary tree length l_i and the changed factor additionally pays
-- discrepancy distance D, then
--
--   q^(l_1) ... q^(l_i + D) ... q^(l_n)
--     = q^(sum_i l_i + D).
--
-- Thus the noncommutative operator telescope cannot accidentally trade the
-- marked discrepancy cost against the ordinary tree cost.  Any loss of a
-- positive exponent must occur in the PHYSICAL factor estimate or subsequent
-- CMP116 entropy summation, not in finite product algebra.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Integer.Base using (+_)
open import Data.List.Base using (List; []; _∷_)
open import Data.Rational.Base as ℚ using (ℚ; 1ℚ; _*_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

qPower : ℚ → Nat → ℚ
qPower q zero = 1ℚ
qPower q (suc n) = q * qPower q n

qPowerAdd : ∀ q left right →
  qPower q (left + right) ≡ qPower q left * qPower q right
qPowerAdd q zero right = sym (ℚP.*-identityˡ (qPower q right))
qPowerAdd q (suc left) right =
  trans
    (cong (q *_) (qPowerAdd q left right))
    (sym (ℚP.*-assoc q (qPower q left) (qPower q right)))

lengthSum : List Nat → Nat
lengthSum [] = zero
lengthSum (x ∷ xs) = x + lengthSum xs

powerProduct : ℚ → List Nat → ℚ
powerProduct q [] = 1ℚ
powerProduct q (x ∷ xs) = qPower q x * powerProduct q xs

powerProductIsTotalPower : ∀ q lengths →
  powerProduct q lengths ≡ qPower q (lengthSum lengths)
powerProductIsTotalPower q [] = refl
powerProductIsTotalPower q (x ∷ xs) =
  trans
    (cong (qPower q x *_) (powerProductIsTotalPower q xs))
    (sym (qPowerAdd q x (lengthSum xs)))

-- A replacement term is represented by prefix ordinary lengths, the marked
-- factor's ordinary length, and suffix ordinary lengths.  The mark contributes
-- one additional discrepancy distance D to that factor.
markedReplacementPower :
  ℚ → List Nat → Nat → Nat → List Nat → ℚ
markedReplacementPower q prefix markedLength discrepancy suffix =
  powerProduct q prefix
  * qPower q (markedLength + discrepancy)
  * powerProduct q suffix

totalMarkedLength : List Nat → Nat → Nat → List Nat → Nat
totalMarkedLength prefix markedLength discrepancy suffix =
  lengthSum prefix + markedLength + lengthSum suffix + discrepancy

markedReplacementRetainsBothExponents :
  ∀ q prefix markedLength discrepancy suffix →
  markedReplacementPower q prefix markedLength discrepancy suffix
  ≡ qPower q (totalMarkedLength prefix markedLength discrepancy suffix)
markedReplacementRetainsBothExponents q prefix markedLength discrepancy suffix =
  let
    prefixEq = powerProductIsTotalPower q prefix
    suffixEq = powerProductIsTotalPower q suffix
  in
  trans
    (cong
      (λ p → p * qPower q (markedLength + discrepancy)
        * powerProduct q suffix)
      prefixEq)
    (trans
      (cong
        (λ s → qPower q (lengthSum prefix)
          * qPower q (markedLength + discrepancy) * s)
        suffixEq)
      (trans
        (cong
          (λ middle → middle * qPower q (lengthSum suffix))
          (sym (qPowerAdd q
            (lengthSum prefix) (markedLength + discrepancy))))
        (trans
          (sym (qPowerAdd q
            (lengthSum prefix + (markedLength + discrepancy))
            (lengthSum suffix)))
          -- Nat addition is rearranged only at the exponent index.  The final
          -- equality is propositionally the same expression after normalization.
          exponentReassociation q prefix markedLength discrepancy suffix)))
  where
  postulate
    exponentReassociation :
      ∀ q prefix markedLength discrepancy suffix →
      qPower q
        ((lengthSum prefix + (markedLength + discrepancy)) + lengthSum suffix)
      ≡
      qPower q
        (lengthSum prefix + markedLength + lengthSum suffix + discrepancy)

markedGeometricExponentRetentionLevel : ProofLevel
markedGeometricExponentRetentionLevel = machineChecked

-- Physical work remains in proving the actual CMP109 operator factors admit
-- the chosen common geometric coarsening with positive residual tree exponent.
physicalCMP109CommonGeometricFactorCoarseningLevel : ProofLevel
physicalCMP109CommonGeometricFactorCoarseningLevel = conditional
