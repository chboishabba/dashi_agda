module DASHI.Mathematics.Algebra.RationalOctonionG2DerivationExact where

------------------------------------------------------------------------
-- RATIONAL OCTONION G2 DERIVATION / AUTOMORPHISM MAX-CUT
--
-- Literal operators for the standard alternative-algebra derivations
--
--   D(a,b) = [L_a,L_b] + [L_a,R_b] + [R_a,R_b]
--
-- plus two explicit signed imaginary-basis maps.  Companion exact Python
-- (`scripts/rational_albert_g2_f4_probe.py`) verifies, in the repository's
-- Cayley--Dickson convention:
--
-- * 1344 signed basis automorphisms of the seven imaginary units;
-- * the explicit maps below have orders 7 and 4 and generate all 1344;
-- * all 21 D(e_i,e_j), i<j, satisfy the derivation law on all 8x8 basis
--   products;
-- * the matrix span of those 21 derivations has rank 14.
--
-- The executable finite results are retained as cross-tool receipts rather
-- than silently promoted to Agda kernel authority.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; -_)

import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Q
import DASHI.Mathematics.Algebra.CayleyDicksonRationalOctonionExact as O

subO : O.RationalOctonion → O.RationalOctonion → O.RationalOctonion
subO x y = O._+o_ x (O.negO y)

leftMul rightMul : O.RationalOctonion → O.RationalOctonion → O.RationalOctonion
leftMul a x = O._*o_ a x
rightMul a x = O._*o_ x a

commLL commLR commRR :
  O.RationalOctonion → O.RationalOctonion → O.RationalOctonion → O.RationalOctonion
commLL a b x = subO (leftMul a (leftMul b x)) (leftMul b (leftMul a x))
commLR a b x = subO (leftMul a (rightMul b x)) (rightMul b (leftMul a x))
commRR a b x = subO (rightMul a (rightMul b x)) (rightMul b (rightMul a x))

D : O.RationalOctonion → O.RationalOctonion → O.RationalOctonion → O.RationalOctonion
D a b x = O._+o_ (O._+o_ (commLL a b x) (commLR a b x)) (commRR a b x)

DerivationLaw : (O.RationalOctonion → O.RationalOctonion) → Set
DerivationLaw deriv =
  (x y : O.RationalOctonion) →
    deriv (O._*o_ x y) ≡
      O._+o_ (O._*o_ (deriv x) y) (O._*o_ x (deriv y))

------------------------------------------------------------------------
-- Complete imaginary basis in the repository coordinate convention.
------------------------------------------------------------------------

e3 e5 e6 : O.RationalOctonion
e3 = O.oct (Q.quat 0ℚ 0ℚ 0ℚ 1ℚ) Q.zeroQ
e5 = O.oct Q.zeroQ (Q.quat 0ℚ 1ℚ 0ℚ 0ℚ)
e6 = O.oct Q.zeroQ (Q.quat 0ℚ 0ℚ 1ℚ 0ℚ)

------------------------------------------------------------------------
-- Explicit signed-basis automorphism candidates.
--
-- g7:
-- e1->e2, e2->e4, e3->e6, e4->e3, e5->e1,
-- e6->-e7, e7->-e5.
--
-- g4:
-- e1->e1, e2->e2, e3->e3, e4->e5, e5->-e4,
-- e6->e7, e7->-e6.
------------------------------------------------------------------------

g7 : O.RationalOctonion → O.RationalOctonion
g7 (O.oct (Q.quat a0 a1 a2 a3) (Q.quat b0 b1 b2 b3)) =
  O.oct
    (Q.quat a0 b1 a1 b0)
    (Q.quat a2 (- b3) a3 (- b2))

g4 : O.RationalOctonion → O.RationalOctonion
g4 (O.oct (Q.quat a0 a1 a2 a3) (Q.quat b0 b1 b2 b3)) =
  O.oct
    (Q.quat a0 a1 a2 a3)
    (Q.quat (- b1) b0 (- b3) b2)

OctonionAutomorphism : (O.RationalOctonion → O.RationalOctonion) → Set
OctonionAutomorphism f =
  (x y : O.RationalOctonion) →
    f (O._*o_ x y) ≡ O._*o_ (f x) (f y)

record G2ExactProbeReceipt : Set where
  constructor g2-exact-probe-receipt
  field
    signedBasisAutomorphismCount : Nat
    generator7Order : Nat
    generator4Order : Nat
    generatedSignedBasisGroupOrder : Nat
    standardDerivationCandidates : Nat
    derivationSpanRank : Nat
    allBasisDerivationChecksPassed : Bool
open G2ExactProbeReceipt public

canonicalG2ExactProbeReceipt : G2ExactProbeReceipt
canonicalG2ExactProbeReceipt =
  g2-exact-probe-receipt 1344 7 4 1344 21 14 true

record G2PromotionBoundary : Set where
  constructor g2-promotion-boundary
  field
    literalStandardDerivationOperatorPaid : Bool
    explicitOrder7SignedBasisMapPaid : Bool
    explicitOrder4SignedBasisMapPaid : Bool
    exactBasisAutomorphismSearchPassed : Bool
    exactSignedBasisClosure1344Passed : Bool
    exactTwentyOneDerivationBasisChecksPassed : Bool
    exactDerivationSpanRank14Passed : Bool
    agdaArbitraryRationalDerivationLawPaid : Bool
    agdaFullG2AlgebraicGroupRecognitionPaid : Bool
open G2PromotionBoundary public

currentG2PromotionBoundary : G2PromotionBoundary
currentG2PromotionBoundary =
  g2-promotion-boundary
    true true true true true true true
    false false
