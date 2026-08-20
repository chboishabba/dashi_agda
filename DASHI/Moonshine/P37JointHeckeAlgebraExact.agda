module DASHI.Moonshine.P37JointHeckeAlgebraExact where

------------------------------------------------------------------------
-- SOURCE / CONTEXT
--
-- Builds on the source p=37 T2 matrix from SageMath and the source-forced T3/T5
-- systems from LMFDB newform eigencharacters in P37SourceForcedT3T5HeckeExact.
--
-- Primary Hecke context:
-- Toshitsune Miyake, "Modular Forms", Springer, 2006.
-- DOI: 10.1007/3-540-29593-3.
-- Fred Diamond and Jerry Shurman, "A First Course in Modular Forms", Springer,
-- 2005. DOI: 10.1007/978-0-387-27226-9.
--
-- DASHI CONTRIBUTION
--
-- Assemble the full three-generator coarse p=37 Hecke algebra by exact Nat
-- matrix multiplication.  T2,T3,T5 commute pairwise, their coprime products
-- are explicit, and the weight-two prime-square laws close with entrywise-Nat
-- residual matrices T4,T9,T25 and the TRUE identity:
--
--   T2^2 = T4  + 2I,
--   T3^2 = T9  + 3I,
--   T5^2 = T25 + 5I.
--
-- Thus even simultaneous positive T2/T3/T5 arithmetic plus the full coarse
-- prime-square algebra survives the non-Ogg p=37 control.  The Frobenius orbit
-- defect remains the first current separator.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

record NatMatrix3 : Set where
  constructor matrix3
  field
    m00 m01 m02
    m10 m11 m12
    m20 m21 m22 : Nat

open NatMatrix3 public

compose : NatMatrix3 → NatMatrix3 → NatMatrix3
compose A B = matrix3
  (m00 A * m00 B + m01 A * m10 B + m02 A * m20 B)
  (m00 A * m01 B + m01 A * m11 B + m02 A * m21 B)
  (m00 A * m02 B + m01 A * m12 B + m02 A * m22 B)
  (m10 A * m00 B + m11 A * m10 B + m12 A * m20 B)
  (m10 A * m01 B + m11 A * m11 B + m12 A * m21 B)
  (m10 A * m02 B + m11 A * m12 B + m12 A * m22 B)
  (m20 A * m00 B + m21 A * m10 B + m22 A * m20 B)
  (m20 A * m01 B + m21 A * m11 B + m22 A * m21 B)
  (m20 A * m02 B + m21 A * m12 B + m22 A * m22 B)

identity3 : NatMatrix3
identity3 = matrix3 1 0 0 0 1 0 0 0 1

addScaledIdentity : NatMatrix3 → Nat → NatMatrix3
addScaledIdentity A scale = matrix3
  (m00 A + scale) (m01 A) (m02 A)
  (m10 A) (m11 A + scale) (m12 A)
  (m20 A) (m21 A) (m22 A + scale)

B37_2 B37_3 B37_5 : NatMatrix3
B37_2 = matrix3 1 1 1 1 0 2 1 2 0
B37_3 = matrix3 2 1 1 1 0 3 1 3 0
B37_5 = matrix3 2 2 2 2 1 3 2 3 1

B37_4 B37_9 B37_25 : NatMatrix3
B37_4 = matrix3 1 3 3 3 3 1 3 1 3
B37_9 = matrix3 3 5 5 5 7 1 5 1 7
B37_25 = matrix3 7 12 12 12 9 10 12 10 9

B37_6 B37_10 B37_15 : NatMatrix3
B37_6 = matrix3 4 4 4 4 7 1 4 1 7
B37_10 = matrix3 6 6 6 6 8 4 6 4 8
B37_15 = matrix3 8 8 8 8 11 5 8 5 11

------------------------------------------------------------------------
-- Coprime products / commutation.
------------------------------------------------------------------------

B2B3IsB6 : compose B37_2 B37_3 ≡ B37_6
B2B3IsB6 = refl

B3B2IsB6 : compose B37_3 B37_2 ≡ B37_6
B3B2IsB6 = refl

B2B5IsB10 : compose B37_2 B37_5 ≡ B37_10
B2B5IsB10 = refl

B5B2IsB10 : compose B37_5 B37_2 ≡ B37_10
B5B2IsB10 = refl

B3B5IsB15 : compose B37_3 B37_5 ≡ B37_15
B3B5IsB15 = refl

B5B3IsB15 : compose B37_5 B37_3 ≡ B37_15
B5B3IsB15 = refl

B2B3Commute : compose B37_2 B37_3 ≡ compose B37_3 B37_2
B2B3Commute = refl

B2B5Commute : compose B37_2 B37_5 ≡ compose B37_5 B37_2
B2B5Commute = refl

B3B5Commute : compose B37_3 B37_5 ≡ compose B37_5 B37_3
B3B5Commute = refl

------------------------------------------------------------------------
-- Weight-two prime-square relations with true identity correction.
------------------------------------------------------------------------

B2SquareHecke : compose B37_2 B37_2 ≡ addScaledIdentity B37_4 2
B2SquareHecke = refl

B3SquareHecke : compose B37_3 B37_3 ≡ addScaledIdentity B37_9 3
B3SquareHecke = refl

B5SquareHecke : compose B37_5 B37_5 ≡ addScaledIdentity B37_25 5
B5SquareHecke = refl

------------------------------------------------------------------------
-- Row degrees of prime-square residuals are ell^2+ell+1.
------------------------------------------------------------------------

row0 : NatMatrix3 → Nat
row0 A = m00 A + m01 A + m02 A

row1 : NatMatrix3 → Nat
row1 A = m10 A + m11 A + m12 A

row2 : NatMatrix3 → Nat
row2 A = m20 A + m21 A + m22 A

B37_4RowsDegreeSeven :
  row0 B37_4 ≡ 7 × row1 B37_4 ≡ 7 × row2 B37_4 ≡ 7
B37_4RowsDegreeSeven = refl , refl , refl

B37_9RowsDegreeThirteen :
  row0 B37_9 ≡ 13 × row1 B37_9 ≡ 13 × row2 B37_9 ≡ 13
B37_9RowsDegreeThirteen = refl , refl , refl

B37_25RowsDegreeThirtyOne :
  row0 B37_25 ≡ 31 × row1 B37_25 ≡ 31 × row2 B37_25 ≡ 31
B37_25RowsDegreeThirtyOne = refl , refl , refl

record P37JointHeckeBoundary : Set where
  field
    simultaneousPrimeGeneratorsConstructed : Bool
    simultaneousPrimeGeneratorsConstructedIsTrue :
      simultaneousPrimeGeneratorsConstructed ≡ true

    pairwiseCoprimeCommutationConstructed : Bool
    pairwiseCoprimeCommutationConstructedIsTrue :
      pairwiseCoprimeCommutationConstructed ≡ true

    allThreePrimeSquareRelationsConstructed : Bool
    allThreePrimeSquareRelationsConstructedIsTrue :
      allThreePrimeSquareRelationsConstructed ≡ true

    primeSquareResidualMatricesEntrywiseNat : Bool
    primeSquareResidualMatricesEntrywiseNatIsTrue :
      primeSquareResidualMatricesEntrywiseNat ≡ true

    fullCoarseHeckeAlgebraPromotedToOggSelector : Bool
    fullCoarseHeckeAlgebraPromotedToOggSelectorIsFalse :
      fullCoarseHeckeAlgebraPromotedToOggSelector ≡ false

canonicalP37JointHeckeBoundary : P37JointHeckeBoundary
canonicalP37JointHeckeBoundary = record
  { simultaneousPrimeGeneratorsConstructed = true
  ; simultaneousPrimeGeneratorsConstructedIsTrue = refl
  ; pairwiseCoprimeCommutationConstructed = true
  ; pairwiseCoprimeCommutationConstructedIsTrue = refl
  ; allThreePrimeSquareRelationsConstructed = true
  ; allThreePrimeSquareRelationsConstructedIsTrue = refl
  ; primeSquareResidualMatricesEntrywiseNat = true
  ; primeSquareResidualMatricesEntrywiseNatIsTrue = refl
  ; fullCoarseHeckeAlgebraPromotedToOggSelector = false
  ; fullCoarseHeckeAlgebraPromotedToOggSelectorIsFalse = refl
  }
