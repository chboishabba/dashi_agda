module DASHI.Physics.YangMills.YMClayOriginalRationalSU2BishopUnitaryWeldExact where

------------------------------------------------------------------------
-- ORIGINAL RATIONAL UNIT QUATERNION -> ACTUAL BISHOP SU2 UNIT MATRIX.
--
-- Unlike a new chosen "norm-one" carrier, this constructs the norm-one
-- witness by transporting the existing ORIGINAL RationalUnitQuaternion
-- norm equation across stdlib toℚᵘ and vendor Bishop._⋆ exact ring
-- homomorphisms. Thus determinant/adjoint/unitarity results apply to
-- literal original rational SU2 source objects.
--
-- No assertion of surjectivity onto Bishop S3, full original SUN
-- matrix-carrier equality, Haar or continuum YM.
--
-- Attribution: original DASHI Balaban rational SU2 and rational
-- normalization sources; Agda stdlib rational homomorphism; Bishop,
-- Murray/Csimma; previous Bishop SU2 quaternion matrix owners.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (subst; sym)
import Data.Rational.Base as ℚ
import Data.Rational.Properties as ℚP
import Real as B
import RealProperties as BP

import DASHI.Physics.YangMills.BalabanSU2RationalWilsonLargeFieldGapExact
  as Original
import DASHI.Physics.Closure.NSTriadKNMurrayBishopDirectCanonicalCarrier
  as Cast
import DASHI.Physics.YangMills.YMClayOriginalRationalSU2ToBishopTraceExact
  as TraceMap
import DASHI.Physics.YangMills.YMClayBishopSU2DeterminantExact as D
import DASHI.Physics.YangMills.YMClayBishopSU2UnitarityExact as U
import DASHI.Physics.YangMills.YMClayBishopSU2QuaternionTraceWeldExact
  as Q
import DASHI.Analysis.BishopSetoidComplexExact as C
import Data.Fin.Base as Fin

embed : ℚ.ℚ → B.ℝ
embed = TraceMap.rationalCoordinateToBishop

embedSum : ∀ x y →
  B._≃_ (embed (ℚ._+_ x y)) (B._+_ (embed x) (embed y))
embedSum = Cast.bishopEmbedAdd

embedProd : ∀ x y →
  B._≃_ (embed (ℚ._*_ x y)) (B._*_ (embed x) (embed y))
embedProd x y =
  BP.≃-trans
    (BP.⋆-cong (ℚP.toℚᵘ-homo-* x y))
    (BP.⋆-distrib-*
      (ℚ.toℚᵘ x) (ℚ.toℚᵘ y))

embedFourSum :
  ∀ a b c d →
  B._≃_
    (embed (ℚ._+_ (ℚ._+_ (ℚ._+_ a b) c) d))
    (B._+_
      (B._+_
        (B._+_ (embed a) (embed b))
        (embed c))
      (embed d))
embedFourSum a b c d =
  BP.≃-trans
    (embedSum (ℚ._+_ (ℚ._+_ a b) c) d)
    (BP.+-cong
      (BP.≃-trans
        (embedSum (ℚ._+_ a b) c)
        (BP.+-cong
          (embedSum a b)
          BP.≃-refl))
      BP.≃-refl)

originalNormPreserved :
  ∀ q →
  B._≃_
    (D.normSq (TraceMap.originalRationalQuaternionAsBishop q))
    (embed (Original.quaternionNormSq q))
originalNormPreserved q =
  let
    a = Original.realPart q
    b = Original.imagI q
    c = Original.imagJ q
    d = Original.imagK q

    pa = Original.squareℚ a
    pb = Original.squareℚ b
    pc = Original.squareℚ c
    pd = Original.squareℚ d

    squares :
      B._≃_
        (D.normSq (TraceMap.originalRationalQuaternionAsBishop q))
        (B._+_
          (embed pa)
          (B._+_ (embed pb) (B._+_ (embed pc) (embed pd))))
    squares =
      BP.+-cong
        (BP.≃-symm (embedProd a a))
        (BP.+-cong
          (BP.≃-symm (embedProd b b))
          (BP.+-cong
            (BP.≃-symm (embedProd c c))
            (BP.≃-symm (embedProd d d))))

    reassociate :
      B._≃_
        (B._+_ (embed pa)
          (B._+_ (embed pb) (B._+_ (embed pc) (embed pd))))
        (B._+_ (B._+_ (B._+_ (embed pa) (embed pb))
          (embed pc)) (embed pd))
    reassociate =
      let open BP.ℝ-Solver in
      solve 4
        (λ a b c d →
          (a ⊕ (b ⊕ (c ⊕ d)))
          ⊜ (((a ⊕ b) ⊕ c) ⊕ d))
        BP.≃-refl
        (embed pa) (embed pb) (embed pc) (embed pd)
  in
  BP.≃-trans squares
    (BP.≃-trans reassociate
      (BP.≃-symm (embedFourSum pa pb pc pd)))

originalNormOneAsBishop :
  ∀ q →
  B._≃_
    (D.normSq (TraceMap.originalRationalQuaternionAsBishop q))
    B.1ℝ
originalNormOneAsBishop q =
  BP.≃-trans
    (originalNormPreserved q)
    (subst
      (λ x → B._≃_ (embed x) B.1ℝ)
      (sym (Original.quaternionNormMatchesUnit q))
      BP.≃-refl)

originalRationalSU2AsBishopUnit :
  Original.RationalUnitQuaternion → D.UnitQuaternion
originalRationalSU2AsBishopUnit q =
  D.unitQuaternion
    (TraceMap.originalRationalQuaternionAsBishop q)
    (originalNormOneAsBishop q)

originalRationalSU2DeterminantOne :
  ∀ q →
  C._≈C_
    (D.quaternionDeterminantExplicit
      (TraceMap.originalRationalQuaternionAsBishop q))
    C.oneC
originalRationalSU2DeterminantOne q =
  D.unitQuaternionDeterminantOne
    (originalRationalSU2AsBishopUnit q)

originalRationalSU2BishopUnitarity :
  ∀ q (i j : Fin.Fin 2) →
  C._≈C_
    (U.gram (TraceMap.originalRationalQuaternionAsBishop q) i j)
    (U.unit2 i j)
originalRationalSU2BishopUnitarity q =
  U.bishopQuaternionUdaggerUIsIdentity
    (originalRationalSU2AsBishopUnit q)
