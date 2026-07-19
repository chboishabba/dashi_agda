module DASHI.Physics.YangMills.BalabanSU2ReducedAdjointGaugeCovariance where

------------------------------------------------------------------------
-- Gauge covariance of the concrete adjoint functional calculus.
--
-- For a general quaternion q, conjugation satisfies
--
--   [qYq*,qXq*] = |q|² q[Y,X]q*.
--
-- The unrestricted identity is proved below through explicit quaternion and
-- bracket polynomial syntax.  Only afterwards is q restricted to the SU(2)
-- unit-quaternion carrier, where the unit-norm witness removes the factor.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using
  ( cong; cong₂; sym; trans )

open import DASHI.Physics.YangMills.BalabanAxiomaticRealPolynomialSolver using
  ( module RealPolynomialSolver; zeroCoefficient )
open import DASHI.Physics.YangMills.BalabanComputedPolynomialSolver using
  ( solveComputed; computed )
open RealPolynomialSolver using
  ( Polynomial; con; _:=_; _:+_; _:*_; :-_ )
open import DASHI.Physics.YangMills.BalabanQuaternionPolynomialIdentities using
  ( q0R; q1R; q2R; q3R; q0P; q1P; q2P; q3P )
open import DASHI.Physics.YangMills.BalabanSU2QuaternionCarrier using
  ( Quaternion
  ; quat
  ; q0; q1; q2; q3
  ; _*q_
  ; conjugateQ
  ; q0Multiply; q1Multiply; q2Multiply; q3Multiply
  ; q0Conjugate; q1Conjugate; q2Conjugate; q3Conjugate
  ; _*R_
  ; -R_
  ; zeroR
  ; oneR
  ; *-identityˡ
  ; normSquaredQ
  ; su2q
  ; quaternion
  ; unitNormSquared
  )
open import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier using
  ( SU2LieAlgebra
  ; su2Lie
  ; su2LieExt
  ; lieAdd
  ; lieScale
  ; su2Adjoint
  ; su2AdjointAdd
  ; su2AdjointScale
  )
open import DASHI.Physics.YangMills.BalabanSU2AdjointInnerProduct using
  ( su2DotAdjointInvariant )
open import DASHI.Physics.YangMills.BalabanSU2LieBracket using
  ( lieBracket
  ; bracket1R; bracket2R; bracket3R
  ; bracket1P; bracket2P; bracket3P
  )
open import DASHI.Physics.YangMills.BalabanSU2AdjointCubicReduction using
  ( fourR
  ; adCubicCoefficient
  )
open import DASHI.Physics.YangMills.BalabanSU2ReducedAdjointCalculus using
  ( reducedAd
  ; applyReducedAdjoint
  )
open import DASHI.Physics.YangMills.BalabanSU2AdjointMatrixDeterminant using
  ( determinantMatrix3
  ; reducedAdjointMatrix
  ; reducedAdjointDeterminant
  )
open import DASHI.Physics.YangMills.BalabanSU2ReducedAdjointDeterminantProduct using
  ( reducedAdjointDeterminantValue )

zeroP : ∀ {n} → Polynomial n
zeroP = con zeroCoefficient

normSquaredP :
  ∀ {n} → Polynomial n → Polynomial n → Polynomial n → Polynomial n → Polynomial n
normSquaredP a₀ a₁ a₂ a₃ =
  (((a₀ :* a₀) :+ (a₁ :* a₁)) :+ (a₂ :* a₂)) :+ (a₃ :* a₃)

adjoint0R : ∀ a₀ a₁ a₂ a₃ x y z → _
adjoint0R a₀ a₁ a₂ a₃ x y z =
  q0R
    (q0R a₀ a₁ a₂ a₃ zeroR x y z)
    (q1R a₀ a₁ a₂ a₃ zeroR x y z)
    (q2R a₀ a₁ a₂ a₃ zeroR x y z)
    (q3R a₀ a₁ a₂ a₃ zeroR x y z)
    a₀ (-R a₁) (-R a₂) (-R a₃)

adjoint1R : ∀ a₀ a₁ a₂ a₃ x y z → _
adjoint1R a₀ a₁ a₂ a₃ x y z =
  q1R
    (q0R a₀ a₁ a₂ a₃ zeroR x y z)
    (q1R a₀ a₁ a₂ a₃ zeroR x y z)
    (q2R a₀ a₁ a₂ a₃ zeroR x y z)
    (q3R a₀ a₁ a₂ a₃ zeroR x y z)
    a₀ (-R a₁) (-R a₂) (-R a₃)

adjoint2R : ∀ a₀ a₁ a₂ a₃ x y z → _
adjoint2R a₀ a₁ a₂ a₃ x y z =
  q2R
    (q0R a₀ a₁ a₂ a₃ zeroR x y z)
    (q1R a₀ a₁ a₂ a₃ zeroR x y z)
    (q2R a₀ a₁ a₂ a₃ zeroR x y z)
    (q3R a₀ a₁ a₂ a₃ zeroR x y z)
    a₀ (-R a₁) (-R a₂) (-R a₃)

adjoint3R : ∀ a₀ a₁ a₂ a₃ x y z → _
adjoint3R a₀ a₁ a₂ a₃ x y z =
  q3R
    (q0R a₀ a₁ a₂ a₃ zeroR x y z)
    (q1R a₀ a₁ a₂ a₃ zeroR x y z)
    (q2R a₀ a₁ a₂ a₃ zeroR x y z)
    (q3R a₀ a₁ a₂ a₃ zeroR x y z)
    a₀ (-R a₁) (-R a₂) (-R a₃)

adjoint0P :
  ∀ {n} → Polynomial n → Polynomial n → Polynomial n → Polynomial n →
  Polynomial n → Polynomial n → Polynomial n → Polynomial n
adjoint0P a₀ a₁ a₂ a₃ x y z =
  q0P
    (q0P a₀ a₁ a₂ a₃ zeroP x y z)
    (q1P a₀ a₁ a₂ a₃ zeroP x y z)
    (q2P a₀ a₁ a₂ a₃ zeroP x y z)
    (q3P a₀ a₁ a₂ a₃ zeroP x y z)
    a₀ (:- a₁) (:- a₂) (:- a₃)

adjoint1P :
  ∀ {n} → Polynomial n → Polynomial n → Polynomial n → Polynomial n →
  Polynomial n → Polynomial n → Polynomial n → Polynomial n
adjoint1P a₀ a₁ a₂ a₃ x y z =
  q1P
    (q0P a₀ a₁ a₂ a₃ zeroP x y z)
    (q1P a₀ a₁ a₂ a₃ zeroP x y z)
    (q2P a₀ a₁ a₂ a₃ zeroP x y z)
    (q3P a₀ a₁ a₂ a₃ zeroP x y z)
    a₀ (:- a₁) (:- a₂) (:- a₃)

adjoint2P :
  ∀ {n} → Polynomial n → Polynomial n → Polynomial n → Polynomial n →
  Polynomial n → Polynomial n → Polynomial n → Polynomial n
adjoint2P a₀ a₁ a₂ a₃ x y z =
  q2P
    (q0P a₀ a₁ a₂ a₃ zeroP x y z)
    (q1P a₀ a₁ a₂ a₃ zeroP x y z)
    (q2P a₀ a₁ a₂ a₃ zeroP x y z)
    (q3P a₀ a₁ a₂ a₃ zeroP x y z)
    a₀ (:- a₁) (:- a₂) (:- a₃)

adjoint3P :
  ∀ {n} → Polynomial n → Polynomial n → Polynomial n → Polynomial n →
  Polynomial n → Polynomial n → Polynomial n → Polynomial n
adjoint3P a₀ a₁ a₂ a₃ x y z =
  q3P
    (q0P a₀ a₁ a₂ a₃ zeroP x y z)
    (q1P a₀ a₁ a₂ a₃ zeroP x y z)
    (q2P a₀ a₁ a₂ a₃ zeroP x y z)
    (q3P a₀ a₁ a₂ a₃ zeroP x y z)
    a₀ (:- a₁) (:- a₂) (:- a₃)

adjoint1Expanded :
  ∀ a₀ a₁ a₂ a₃ x y z →
  q1 (((quat a₀ a₁ a₂ a₃ *q quat zeroR x y z)
      *q conjugateQ (quat a₀ a₁ a₂ a₃)))
    ≡ adjoint1R a₀ a₁ a₂ a₃ x y z
adjoint1Expanded a₀ a₁ a₂ a₃ x y z
  rewrite q1Multiply
      (quat a₀ a₁ a₂ a₃ *q quat zeroR x y z)
      (conjugateQ (quat a₀ a₁ a₂ a₃))
    | q0Multiply (quat a₀ a₁ a₂ a₃) (quat zeroR x y z)
    | q1Multiply (quat a₀ a₁ a₂ a₃) (quat zeroR x y z)
    | q2Multiply (quat a₀ a₁ a₂ a₃) (quat zeroR x y z)
    | q3Multiply (quat a₀ a₁ a₂ a₃) (quat zeroR x y z)
    | q0Conjugate (quat a₀ a₁ a₂ a₃)
    | q1Conjugate (quat a₀ a₁ a₂ a₃)
    | q2Conjugate (quat a₀ a₁ a₂ a₃)
    | q3Conjugate (quat a₀ a₁ a₂ a₃) = refl

adjoint2Expanded :
  ∀ a₀ a₁ a₂ a₃ x y z →
  q2 (((quat a₀ a₁ a₂ a₃ *q quat zeroR x y z)
      *q conjugateQ (quat a₀ a₁ a₂ a₃)))
    ≡ adjoint2R a₀ a₁ a₂ a₃ x y z
adjoint2Expanded a₀ a₁ a₂ a₃ x y z
  rewrite q2Multiply
      (quat a₀ a₁ a₂ a₃ *q quat zeroR x y z)
      (conjugateQ (quat a₀ a₁ a₂ a₃))
    | q0Multiply (quat a₀ a₁ a₂ a₃) (quat zeroR x y z)
    | q1Multiply (quat a₀ a₁ a₂ a₃) (quat zeroR x y z)
    | q2Multiply (quat a₀ a₁ a₂ a₃) (quat zeroR x y z)
    | q3Multiply (quat a₀ a₁ a₂ a₃) (quat zeroR x y z)
    | q0Conjugate (quat a₀ a₁ a₂ a₃)
    | q1Conjugate (quat a₀ a₁ a₂ a₃)
    | q2Conjugate (quat a₀ a₁ a₂ a₃)
    | q3Conjugate (quat a₀ a₁ a₂ a₃) = refl

adjoint3Expanded :
  ∀ a₀ a₁ a₂ a₃ x y z →
  q3 (((quat a₀ a₁ a₂ a₃ *q quat zeroR x y z)
      *q conjugateQ (quat a₀ a₁ a₂ a₃)))
    ≡ adjoint3R a₀ a₁ a₂ a₃ x y z
adjoint3Expanded a₀ a₁ a₂ a₃ x y z
  rewrite q3Multiply
      (quat a₀ a₁ a₂ a₃ *q quat zeroR x y z)
      (conjugateQ (quat a₀ a₁ a₂ a₃))
    | q0Multiply (quat a₀ a₁ a₂ a₃) (quat zeroR x y z)
    | q1Multiply (quat a₀ a₁ a₂ a₃) (quat zeroR x y z)
    | q2Multiply (quat a₀ a₁ a₂ a₃) (quat zeroR x y z)
    | q3Multiply (quat a₀ a₁ a₂ a₃) (quat zeroR x y z)
    | q0Conjugate (quat a₀ a₁ a₂ a₃)
    | q1Conjugate (quat a₀ a₁ a₂ a₃)
    | q2Conjugate (quat a₀ a₁ a₂ a₃)
    | q3Conjugate (quat a₀ a₁ a₂ a₃) = refl

su2AdjointExpanded :
  ∀ a₀ a₁ a₂ a₃ unit x y z →
  su2Adjoint (su2q (quat a₀ a₁ a₂ a₃) unit) (su2Lie x y z)
  ≡ su2Lie
      (adjoint1R a₀ a₁ a₂ a₃ x y z)
      (adjoint2R a₀ a₁ a₂ a₃ x y z)
      (adjoint3R a₀ a₁ a₂ a₃ x y z)
su2AdjointExpanded a₀ a₁ a₂ a₃ unit x y z =
  su2LieExt
    (adjoint1Expanded a₀ a₁ a₂ a₃ x y z)
    (adjoint2Expanded a₀ a₁ a₂ a₃ x y z)
    (adjoint3Expanded a₀ a₁ a₂ a₃ x y z)

bracketAdjoint1Polynomial :
  ∀ a₀ a₁ a₂ a₃ y₁ y₂ y₃ x₁ x₂ x₃ →
  bracket1R
    (adjoint2R a₀ a₁ a₂ a₃ y₁ y₂ y₃)
    (adjoint3R a₀ a₁ a₂ a₃ y₁ y₂ y₃)
    (adjoint2R a₀ a₁ a₂ a₃ x₁ x₂ x₃)
    (adjoint3R a₀ a₁ a₂ a₃ x₁ x₂ x₃)
  ≡
  normSquaredQ (quat a₀ a₁ a₂ a₃) *R
    adjoint1R a₀ a₁ a₂ a₃
      (bracket1R y₂ y₃ x₂ x₃)
      (bracket2R y₃ y₁ x₃ x₁)
      (bracket3R y₁ y₂ x₁ x₂)
bracketAdjoint1Polynomial =
  solveComputed 10
    (λ a₀ a₁ a₂ a₃ y₁ y₂ y₃ x₁ x₂ x₃ →
      bracket1P
        (adjoint2P a₀ a₁ a₂ a₃ y₁ y₂ y₃)
        (adjoint3P a₀ a₁ a₂ a₃ y₁ y₂ y₃)
        (adjoint2P a₀ a₁ a₂ a₃ x₁ x₂ x₃)
        (adjoint3P a₀ a₁ a₂ a₃ x₁ x₂ x₃)
      :=
      normSquaredP a₀ a₁ a₂ a₃ :*
        adjoint1P a₀ a₁ a₂ a₃
          (bracket1P y₂ y₃ x₂ x₃)
          (bracket2P y₃ y₁ x₃ x₁)
          (bracket3P y₁ y₂ x₁ x₂))
    computed

bracketAdjoint2Polynomial :
  ∀ a₀ a₁ a₂ a₃ y₁ y₂ y₃ x₁ x₂ x₃ →
  bracket2R
    (adjoint3R a₀ a₁ a₂ a₃ y₁ y₂ y₃)
    (adjoint1R a₀ a₁ a₂ a₃ y₁ y₂ y₃)
    (adjoint3R a₀ a₁ a₂ a₃ x₁ x₂ x₃)
    (adjoint1R a₀ a₁ a₂ a₃ x₁ x₂ x₃)
  ≡
  normSquaredQ (quat a₀ a₁ a₂ a₃) *R
    adjoint2R a₀ a₁ a₂ a₃
      (bracket1R y₂ y₃ x₂ x₃)
      (bracket2R y₃ y₁ x₃ x₁)
      (bracket3R y₁ y₂ x₁ x₂)
bracketAdjoint2Polynomial =
  solveComputed 10
    (λ a₀ a₁ a₂ a₃ y₁ y₂ y₃ x₁ x₂ x₃ →
      bracket2P
        (adjoint3P a₀ a₁ a₂ a₃ y₁ y₂ y₃)
        (adjoint1P a₀ a₁ a₂ a₃ y₁ y₂ y₃)
        (adjoint3P a₀ a₁ a₂ a₃ x₁ x₂ x₃)
        (adjoint1P a₀ a₁ a₂ a₃ x₁ x₂ x₃)
      :=
      normSquaredP a₀ a₁ a₂ a₃ :*
        adjoint2P a₀ a₁ a₂ a₃
          (bracket1P y₂ y₃ x₂ x₃)
          (bracket2P y₃ y₁ x₃ x₁)
          (bracket3P y₁ y₂ x₁ x₂))
    computed

bracketAdjoint3Polynomial :
  ∀ a₀ a₁ a₂ a₃ y₁ y₂ y₃ x₁ x₂ x₃ →
  bracket3R
    (adjoint1R a₀ a₁ a₂ a₃ y₁ y₂ y₃)
    (adjoint2R a₀ a₁ a₂ a₃ y₁ y₂ y₃)
    (adjoint1R a₀ a₁ a₂ a₃ x₁ x₂ x₃)
    (adjoint2R a₀ a₁ a₂ a₃ x₁ x₂ x₃)
  ≡
  normSquaredQ (quat a₀ a₁ a₂ a₃) *R
    adjoint3R a₀ a₁ a₂ a₃
      (bracket1R y₂ y₃ x₂ x₃)
      (bracket2R y₃ y₁ x₃ x₁)
      (bracket3R y₁ y₂ x₁ x₂)
bracketAdjoint3Polynomial =
  solveComputed 10
    (λ a₀ a₁ a₂ a₃ y₁ y₂ y₃ x₁ x₂ x₃ →
      bracket3P
        (adjoint1P a₀ a₁ a₂ a₃ y₁ y₂ y₃)
        (adjoint2P a₀ a₁ a₂ a₃ y₁ y₂ y₃)
        (adjoint1P a₀ a₁ a₂ a₃ x₁ x₂ x₃)
        (adjoint2P a₀ a₁ a₂ a₃ x₁ x₂ x₃)
      :=
      normSquaredP a₀ a₁ a₂ a₃ :*
        adjoint3P a₀ a₁ a₂ a₃
          (bracket1P y₂ y₃ x₂ x₃)
          (bracket2P y₃ y₁ x₃ x₁)
          (bracket3P y₁ y₂ x₁ x₂))
    computed

lieScaleOne :
  ∀ X → lieScale oneR X ≡ X
lieScaleOne (su2Lie x y z) =
  su2LieExt
    (*-identityˡ x)
    (*-identityˡ y)
    (*-identityˡ z)

su2AdjointBracketNormFactor :
  ∀ u Y X →
  lieBracket (su2Adjoint u Y) (su2Adjoint u X)
  ≡
  lieScale
    (normSquaredQ (quaternion u))
    (su2Adjoint u (lieBracket Y X))
su2AdjointBracketNormFactor
  (su2q (quat a₀ a₁ a₂ a₃) unit)
  (su2Lie y₁ y₂ y₃)
  (su2Lie x₁ x₂ x₃)
  rewrite su2AdjointExpanded a₀ a₁ a₂ a₃ unit y₁ y₂ y₃
    | su2AdjointExpanded a₀ a₁ a₂ a₃ unit x₁ x₂ x₃
    | su2AdjointExpanded a₀ a₁ a₂ a₃ unit
        (bracket1R y₂ y₃ x₂ x₃)
        (bracket2R y₃ y₁ x₃ x₁)
        (bracket3R y₁ y₂ x₁ x₂) =
  su2LieExt
    (bracketAdjoint1Polynomial a₀ a₁ a₂ a₃ y₁ y₂ y₃ x₁ x₂ x₃)
    (bracketAdjoint2Polynomial a₀ a₁ a₂ a₃ y₁ y₂ y₃ x₁ x₂ x₃)
    (bracketAdjoint3Polynomial a₀ a₁ a₂ a₃ y₁ y₂ y₃ x₁ x₂ x₃)

su2AdjointBracketEquivariant :
  ∀ u Y X →
  su2Adjoint u (lieBracket Y X)
    ≡ lieBracket (su2Adjoint u Y) (su2Adjoint u X)
su2AdjointBracketEquivariant u Y X =
  trans
    (sym (lieScaleOne (su2Adjoint u (lieBracket Y X))))
    (trans
      (cong
        (λ scalar → lieScale scalar (su2Adjoint u (lieBracket Y X)))
        (sym (unitNormSquared u)))
      (sym (su2AdjointBracketNormFactor u Y X)))

su2AdjointAdSquaredEquivariant :
  ∀ u Y X →
  su2Adjoint u (lieBracket Y (lieBracket Y X))
  ≡
  lieBracket
    (su2Adjoint u Y)
    (lieBracket (su2Adjoint u Y) (su2Adjoint u X))
su2AdjointAdSquaredEquivariant u Y X =
  trans
    (su2AdjointBracketEquivariant u Y (lieBracket Y X))
    (cong
      (lieBracket (su2Adjoint u Y))
      (su2AdjointBracketEquivariant u Y X))

applyReducedAdjointGaugeCovariant :
  ∀ u Y operator X →
  su2Adjoint u (applyReducedAdjoint Y operator X)
  ≡
  applyReducedAdjoint
    (su2Adjoint u Y)
    operator
    (su2Adjoint u X)
applyReducedAdjointGaugeCovariant
  u Y (reducedAd a b c) X =
  trans
    (su2AdjointAdd u
      (lieScale a X)
      (lieAdd
        (lieScale b (lieBracket Y X))
        (lieScale c (lieBracket Y (lieBracket Y X)))))
    (cong₂ lieAdd
      (su2AdjointScale u a X)
      (trans
        (su2AdjointAdd u
          (lieScale b (lieBracket Y X))
          (lieScale c (lieBracket Y (lieBracket Y X))))
        (cong₂ lieAdd
          (trans
            (su2AdjointScale u b (lieBracket Y X))
            (cong (lieScale b)
              (su2AdjointBracketEquivariant u Y X)))
          (trans
            (su2AdjointScale u c
              (lieBracket Y (lieBracket Y X)))
            (cong (lieScale c)
              (su2AdjointAdSquaredEquivariant u Y X))))))

adCubicCoefficientGaugeInvariant :
  ∀ u Y →
  adCubicCoefficient (su2Adjoint u Y)
    ≡ adCubicCoefficient Y
adCubicCoefficientGaugeInvariant u Y =
  cong
    (λ norm → -R (fourR *R norm))
    (su2DotAdjointInvariant u Y Y)

reducedAdjointDeterminantGaugeInvariant :
  ∀ u Y operator →
  reducedAdjointDeterminantValue
    (su2Adjoint u Y) operator
  ≡ reducedAdjointDeterminantValue Y operator
reducedAdjointDeterminantGaugeInvariant
  u Y (reducedAd a b c)
  rewrite adCubicCoefficientGaugeInvariant u Y = refl

reducedAdjointMatrixDeterminantGaugeInvariant :
  ∀ u Y operator →
  determinantMatrix3
    (reducedAdjointMatrix (su2Adjoint u Y) operator)
  ≡
  determinantMatrix3
    (reducedAdjointMatrix Y operator)
reducedAdjointMatrixDeterminantGaugeInvariant
  u Y (reducedAd a b c) =
  trans
    (reducedAdjointDeterminant (su2Adjoint u Y) a b c)
    (trans
      (reducedAdjointDeterminantGaugeInvariant
        u Y (reducedAd a b c))
      (sym (reducedAdjointDeterminant Y a b c)))
