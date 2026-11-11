module DASHI.Biology.Molecular.BH4RationalFiniteFubiniExact where

-- Finite Fubini for the SAME unnormalised rational setoid ℚᵘ as the
-- original BH4 rational 27×29 semidiscrete operator and Bishop embedding.
-- Source-independent proof algebra, not a second physical operator.
-- No postulates, floating arithmetic, measured rates, or classical limits.

open import DASHI.Core.Prelude
import Data.Vec.Base as V
import Data.Fin.Base as F
import Data.Rational.Unnormalised as Q
import Data.Rational.Unnormalised.Properties as QP
import NonReflectiveQ as QSolver

qFiniteSum : ∀ {n} → V.Vec Q.ℚᵘ n → Q.ℚᵘ
qFiniteSum V.[] = Q.0ℚᵘ
qFiniteSum (V._∷_ x xs) =
  Q._+_ x (qFiniteSum xs)

qFiniteSumCong :
  ∀ {n} (left right : V.Vec Q.ℚᵘ n) →
  ((i : F.Fin n) →
    Q._≃_ (V.lookup left i) (V.lookup right i)) →
  Q._≃_ (qFiniteSum left) (qFiniteSum right)
qFiniteSumCong V.[] V.[] same = QP.≃-refl
qFiniteSumCong (V._∷_ x xs) (V._∷_ y ys) same =
  QP.+-cong (same F.zero)
    (qFiniteSumCong xs ys (λ i → same (F.suc i)))

qShuffle : ∀ a b c d →
  Q._≃_ (Q._+_ (Q._+_ a b) (Q._+_ c d))
        (Q._+_ (Q._+_ a c) (Q._+_ b d))
qShuffle a b c d =
  let open QSolver in
  solve 4
    (λ a′ b′ c′ d′ →
      ((a′ ⊕ b′) ⊕ (c′ ⊕ d′))
      ⊜ ((a′ ⊕ c′) ⊕ (b′ ⊕ d′)))
    QP.≃-refl a b c d

qSumZipAdd :
  ∀ {n} (left right : V.Vec Q.ℚᵘ n) →
  Q._≃_
    (qFiniteSum (V.zipWith Q._+_ left right))
    (Q._+_ (qFiniteSum left) (qFiniteSum right))
qSumZipAdd V.[] V.[] =
  QP.≃-sym (QP.+-identityˡ Q.0ℚᵘ)
qSumZipAdd (V._∷_ a as) (V._∷_ b bs) =
  QP.≃-trans
    (QP.+-cong QP.≃-refl (qSumZipAdd as bs))
    (qShuffle a b (qFiniteSum as) (qFiniteSum bs))

qSumReplicateZero :
  ∀ n → Q._≃_ (qFiniteSum (V.replicate {n = n} Q.0ℚᵘ)) Q.0ℚᵘ
qSumReplicateZero zero = QP.≃-refl
qSumReplicateZero (suc n) =
  QP.≃-trans
    (QP.+-cong QP.≃-refl (qSumReplicateZero n))
    (QP.+-identityˡ Q.0ℚᵘ)

-- Fold all site rows columnwise using Q._+_. The Fubini theorem
-- is source independent; the original 27×29 instance specializes it.
qColumnTotals :
  ∀ {sites species} →
  V.Vec (V.Vec Q.ℚᵘ species) sites →
  V.Vec Q.ℚᵘ species
qColumnTotals {species = species} V.[] =
  V.replicate {n = species} Q.0ℚᵘ
qColumnTotals (V._∷_ row rows) =
  V.zipWith Q._+_ row (qColumnTotals rows)

qFiniteFubini :
  ∀ {sites species}
  (rows : V.Vec (V.Vec Q.ℚᵘ species) sites) →
  Q._≃_
    (qFiniteSum (V.map qFiniteSum rows))
    (qFiniteSum (qColumnTotals rows))
qFiniteFubini {sites = zero} {species = species} V.[] =
  QP.≃-sym (qSumReplicateZero species)
qFiniteFubini (V._∷_ row rows) =
  QP.≃-trans
    (QP.+-cong QP.≃-refl (qFiniteFubini rows))
    (QP.≃-sym (qSumZipAdd row (qColumnTotals rows)))

-- Concrete original physical accounting chart sizes.
original27x29RationalFubini :
  (rhs : V.Vec (V.Vec Q.ℚᵘ 29) 27) →
  Q._≃_
    (qFiniteSum (V.map qFiniteSum rhs))
    (qFiniteSum (qColumnTotals rhs))
original27x29RationalFubini = qFiniteFubini

------------------------------------------------------------------------
-- Weighted finite Fubini, in the *existing* BH4 weighted-row semantics.
-- This is the source-independent 27×29 change-of-summation lemma
-- needed by the original 783-coordinate RHS proof.
------------------------------------------------------------------------

import DASHI.Biology.Molecular.BH4RationalToBishopFiniteContinuityExact as Lift

qMulZero : (w : Q.ℚᵘ) → Q._≃_ (Q._*_ w Q.0ℚᵘ) Q.0ℚᵘ
qMulZero w =
  let open QSolver in
  solve 1 (λ w′ → (w′ ⊗ Κ Q.0ℚᵘ) ⊜ Κ Q.0ℚᵘ)
    QP.≃-refl w

qMulDistributes : (w x y : Q.ℚᵘ) →
  Q._≃_ (Q._*_ w (Q._+_ x y))
    (Q._+_ (Q._*_ w x) (Q._*_ w y))
qMulDistributes w x y =
  let open QSolver in
  solve 3
    (λ w′ x′ y′ →
      (w′ ⊗ (x′ ⊕ y′)) ⊜ ((w′ ⊗ x′) ⊕ (w′ ⊗ y′)))
    QP.≃-refl w x y

qWeightedRowAdd :
  ∀ {n}
  (weights left right : V.Vec Q.ℚᵘ n) →
  Q._≃_
    (Lift.sourceWeightedRow weights (V.zipWith Q._+_ left right))
    (Q._+_
      (Lift.sourceWeightedRow weights left)
      (Lift.sourceWeightedRow weights right))
qWeightedRowAdd V.[] V.[] V.[] =
  QP.≃-sym (QP.+-identityˡ Q.0ℚᵘ)
qWeightedRowAdd (V._∷_ w weights)
  (V._∷_ x left) (V._∷_ y right) =
  QP.≃-trans
    (QP.+-cong
      (qMulDistributes w x y)
      (qWeightedRowAdd weights left right))
    (qShuffle
      (Q._*_ w x) (Q._*_ w y)
      (Lift.sourceWeightedRow weights left)
      (Lift.sourceWeightedRow weights right))

qWeightedZeroRow :
  ∀ {n} (weights : V.Vec Q.ℚᵘ n) →
  Q._≃_
    (Lift.sourceWeightedRow weights (V.replicate {n = n} Q.0ℚᵘ))
    Q.0ℚᵘ
qWeightedZeroRow V.[] = QP.≃-refl
qWeightedZeroRow (V._∷_ w weights) =
  QP.≃-trans
    (QP.+-cong (qMulZero w) (qWeightedZeroRow weights))
    (QP.+-identityˡ Q.0ℚᵘ)

qWeightedFiniteFubini :
  ∀ {sites species}
  (weights : V.Vec Q.ℚᵘ species)
  (rhs : V.Vec (V.Vec Q.ℚᵘ species) sites) →
  Q._≃_
    (Lift.sourceSpatialWeighted weights rhs)
    (Lift.sourceWeightedRow weights (qColumnTotals rhs))
qWeightedFiniteFubini {species = species} weights V.[] =
  QP.≃-sym (qWeightedZeroRow weights)
qWeightedFiniteFubini weights (V._∷_ row rows) =
  QP.≃-trans
    (QP.+-cong QP.≃-refl
      (qWeightedFiniteFubini weights rows))
    (QP.≃-sym
      (qWeightedRowAdd weights row (qColumnTotals rows)))

-- This is a HIGHER-ALPHA computed-RHS consumer: it needs a source
-- proof that each actual per-species sum over 27 sites vanishes,
-- rather than six unrelated global weighted-zero assumptions.
-- In particular, it will consume a proved original incidence
-- cancellation theorem for the transport-only submatrix.
qWeightedDotCong :
  ∀ {n} (weights left right : V.Vec Q.ℚᵘ n) →
  ((species : F.Fin n) →
    Q._≃_ (V.lookup left species) (V.lookup right species)) →
  Q._≃_
    (Lift.sourceWeightedRow weights left)
    (Lift.sourceWeightedRow weights right)
qWeightedDotCong V.[] V.[] V.[] same = QP.≃-refl
qWeightedDotCong (V._∷_ w weights)
  (V._∷_ x left) (V._∷_ y right) same =
  QP.+-cong
    (QP.*-cong QP.≃-refl (same F.zero))
    (qWeightedDotCong weights left right
      (λ j → same (F.suc j)))

qWeightedColumnZeroImpliesSpatialZero :
  ∀ {sites species}
  (weights : V.Vec Q.ℚᵘ species)
  (rhs : V.Vec (V.Vec Q.ℚᵘ species) sites) →
  ((species : F.Fin species) →
    Q._≃_ (V.lookup (qColumnTotals rhs) species) Q.0ℚᵘ) →
  Q._≃_ (Lift.sourceSpatialWeighted weights rhs) Q.0ℚᵘ
qWeightedColumnZeroImpliesSpatialZero
  {species = species} weights rhs columnsZero =
  QP.≃-trans
    (qWeightedFiniteFubini weights rhs)
    (QP.≃-trans
      (qWeightedDotCong
        weights (qColumnTotals rhs)
        (V.replicate {n = species} Q.0ℚᵘ)
        columnsZero)
      (qWeightedZeroRow weights))

original27x29WeightedFubini :
  (weights : V.Vec Q.ℚᵘ 29)
  (rhs : V.Vec (V.Vec Q.ℚᵘ 29) 27) →
  Q._≃_
    (Lift.sourceSpatialWeighted weights rhs)
    (Lift.sourceWeightedRow weights (qColumnTotals rhs))
original27x29WeightedFubini = qWeightedFiniteFubini
