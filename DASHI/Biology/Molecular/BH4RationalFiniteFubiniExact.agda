module DASHI.Biology.Molecular.BH4RationalFiniteFubiniExact where

-- Finite Fubini for the SAME unnormalised rational setoid ℚᵘ as the
-- original BH4 rational 27×29 semidiscrete operator and Bishop embedding.
-- Source-independent proof algebra, not a second physical operator.
-- No postulates, floating arithmetic, measured rates, or classical limits.

open import DASHI.Core.Prelude
import Data.Vec.Base as V
import Data.Rational.Unnormalised as Q
import Data.Rational.Unnormalised.Properties as QP
import NonReflectiveQ as QSolver

qFiniteSum : ∀ {n} → V.Vec Q.ℚᵘ n → Q.ℚᵘ
qFiniteSum V.[] = Q.0ℚᵘ
qFiniteSum (V._∷_ x xs) =
  Q._+_ x (qFiniteSum xs)

qFiniteSumCong :
  ∀ {n} (left right : V.Vec Q.ℚᵘ n) →
  ((i : Data.Fin.Base.Fin n) →
    Q._≃_ (V.lookup left i) (V.lookup right i)) →
  Q._≃_ (qFiniteSum left) (qFiniteSum right)
qFiniteSumCong V.[] V.[] same = QP.≃-refl
qFiniteSumCong (V._∷_ x xs) (V._∷_ y ys) same =
  QP.+-cong (same Data.Fin.Base.zero)
    (qFiniteSumCong xs ys (λ i → same (Data.Fin.Base.suc i)))

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
