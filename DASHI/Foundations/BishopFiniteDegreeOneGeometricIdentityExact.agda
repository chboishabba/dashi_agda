module DASHI.Foundations.BishopFiniteDegreeOneGeometricIdentityExact where

------------------------------------------------------------------------
-- SHARP FINITE DEGREE-ONE GEOMETRIC IDENTITY
--
-- For a Bishop real q define
--
--   W_N(q) = sum_{v=1}^N v q^v.
--
-- Then, entirely finitely,
--
--   (1-q)^2 W_N(q)
--     ~= q - (N+1) q^(N+1) + N q^(N+2).
--
-- This is the algebraic core of the Erdos v q^v kernel.  It avoids formal
-- differentiation of an infinite geometric series and uses no convergence.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (0ℚᵘ; 1ℚᵘ; _/_)

import Real as BishopReal
import RealProperties as BishopP

import DASHI.Mathematics.NumberTheory.FiniteNatRationalEmbeddingExact as NatEmbed
open import DASHI.Physics.YangMills.CompactLieProofLevel

natReal : Nat → BishopReal.ℝ
natReal n = BishopReal._⋆ (NatEmbed.natAsRational n)

natRealSuccessor : ∀ n →
  BishopReal._≃_
    (natReal (suc n))
    (BishopReal._+_ (natReal n) BishopReal.1ℝ)
natRealSuccessor n =
  BishopP.≃-trans
    (BishopP.⋆-cong (NatEmbed.natAsRationalSuccessor n))
    (BishopP.≃-trans
      (BishopP.⋆-distrib-+
        (NatEmbed.natAsRational n)
        (+ 1 / 1))
      (BishopP.+-cong BishopP.≃-refl BishopP.≃-refl))

weightedPartial : BishopReal.ℝ → Nat → BishopReal.ℝ
weightedPartial q zero = BishopReal.0ℝ
weightedPartial q (suc count) =
  BishopReal._+_
    (weightedPartial q count)
    (BishopReal._*_
      (natReal (suc count))
      (BishopReal.pow q (suc count)))

oneMinus : BishopReal.ℝ → BishopReal.ℝ
oneMinus q = BishopReal._-_ BishopReal.1ℝ q

square : BishopReal.ℝ → BishopReal.ℝ
square x = BishopReal._*_ x x

finiteDegreeOneGeometricIdentity :
  (q : BishopReal.ℝ) →
  ∀ count →
  BishopReal._≃_
    (BishopReal._*_
      (square (oneMinus q))
      (weightedPartial q count))
    (BishopReal._+_
      (BishopReal._-_
        q
        (BishopReal._*_
          (natReal (suc count))
          (BishopReal.pow q (suc count))))
      (BishopReal._*_
        (natReal count)
        (BishopReal.pow q (suc (suc count)))))
finiteDegreeOneGeometricIdentity q zero =
  let open BishopP.ℝ-Solver
  in solve 1
    (λ q′ →
      ((Κ 1ℚᵘ ⊖ q′) ⊗ (Κ 1ℚᵘ ⊖ q′)) ⊗ Κ 0ℚᵘ
      ⊜ (q′ ⊖ (Κ 1ℚᵘ ⊗ q′)) ⊕ (Κ 0ℚᵘ ⊗ (q′ ⊗ q′)))
    BishopP.≃-refl q
finiteDegreeOneGeometricIdentity q (suc count) =
  let
    gap = oneMinus q
    old = weightedPartial q count
    coefficient = natReal (suc count)
    n = natReal count
    p = BishopReal.pow q (suc count)
    pq = BishopReal._*_ p q
    pqq = BishopReal._*_ pq q
    open BishopP.ℝ-Solver

    distributed :
      BishopReal._≃_
        (BishopReal._*_
          (square gap)
          (BishopReal._+_ old (BishopReal._*_ coefficient p)))
        (BishopReal._+_
          (BishopReal._*_ (square gap) old)
          (BishopReal._*_
            (square gap)
            (BishopReal._*_ coefficient p)))
    distributed =
      solve 4
        (λ g old′ c p′ →
          ((g ⊗ g) ⊗ (old′ ⊕ (c ⊗ p′)))
          ⊜ ((g ⊗ g) ⊗ old′) ⊕ ((g ⊗ g) ⊗ (c ⊗ p′)))
        BishopP.≃-refl gap old coefficient p

    afterIH :
      BishopReal._≃_
        (BishopReal._+_
          (BishopReal._*_ (square gap) old)
          (BishopReal._*_
            (square gap)
            (BishopReal._*_ coefficient p)))
        (BishopReal._+_
          (BishopReal._+_
            (BishopReal._-_
              q
              (BishopReal._*_ coefficient p))
            (BishopReal._*_ n pq))
          (BishopReal._*_
            (square gap)
            (BishopReal._*_ coefficient p)))
    afterIH =
      BishopP.+-cong
        (finiteDegreeOneGeometricIdentity q count)
        BishopP.≃-refl

    algebraBeforeCoefficientTransport :
      BishopReal._≃_
        (BishopReal._+_
          (BishopReal._+_
            (BishopReal._-_
              q
              (BishopReal._*_ coefficient p))
            (BishopReal._*_ n pq))
          (BishopReal._*_
            (square gap)
            (BishopReal._*_ coefficient p)))
        (BishopReal._+_
          (BishopReal._-_
            q
            (BishopReal._*_
              (BishopReal._+_ coefficient BishopReal.1ℝ)
              pq))
          (BishopReal._*_ coefficient pqq))
    algebraBeforeCoefficientTransport =
      solve 4
        (λ q′ n′ c p′ →
          ((q′ ⊖ (c ⊗ p′)) ⊕ (n′ ⊗ (p′ ⊗ q′)))
            ⊕ (((Κ 1ℚᵘ ⊖ q′) ⊗ (Κ 1ℚᵘ ⊖ q′)) ⊗ (c ⊗ p′))
          ⊜ (q′ ⊖ ((c ⊕ Κ 1ℚᵘ) ⊗ (p′ ⊗ q′)))
            ⊕ (c ⊗ ((p′ ⊗ q′) ⊗ q′)))
        BishopP.≃-refl q n coefficient p

    nextCoefficient :
      BishopReal._≃_
        (BishopReal._+_ coefficient BishopReal.1ℝ)
        (natReal (suc (suc count)))
    nextCoefficient =
      BishopP.≃-symm (natRealSuccessor (suc count))

    nextCoefficientProduct :
      BishopReal._≃_
        (BishopReal._*_
          (BishopReal._+_ coefficient BishopReal.1ℝ)
          pq)
        (BishopReal._*_
          (natReal (suc (suc count)))
          pq)
    nextCoefficientProduct = BishopP.*-congʳ nextCoefficient

    coefficientTransport :
      BishopReal._≃_
        (BishopReal._+_
          (BishopReal._-_
            q
            (BishopReal._*_
              (BishopReal._+_ coefficient BishopReal.1ℝ)
              pq))
          (BishopReal._*_ coefficient pqq))
        (BishopReal._+_
          (BishopReal._-_
            q
            (BishopReal._*_
              (natReal (suc (suc count)))
              pq))
          (BishopReal._*_ coefficient pqq))
    coefficientTransport =
      BishopP.+-congˡ
        (BishopReal._*_ coefficient pqq)
        (BishopP.+-congʳ q
          (BishopP.-‿cong nextCoefficientProduct))
  in
  BishopP.≃-trans distributed
    (BishopP.≃-trans afterIH
      (BishopP.≃-trans
        algebraBeforeCoefficientTransport
        coefficientTransport))

bishopFiniteDegreeOneGeometricIdentityLevel : ProofLevel
bishopFiniteDegreeOneGeometricIdentityLevel = machineChecked
