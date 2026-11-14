module DASHI.Moonshine.AbelBishopTetrationNaturalHeightExact where

------------------------------------------------------------------------
-- ACTUAL ORIGINAL BISHOP EXPONENTIAL: TETRATION AT NATURAL HEIGHTS
--
-- If a candidate F obeys F(0) ≈ 1 and F(suc n) ≈ exp_C(F(n))
-- on the original Bishop complex setoid, its values on the natural
-- heights necessarily coincide with the source's exact exponential tower.
--
-- This is a proved uniqueness law for FINITE INTEGER HEIGHTS.
-- It does not construct a holomorphic interpolation, a global Kneser
-- function or a certified contour integral.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
import DASHI.Analysis.BishopSetoidComplexExact as Complex
import DASHI.Moonshine.BishopRound11MachinSetoidComplexInstanceExact as Round11
import DASHI.Physics.YangMills.YangMillsSubmissionRound11ExactCutset as Cutset

originalBishopExponentialTower :
  Complex.BishopSetoidComplexTranscendentals →
  Nat → Complex.BishopComplex
originalBishopExponentialTower T zero = Complex.oneC
originalBishopExponentialTower T (suc n) =
  Complex.expC T (originalBishopExponentialTower T n)

record OriginalBishopTetrationNatLaw
    (T : Complex.BishopSetoidComplexTranscendentals)
    (candidate : Nat → Complex.BishopComplex) : Set where
  field
    normalizedAtZero :
      Complex._≈C_ (candidate zero) Complex.oneC

    originalSuccessorEquation :
      (n : Nat) →
      Complex._≈C_
        (candidate (suc n))
        (Complex.expC T (candidate n))

open OriginalBishopTetrationNatLaw public

originalBishopTetrationNaturalHeightUniqueness :
  (T : Complex.BishopSetoidComplexTranscendentals) →
  (candidate : Nat → Complex.BishopComplex) →
  OriginalBishopTetrationNatLaw T candidate →
  (n : Nat) →
  Complex._≈C_
    (candidate n)
    (originalBishopExponentialTower T n)
originalBishopTetrationNaturalHeightUniqueness T candidate law zero =
  normalizedAtZero law
originalBishopTetrationNaturalHeightUniqueness T candidate law (suc n) =
  Complex.≈C-trans
    (originalSuccessorEquation law n)
    (Complex.expCongruent T
      (originalBishopTetrationNaturalHeightUniqueness
        T candidate law n))

originalBishopExponentialTowerSatisfiesNatLaw :
  (T : Complex.BishopSetoidComplexTranscendentals) →
  OriginalBishopTetrationNatLaw T
    (originalBishopExponentialTower T)
originalBishopExponentialTowerSatisfiesNatLaw T =
  record
    { normalizedAtZero = Complex.≈C-refl Complex.oneC
    ; originalSuccessorEquation =
        λ n → Complex.≈C-refl
          (originalBishopExponentialTower T (suc n))
    }

originalBishopAnyTwoTetrationCandidatesAgreeOnNat :
  (T : Complex.BishopSetoidComplexTranscendentals) →
  (left right : Nat → Complex.BishopComplex) →
  OriginalBishopTetrationNatLaw T left →
  OriginalBishopTetrationNatLaw T right →
  (n : Nat) →
  Complex._≈C_ (left n) (right n)
originalBishopAnyTwoTetrationCandidatesAgreeOnNat T left right l r n =
  Complex.≈C-trans
    (originalBishopTetrationNaturalHeightUniqueness T left l n)
    (Complex.≈C-sym
      (originalBishopTetrationNaturalHeightUniqueness T right r n))

originalRound11ExponentialTower :
  Cutset.Round11BishopCutset →
  Nat → Complex.BishopComplex
originalRound11ExponentialTower inputs =
  originalBishopExponentialTower
    (Round11.round11MachinTranscendentals inputs)

originalRound11NaturalHeightUniqueness :
  (inputs : Cutset.Round11BishopCutset) →
  (candidate : Nat → Complex.BishopComplex) →
  OriginalBishopTetrationNatLaw
    (Round11.round11MachinTranscendentals inputs)
    candidate →
  (n : Nat) →
  Complex._≈C_
    (candidate n)
    (originalRound11ExponentialTower inputs n)
originalRound11NaturalHeightUniqueness inputs candidate law n =
  originalBishopTetrationNaturalHeightUniqueness
    (Round11.round11MachinTranscendentals inputs)
    candidate law n
