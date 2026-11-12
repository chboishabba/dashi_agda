module DASHI.Biology.Molecular.BH4RationalSemidiscreteBilinearityExact where

-- Exact finite rational bilinearity for the original 27 x 29 RHS.
-- Source mathematics: ordinary finite vector sums over the original
-- DASHI BH4/369 arithmetic chart. No alternate geometry/chemistry.
-- Rational proof equality is setoid equality, not raw representative
-- identity in unnormalised fractions.
--
-- This is the missing additive-splitting leaf toward the actual
-- incidence/stoichiometry finite Fubini proof. It does NOT assert
-- that a globally summed native divergence vanishes merely because
-- its input arrays have the right dimensions.

open import DASHI.Core.Prelude
import Data.Vec.Base as V
import Data.Rational.Unnormalised as Q
import Data.Rational.Unnormalised.Properties as QP
import NonReflectiveQ as Solver
import DASHI.Biology.Molecular.BH4RationalToBishopFiniteContinuityExact as Lift
import DASHI.Biology.Molecular.BH4OriginalRationalSemidiscreteOperatorExact as Operator

-- Addition of two identically indexed vector coordinates; no float.
rationalZipAdd :
  ∀ {n} →
  V.Vec Q.ℚᵘ n → V.Vec Q.ℚᵘ n → V.Vec Q.ℚᵘ n
rationalZipAdd V.[] V.[] = V.[]
rationalZipAdd (V._∷_ a as) (V._∷_ b bs) =
  V._∷_ (Q._+_ a b) (rationalZipAdd as bs)

rationalWeightedAdditive :
  ∀ {n}
  (weights a b : V.Vec Q.ℚᵘ n) →
  Q._≃_
    (Lift.sourceWeightedRow weights (rationalZipAdd a b))
    (Q._+_ (Lift.sourceWeightedRow weights a)
           (Lift.sourceWeightedRow weights b))
rationalWeightedAdditive V.[] V.[] V.[] =
  let open Solver in
  solve 0
    (λ → Κ Q.0ℚᵘ ⊜ Κ Q.0ℚᵘ ⊕ Κ Q.0ℚᵘ)
    QP.≃-refl
rationalWeightedAdditive
  (V._∷_ w ws) (V._∷_ a as) (V._∷_ b bs) =
  QP.≃-trans
    (QP.+-cong
      QP.≃-refl
      (rationalWeightedAdditive ws as bs))
    (let open Solver in
     solve 5
       (λ w′ a′ b′ restA restB →
         (w′ ⊗ (a′ ⊕ b′)) ⊕ (restA ⊕ restB)
           ⊜ ((w′ ⊗ a′) ⊕ restA)
             ⊕ ((w′ ⊗ b′) ⊕ restB))
       QP.≃-refl w a b
       (Lift.sourceWeightedRow ws as)
       (Lift.sourceWeightedRow ws bs))

-- Row-by-row 27-site addition, matching Operator.Matrix 27 29.
rationalSpatialZipAdd :
  ∀ {sites species} →
  V.Vec (V.Vec Q.ℚᵘ species) sites →
  V.Vec (V.Vec Q.ℚᵘ species) sites →
  V.Vec (V.Vec Q.ℚᵘ species) sites
rationalSpatialZipAdd V.[] V.[] = V.[]
rationalSpatialZipAdd (V._∷_ row rows) (V._∷_ other others) =
  V._∷_ (rationalZipAdd row other)
          (rationalSpatialZipAdd rows others)

original369SpatialWeightedAdditive :
  ∀ {sites}
  (weights : V.Vec Q.ℚᵘ 29)
  (a b : V.Vec (V.Vec Q.ℚᵘ 29) sites) →
  Q._≃_
    (Lift.sourceSpatialWeighted
      weights (rationalSpatialZipAdd a b))
    (Q._+_
      (Lift.sourceSpatialWeighted weights a)
      (Lift.sourceSpatialWeighted weights b))
original369SpatialWeightedAdditive weights V.[] V.[] =
  let open Solver in
  solve 0
    (λ → Κ Q.0ℚᵘ ⊜ Κ Q.0ℚᵘ ⊕ Κ Q.0ℚᵘ)
    QP.≃-refl
original369SpatialWeightedAdditive weights
  (V._∷_ a as) (V._∷_ b bs) =
  QP.≃-trans
    (QP.+-cong
      (rationalWeightedAdditive weights a b)
      (original369SpatialWeightedAdditive weights as bs))
    (let open Solver in
     solve 4
       (λ rowA rowB restA restB →
         (rowA ⊕ rowB) ⊕ (restA ⊕ restB)
         ⊜ (rowA ⊕ restA) ⊕ (rowB ⊕ restB))
       QP.≃-refl
       (Lift.sourceWeightedRow weights a)
       (Lift.sourceWeightedRow weights b)
       (Lift.sourceSpatialWeighted weights as)
       (Lift.sourceSpatialWeighted weights bs))

-- Definitional decomposition of the SAME original operator's RHS.
original369RHSIsBondPlusReaction :
  (inputs : Operator.Rational369SemidiscreteInputs) →
  Operator.rational369SemidiscreteRHS inputs
    ≡
  rationalSpatialZipAdd
    (V.tabulate (λ site →
       V.tabulate (λ species →
         Operator.bondContribution inputs site species)))
    (V.tabulate (λ site →
       V.tabulate (λ species →
         Operator.reactionContribution inputs site species)))
original369RHSIsBondPlusReaction inputs = refl

-- A single selected weight coordinate splits into actual bond and
-- actual reaction totals, with no additional conservation premises.
-- Remaining: finite Fubini to identify these totals with the
-- source-native paired edge and rate column producers.
original369ComputedRHSWeightedSplit :
  (inputs : Operator.Rational369SemidiscreteInputs)
  (weights : V.Vec Q.ℚᵘ 29) →
  Q._≃_
    (Lift.sourceSpatialWeighted
      weights (Operator.rational369SemidiscreteRHS inputs))
    (Q._+_
      (Lift.sourceSpatialWeighted weights
        (V.tabulate (λ site →
           V.tabulate (λ species →
             Operator.bondContribution inputs site species))))
      (Lift.sourceSpatialWeighted weights
        (V.tabulate (λ site →
           V.tabulate (λ species →
             Operator.reactionContribution inputs site species)))))
original369ComputedRHSWeightedSplit inputs weights =
  QP.≃-trans
    (QP.≃-reflexive
      (cong (Lift.sourceSpatialWeighted weights)
        (original369RHSIsBondPlusReaction inputs)))
    (original369SpatialWeightedAdditive weights
      (V.tabulate (λ site →
        V.tabulate (λ species →
          Operator.bondContribution inputs site species)))
      (V.tabulate (λ site →
        V.tabulate (λ species →
          Operator.reactionContribution inputs site species))))
