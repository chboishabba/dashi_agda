module DASHI.Physics.Closure.NSBoundedPotentialTurnoverBudget where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Primitive using (Set)
open import Relation.Binary.PropositionalEquality using (subst; sym)

------------------------------------------------------------------------
-- One-sided bounded-potential accounting.
--
-- For an absolutely continuous scalar potential A with
--
--   A' = replenishment - depletion,
--
-- integration gives
--
--   initial + replenishment = final + depletion.
--
-- Nonnegativity of the final potential therefore bounds total depletion by
-- initial potential plus replenishment.  This is the missing algebraic bridge
-- between a signed turnover potential and the residence reduction: unsigned
-- geometric path length alone has no finite budget, while one-sided escape
-- from a bounded potential does.
------------------------------------------------------------------------

record PotentialBudgetArithmetic : Set₁ where
  field
    Scalar : Set
    zero : Scalar
    _+_ : Scalar → Scalar → Scalar
    _*_ : Scalar → Scalar → Scalar
    _≤_ : Scalar → Scalar → Set

    ≤-trans :
      {a b c : Scalar} → _≤_ a b → _≤_ b c → _≤_ a c

    addZeroLeft :
      (a : Scalar) → _+_ zero a ≡ a

    additionMonotoneRight :
      {a b c : Scalar} →
      _≤_ a b →
      _≤_ (_+_ a c) (_+_ b c)

open PotentialBudgetArithmetic public

record BoundedPotentialBalance
    (A : PotentialBudgetArithmetic) : Set₁ where
  field
    initialPotential : Scalar A
    finalPotential : Scalar A
    depletionIntegral : Scalar A
    replenishmentIntegral : Scalar A

    finalPotentialNonnegative :
      _≤_ A (zero A) finalPotential

    oneSidedBalance :
      _+_ A initialPotential replenishmentIntegral ≡
      _+_ A finalPotential depletionIntegral

open BoundedPotentialBalance public

boundedPotentialControlsDepletion :
  (A : PotentialBudgetArithmetic) →
  (B : BoundedPotentialBalance A) →
  _≤_ A
    (depletionIntegral B)
    (_+_ A (initialPotential B) (replenishmentIntegral B))
boundedPotentialControlsDepletion A B =
  subst
    (λ rhs → _≤_ A (depletionIntegral B) rhs)
    (sym (oneSidedBalance B))
    depletion≤finalPlusDepletion
  where
  zeroPlusDepletion≤finalPlusDepletion :
    _≤_ A
      (_+_ A (zero A) (depletionIntegral B))
      (_+_ A (finalPotential B) (depletionIntegral B))
  zeroPlusDepletion≤finalPlusDepletion =
    additionMonotoneRight A (finalPotentialNonnegative B)

  depletion≤finalPlusDepletion :
    _≤_ A
      (depletionIntegral B)
      (_+_ A (finalPotential B) (depletionIntegral B))
  depletion≤finalPlusDepletion =
    subst
      (λ lhs →
        _≤_ A lhs
          (_+_ A (finalPotential B) (depletionIntegral B)))
      (addZeroLeft A (depletionIntegral B))
      zeroPlusDepletion≤finalPlusDepletion

------------------------------------------------------------------------
-- Residence composition.  The PDE-facing theorem must prove that dangerous
-- transfer consumes the signed depletion integral.  Once that is supplied,
-- the bounded potential and its replenishment control dangerous residence.
------------------------------------------------------------------------

record BoundedPotentialResidenceInputs
    (A : PotentialBudgetArithmetic) : Set₁ where
  field
    potentialBalance : BoundedPotentialBalance A
    dangerCost : Scalar A
    dangerousResidence : Scalar A

    dangerousTransferConsumesSignedEscape :
      _≤_ A
        (_*_ A dangerCost dangerousResidence)
        (depletionIntegral potentialBalance)

open BoundedPotentialResidenceInputs public

boundedPotentialForcesResidenceBound :
  (A : PotentialBudgetArithmetic) →
  (I : BoundedPotentialResidenceInputs A) →
  _≤_ A
    (_*_ A (dangerCost I) (dangerousResidence I))
    (_+_ A
      (initialPotential (potentialBalance I))
      (replenishmentIntegral (potentialBalance I)))
boundedPotentialForcesResidenceBound A I =
  ≤-trans A
    (dangerousTransferConsumesSignedEscape I)
    (boundedPotentialControlsDepletion A (potentialBalance I))

------------------------------------------------------------------------
-- Candidate mechanism labels.  The experiment may rank mechanisms, but only
-- a proof inhabiting the signed-escape field above promotes one into the
-- residence theorem.
------------------------------------------------------------------------

data TurnoverMechanism : Set where
  directionMotion : TurnoverMechanism
  spectralProjectorMotion : TurnoverMechanism
  enstrophyRedistribution : TurnoverMechanism
  combinedAlignmentEscape : TurnoverMechanism

record CandidateTurnoverCurrency
    (A : PotentialBudgetArithmetic) : Set₁ where
  field
    mechanism : TurnoverMechanism
    unsignedPathLength : Scalar A
    signedEscape : Scalar A

open CandidateTurnoverCurrency public
