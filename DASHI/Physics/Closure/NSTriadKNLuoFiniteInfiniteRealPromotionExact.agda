module DASHI.Physics.Closure.NSTriadKNLuoFiniteInfiniteRealPromotionExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- Springer, 2011.
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- Acta Mathematica 63 (1934), 193--248.
-- DOI: 10.1007/BF02547354.
--
-- PURPOSE
-- Isolate the exact logical content of passing a uniform finite Fourier bound
-- or identity to the physical infinite-mode carrier and then transporting an
-- exact rational certificate into the selected real carrier.  Topological
-- convergence and closedness remain explicit inputs; once supplied, the final
-- bound/equality is no longer a separate analytic field.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

record UniformFiniteBoundLimitInputs : Set₁ where
  field
    Value : Set
    lessOrEqual : Value → Value → Set

    finiteLeft finiteRight : Nat → Value
    limitingLeft limitingRight : Value

    finiteBound :
      (cutoff : Nat) →
      lessOrEqual (finiteLeft cutoff) (finiteRight cutoff)

    FiniteLeftConverges : Set
    finiteLeftConverges : FiniteLeftConverges

    FiniteRightConverges : Set
    finiteRightConverges : FiniteRightConverges

    orderClosedUnderSelectedLimits :
      FiniteLeftConverges →
      FiniteRightConverges →
      ((cutoff : Nat) →
        lessOrEqual (finiteLeft cutoff) (finiteRight cutoff)) →
      lessOrEqual limitingLeft limitingRight

open UniformFiniteBoundLimitInputs public

uniformFiniteBoundPassesToLimit :
  (inputs : UniformFiniteBoundLimitInputs) →
  lessOrEqual inputs
    (limitingLeft inputs)
    (limitingRight inputs)
uniformFiniteBoundPassesToLimit inputs =
  orderClosedUnderSelectedLimits inputs
    (finiteLeftConverges inputs)
    (finiteRightConverges inputs)
    (finiteBound inputs)

record UniformFiniteEqualityLimitInputs : Set₁ where
  field
    Value : Set

    finiteLeft finiteRight : Nat → Value
    limitingLeft limitingRight : Value

    finiteEquality :
      (cutoff : Nat) → finiteLeft cutoff ≡ finiteRight cutoff

    FiniteLeftConverges : Set
    finiteLeftConverges : FiniteLeftConverges

    FiniteRightConverges : Set
    finiteRightConverges : FiniteRightConverges

    equalityClosedUnderSelectedLimits :
      FiniteLeftConverges →
      FiniteRightConverges →
      ((cutoff : Nat) → finiteLeft cutoff ≡ finiteRight cutoff) →
      limitingLeft ≡ limitingRight

open UniformFiniteEqualityLimitInputs public

uniformFiniteEqualityPassesToLimit :
  (inputs : UniformFiniteEqualityLimitInputs) →
  limitingLeft inputs ≡ limitingRight inputs
uniformFiniteEqualityPassesToLimit inputs =
  equalityClosedUnderSelectedLimits inputs
    (finiteLeftConverges inputs)
    (finiteRightConverges inputs)
    (finiteEquality inputs)

record OrderedEmbeddingInputs : Set₁ where
  field
    ExactCarrier RealCarrier : Set

    exactLessOrEqual : ExactCarrier → ExactCarrier → Set
    realLessOrEqual : RealCarrier → RealCarrier → Set

    embed : ExactCarrier → RealCarrier

    embeddingPreservesOrder :
      (left right : ExactCarrier) →
      exactLessOrEqual left right →
      realLessOrEqual (embed left) (embed right)

    ExactAdditionPreserved : Set
    exactAdditionPreserved : ExactAdditionPreserved

    ExactMultiplicationPreserved : Set
    exactMultiplicationPreserved : ExactMultiplicationPreserved

    ExactZeroOnePreserved : Set
    exactZeroOnePreserved : ExactZeroOnePreserved

    ExactFiniteSumsPreserved : Set
    exactFiniteSumsPreserved : ExactFiniteSumsPreserved

open OrderedEmbeddingInputs public

exactBoundTransfersToRealCarrier :
  (inputs : OrderedEmbeddingInputs) →
  (left right : ExactCarrier inputs) →
  exactLessOrEqual inputs left right →
  realLessOrEqual inputs
    (embed inputs left)
    (embed inputs right)
exactBoundTransfersToRealCarrier = embeddingPreservesOrder

record PhysicalLimitPromotionReceipt : Set₁ where
  field
    schurBoundLimit : UniformFiniteBoundLimitInputs
    equation42Limit : UniformFiniteBoundLimitInputs
    section4J11LowerLimit : UniformFiniteBoundLimitInputs
    section4J11UpperLimit : UniformFiniteBoundLimitInputs
    section4J12Limit : UniformFiniteBoundLimitInputs
    section4J2Limit : UniformFiniteBoundLimitInputs
    fixedShiftDecayLimit : UniformFiniteBoundLimitInputs

    fluxIdentityLimit : UniformFiniteEqualityLimitInputs
    energyIdentityLimit : UniformFiniteEqualityLimitInputs
    dissipationIdentityLimit : UniformFiniteEqualityLimitInputs

open PhysicalLimitPromotionReceipt public

physicalSchurBoundAtInfiniteCutoff :
  (receipt : PhysicalLimitPromotionReceipt) →
  lessOrEqual (schurBoundLimit receipt)
    (limitingLeft (schurBoundLimit receipt))
    (limitingRight (schurBoundLimit receipt))
physicalSchurBoundAtInfiniteCutoff receipt =
  uniformFiniteBoundPassesToLimit (schurBoundLimit receipt)

physicalEquation42AtInfiniteCutoff :
  (receipt : PhysicalLimitPromotionReceipt) →
  lessOrEqual (equation42Limit receipt)
    (limitingLeft (equation42Limit receipt))
    (limitingRight (equation42Limit receipt))
physicalEquation42AtInfiniteCutoff receipt =
  uniformFiniteBoundPassesToLimit (equation42Limit receipt)

physicalFluxIdentityAtInfiniteCutoff :
  (receipt : PhysicalLimitPromotionReceipt) →
  limitingLeft (fluxIdentityLimit receipt)
  ≡ limitingRight (fluxIdentityLimit receipt)
physicalFluxIdentityAtInfiniteCutoff receipt =
  uniformFiniteEqualityPassesToLimit (fluxIdentityLimit receipt)

finiteBoundLimitReducerConstructed : Bool
finiteBoundLimitReducerConstructed = true

finiteEqualityLimitReducerConstructed : Bool
finiteEqualityLimitReducerConstructed = true

orderedEmbeddingReducerConstructed : Bool
orderedEmbeddingReducerConstructed = true

finiteBoundLimitReducerConstructedIsTrue :
  finiteBoundLimitReducerConstructed ≡ true
finiteBoundLimitReducerConstructedIsTrue = refl

finiteEqualityLimitReducerConstructedIsTrue :
  finiteEqualityLimitReducerConstructed ≡ true
finiteEqualityLimitReducerConstructedIsTrue = refl

orderedEmbeddingReducerConstructedIsTrue :
  orderedEmbeddingReducerConstructed ≡ true
orderedEmbeddingReducerConstructedIsTrue = refl
