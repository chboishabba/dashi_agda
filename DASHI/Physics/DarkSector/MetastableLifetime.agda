module DASHI.Physics.DarkSector.MetastableLifetime where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Deterministic finite persistence witness.  The hidden excitation survives
-- through four declared ages and becomes visible only at the terminal age.

data DecayAge : Set where
  ageZero : DecayAge
  ageOne : DecayAge
  ageTwo : DecayAge
  ageThree : DecayAge
  ageFour : DecayAge

data VisibilityPhase : Set where
  hiddenPhase : VisibilityPhase
  visibleDecayPhase : VisibilityPhase

visibilityAtAge : DecayAge → VisibilityPhase
visibilityAtAge ageZero = hiddenPhase
visibilityAtAge ageOne = hiddenPhase
visibilityAtAge ageTwo = hiddenPhase
visibilityAtAge ageThree = hiddenPhase
visibilityAtAge ageFour = visibleDecayPhase

hiddenUntilTerminalAge :
  visibilityAtAge ageZero ≡ hiddenPhase
  ×
  (visibilityAtAge ageOne ≡ hiddenPhase
    ×
    (visibilityAtAge ageTwo ≡ hiddenPhase
      × visibilityAtAge ageThree ≡ hiddenPhase))
hiddenUntilTerminalAge = refl , (refl , (refl , refl))

visibleAtTerminalAge :
  visibilityAtAge ageFour ≡ visibleDecayPhase
visibleAtTerminalAge = refl

------------------------------------------------------------------------
-- Finite scaled analogue of tau = Gamma^{-1}.  Natural-unit reciprocals are
-- represented without rational arithmetic by a common scale.

record ScaledDecayDatum : Set where
  constructor scaledDecayDatum
  field
    widthUnits : Nat
    lifetimeUnits : Nat
    reciprocalScale : Nat

open ScaledDecayDatum public

scaledReciprocalLaw : ScaledDecayDatum → Set
scaledReciprocalLaw datum =
  widthUnits datum * lifetimeUnits datum ≡ reciprocalScale datum

canonicalLongLivedDecay : ScaledDecayDatum
canonicalLongLivedDecay = scaledDecayDatum 3 4 12

canonicalWidthLifetimeReciprocal :
  scaledReciprocalLaw canonicalLongLivedDecay
canonicalWidthLifetimeReciprocal = refl

------------------------------------------------------------------------
-- A finite survival-weight table mirrors monotone decay of persistence.  It is
-- not asserted to be the continuum exponential distribution.

survivalWeight : DecayAge → Nat
survivalWeight ageZero = 12
survivalWeight ageOne = 9
survivalWeight ageTwo = 6
survivalWeight ageThree = 3
survivalWeight ageFour = 0

survivalWeightDropsByThreeAtFirstStep :
  survivalWeight ageZero ≡ survivalWeight ageOne + 3
survivalWeightDropsByThreeAtFirstStep = refl

survivalWeightVanishesAtDecay :
  survivalWeight ageFour ≡ 0
survivalWeightVanishesAtDecay = refl

record MetastableLifetimeBoundary : Set where
  constructor metastableLifetimeBoundary
  field
    deterministicFourTickPersistenceIsExponentialDecayLaw : Bool
    deterministicFourTickPersistenceIsExponentialDecayLawIsFalse :
      deterministicFourTickPersistenceIsExponentialDecayLaw ≡ false

    scaledNatReciprocalIsContinuumDecayWidthCalculation : Bool
    scaledNatReciprocalIsContinuumDecayWidthCalculationIsFalse :
      scaledNatReciprocalIsContinuumDecayWidthCalculation ≡ false

    metastabilityAloneGuaranteesVisibleDecayProducts : Bool
    metastabilityAloneGuaranteesVisibleDecayProductsIsFalse :
      metastabilityAloneGuaranteesVisibleDecayProducts ≡ false

open MetastableLifetimeBoundary public

canonicalMetastableLifetimeBoundary : MetastableLifetimeBoundary
canonicalMetastableLifetimeBoundary =
  metastableLifetimeBoundary false refl false refl false refl
