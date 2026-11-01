module DASHI.Biology.QuantitativeStateDynamics where

open import DASHI.Core.Prelude

import DASHI.Biology.StateDependentMultiplexTransducer as Stateful

------------------------------------------------------------------------
-- Finite quantitative state dynamics.
--
-- One fixed input has amplified, attenuated, shunted, delayed, inverted, and
-- ineffective regimes depending on cellular/modulatory state.  This upgrades
-- the earlier Bool carrier with an exact response profile while remaining a
-- deliberately finite abstraction rather than a conductance calibration.
--
-- Source-facing references are inherited from
-- StateDependentMultiplexTransducer.agda:
-- David Beniaguev, Idan Segev, Michael London,
-- "Single cortical neurons as deep artificial neural networks",
-- DOI 10.1016/j.neuron.2021.07.002.
-- Michael London and Michael Hausser,
-- "Dendritic computation",
-- DOI 10.1146/annurev.neuro.28.061604.135703.

data CellularRegime : Set where
  amplifiedRegime : CellularRegime
  attenuatedRegime : CellularRegime
  shuntedRegime : CellularRegime
  delayedRegime : CellularRegime
  invertedRegime : CellularRegime
  ineffectiveRegime : CellularRegime

record QuantitativeResponse : Set where
  constructor quantitativeResponse
  field
    magnitude : Nat
    polarity : Bool
    delayed : Bool

open QuantitativeResponse public

respond : Bool → CellularRegime → QuantitativeResponse
respond false regime = quantitativeResponse 0 false false
respond true amplifiedRegime = quantitativeResponse 3 true false
respond true attenuatedRegime = quantitativeResponse 1 true false
respond true shuntedRegime = quantitativeResponse 0 true false
respond true delayedRegime = quantitativeResponse 0 true true
respond true invertedRegime = quantitativeResponse 1 false false
respond true ineffectiveRegime = quantitativeResponse 0 false false

sameInput : Bool
sameInput = true

amplifiedResponseIsThree :
  magnitude (respond sameInput amplifiedRegime) ≡ 3
amplifiedResponseIsThree = refl

attenuatedResponseIsOne :
  magnitude (respond sameInput attenuatedRegime) ≡ 1
attenuatedResponseIsOne = refl

shuntedResponseIsZero :
  magnitude (respond sameInput shuntedRegime) ≡ 0
shuntedResponseIsZero = refl

delayedResponseCarriesDelayFlag :
  delayed (respond sameInput delayedRegime) ≡ true
delayedResponseCarriesDelayFlag = refl

invertedResponseChangesPolarity :
  polarity (respond sameInput invertedRegime) ≡ false
invertedResponseChangesPolarity = refl

ineffectiveResponseIsZero :
  magnitude (respond sameInput ineffectiveRegime) ≡ 0
ineffectiveResponseIsZero = refl

amplifiedAndAttenuatedDiffer :
  respond sameInput amplifiedRegime
  ≡
  respond sameInput attenuatedRegime
  →
  ⊥
amplifiedAndAttenuatedDiffer ()

attenuatedAndInvertedDiffer :
  respond sameInput attenuatedRegime
  ≡
  respond sameInput invertedRegime
  →
  ⊥
attenuatedAndInvertedDiffer ()

shuntedAndDelayedDiffer :
  respond sameInput shuntedRegime
  ≡
  respond sameInput delayedRegime
  →
  ⊥
shuntedAndDelayedDiffer ()

------------------------------------------------------------------------
-- Delayed transmission stores a pending response for the next step.

record QuantitativeCellState : Set where
  constructor quantitativeCellState
  field
    regime : CellularRegime
    pendingMagnitude : Nat

open QuantitativeCellState public

quantitativeStep :
  Bool → QuantitativeCellState → QuantitativeResponse × QuantitativeCellState
quantitativeStep input (quantitativeCellState delayedRegime pending) =
  quantitativeResponse pending true false
  ,
  quantitativeCellState delayedRegime
    (magnitude (respond input delayedRegime) + 1)
quantitativeStep input (quantitativeCellState current pending) =
  respond input current
  ,
  quantitativeCellState current 0

initialDelayedCell : QuantitativeCellState
initialDelayedCell = quantitativeCellState delayedRegime 0

firstDelayedStepHasNoImmediateMagnitude :
  magnitude (proj₁ (quantitativeStep true initialDelayedCell)) ≡ 0
firstDelayedStepHasNoImmediateMagnitude = refl

firstDelayedStepStoresPendingMagnitude :
  pendingMagnitude (proj₂ (quantitativeStep true initialDelayedCell)) ≡ 1
firstDelayedStepStoresPendingMagnitude = refl

secondDelayedStepReleasesPendingMagnitude :
  magnitude
    (proj₁
      (quantitativeStep false
        (proj₂ (quantitativeStep true initialDelayedCell))))
  ≡
  1
secondDelayedStepReleasesPendingMagnitude = refl

------------------------------------------------------------------------
-- Bridge to the existing abstract transducer.

quantitativeTransducer : Stateful.StatefulTransducer
quantitativeTransducer =
  record
    { Input = Bool
    ; State = QuantitativeCellState
    ; Modulator = CellularRegime
    ; Output = QuantitativeResponse
    ; step = λ input state modulation →
        quantitativeStep input
          (quantitativeCellState modulation (pendingMagnitude state))
    }

quantitativeTransducerAmplifies :
  magnitude
    (Stateful.runOutput quantitativeTransducer true
      (quantitativeCellState ineffectiveRegime 0)
      amplifiedRegime)
  ≡
  3
quantitativeTransducerAmplifies = refl

quantitativeTransducerInverts :
  polarity
    (Stateful.runOutput quantitativeTransducer true
      (quantitativeCellState amplifiedRegime 0)
      invertedRegime)
  ≡
  false
quantitativeTransducerInverts = refl

record QuantitativeStateBoundary : Set where
  constructor quantitativeStateBoundary
  field
    natMagnitudeIsMembraneVoltage : Bool
    natMagnitudeIsMembraneVoltageIsFalse :
      natMagnitudeIsMembraneVoltage ≡ false

    finiteRegimesExhaustCellBiophysics : Bool
    finiteRegimesExhaustCellBiophysicsIsFalse :
      finiteRegimesExhaustCellBiophysics ≡ false

    priorStateBoundary :
      Stateful.StateDependentMultiplexBoundary

open QuantitativeStateBoundary public

canonicalQuantitativeStateBoundary : QuantitativeStateBoundary
canonicalQuantitativeStateBoundary =
  quantitativeStateBoundary
    false refl
    false refl
    Stateful.canonicalStateDependentMultiplexBoundary
