module DASHI.Physics.Closure.FiniteQuantumGRFlatModel where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import Base369 as B369
import DASHI.Physics.Closure.QuantumGRActionCompatibilityBoundary as Conditional
import DASHI.Physics.Closure.SymbolicEinsteinHilbertModel as EH
import DASHI.Physics.Closure.TypedStressEnergyMassBridge as Source

------------------------------------------------------------------------
-- A finite one-history quantum model.
--
-- This is intentionally the smallest nonempty model satisfying composition,
-- gauge-reflexivity, and amplitude compatibility.  Its purpose is to prove
-- that the quantum and flat-GR interfaces are jointly inhabitable.  It is not
-- an interacting quantum field theory or a quantisation of gravity.


data VacuumHistory : Set where
  vacuumHistory : VacuumHistory

composeHistory : VacuumHistory → VacuumHistory → VacuumHistory
composeHistory vacuumHistory vacuumHistory = vacuumHistory

historyIdentity : VacuumHistory
historyIdentity = vacuumHistory

historyActionPhase : VacuumHistory → B369.TriTruth
historyActionPhase vacuumHistory = B369.tri-low

historyAmplitude : VacuumHistory → B369.TriTruth
historyAmplitude vacuumHistory = B369.tri-low

composeAssociative :
  (a b c : VacuumHistory) →
  composeHistory a (composeHistory b c)
  ≡ composeHistory (composeHistory a b) c
composeAssociative vacuumHistory vacuumHistory vacuumHistory = refl

leftIdentity :
  (history : VacuumHistory) →
  composeHistory historyIdentity history ≡ history
leftIdentity vacuumHistory = refl

rightIdentity :
  (history : VacuumHistory) →
  composeHistory history historyIdentity ≡ history
rightIdentity vacuumHistory = refl

amplitudeRespectsComposition :
  (left right : VacuumHistory) →
  historyAmplitude (composeHistory left right)
  ≡ B369.triXor (historyAmplitude left) (historyAmplitude right)
amplitudeRespectsComposition vacuumHistory vacuumHistory = refl


data GaugeEquivalent : VacuumHistory → VacuumHistory → Set where
  gaugeRefl : GaugeEquivalent vacuumHistory vacuumHistory

gaugeReflexive : (history : VacuumHistory) → GaugeEquivalent history history
gaugeReflexive vacuumHistory = gaugeRefl

record FiniteQuantumModelReceipt : Set where
  constructor mkFiniteQuantumModelReceipt
  field
    associativityReceipt :
      (a b c : VacuumHistory) →
      composeHistory a (composeHistory b c)
      ≡ composeHistory (composeHistory a b) c
    leftIdentityReceipt :
      (history : VacuumHistory) →
      composeHistory historyIdentity history ≡ history
    rightIdentityReceipt :
      (history : VacuumHistory) →
      composeHistory history historyIdentity ≡ history
    amplitudeCompositionReceipt :
      (left right : VacuumHistory) →
      historyAmplitude (composeHistory left right)
      ≡ B369.triXor (historyAmplitude left) (historyAmplitude right)
    gaugeReflexivityReceipt :
      (history : VacuumHistory) → GaugeEquivalent history history
    modelScope : String

open FiniteQuantumModelReceipt public

finiteQuantumModelReceipt : FiniteQuantumModelReceipt
finiteQuantumModelReceipt =
  mkFiniteQuantumModelReceipt
    composeAssociative
    leftIdentity
    rightIdentity
    amplitudeRespectsComposition
    gaugeReflexive
    "singleton finite history model over the existing TriTruth composition law"

------------------------------------------------------------------------
-- Joint flat quantum/GR interface model.

record FlatQuantumGRInterfaceReceipt : Set where
  constructor mkFlatQuantumGRInterfaceReceipt
  field
    quantumReceipt : FiniteQuantumModelReceipt
    flatEinsteinReceipt : EH.FlatVacuumEinsteinReceipt
    flatSourceReceipt : Source.FlatBianchiStressReceipt
    conditionalCompatibilityReceipt :
      Conditional.QuantumGRCompatibilityReceipt
        Conditional.canonicalSharedActionCarrier
        Conditional.canonicalConditionalQuantumMeasure
        Conditional.canonicalConditionalQuantumGRLimit
    theoryOfEverythingStillBlocked :
      Conditional.theoryOfEverythingPromotionPermitted
        Conditional.canonicalUnificationPromotionBoundary
      ≡ false
    interfaceScope : String

open FlatQuantumGRInterfaceReceipt public

flatQuantumGRInterfaceReceipt : FlatQuantumGRInterfaceReceipt
flatQuantumGRInterfaceReceipt =
  mkFlatQuantumGRInterfaceReceipt
    finiteQuantumModelReceipt
    EH.flatVacuumEinsteinReceipt
    Source.flatBianchiStressReceipt
    Conditional.canonicalConditionalQuantumGRCompatibility
    Conditional.canonicalTheoryOfEverythingBlocked
    "jointly inhabited finite interface; no interacting quantum gravity or empirical claim"
