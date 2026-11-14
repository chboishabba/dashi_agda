{-# OPTIONS --safe #-}
module DASHI.Physics.Plasma.KSW668FiniteDiscriminatorsExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.Bool using (Bool; true; false)

------------------------------------------------------------------------
-- KSW 668: FINITE DISCRIMINATORS, NOT AN INHABITED UNIVERSAL TOE.
-- Original video claims remain attributed hypotheses.
-- No postulates, arbitrary evidence constants, or physics promotions.
------------------------------------------------------------------------

data ⊥ : Set where

sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl yz = yz

------------------------------------------------------------------------
-- A. Exchange cancellation does not determine direction from field size.
--
-- An exchanged pair has opposite signed directions, but both assignments
-- are possible with EXACTLY the same ordered 2 > 1 field magnitudes.
-- The underlying real-valued cancellation theorem is in
-- MHDFullTransferFromExchangeCompatiblePayloadExact, reused by adapter.
------------------------------------------------------------------------

data Flow : Set where
  outflow inflow stagnant : Flow

reverseFlow : Flow → Flow
reverseFlow outflow = inflow
reverseFlow inflow = outflow
reverseFlow stagnant = stagnant

record ExchangeWorld : Set where
  constructor exchange-world
  field
    strongMagnitude weakMagnitude : Nat
    forward backward : Flow
    exchanged : forward ≡ reverseFlow backward

open ExchangeWorld public

forwardWorld : ExchangeWorld
forwardWorld = exchange-world 2 1 outflow inflow refl

reverseWorld : ExchangeWorld
reverseWorld = exchange-world 2 1 inflow outflow refl

sameOrderedMagnitudes :
  strongMagnitude forwardWorld ≡ strongMagnitude reverseWorld
sameOrderedMagnitudes = refl

sameWeakMagnitude :
  weakMagnitude forwardWorld ≡ weakMagnitude reverseWorld
sameWeakMagnitude = refl

reverseWorldStillExchanged : forward reverseWorld ≡ reverseFlow (backward reverseWorld)
reverseWorldStillExchanged = exchanged reverseWorld

inflowCannotBeOutflow : inflow ≡ outflow → ⊥
inflowCannotBeOutflow ()

universalStrongToWeakFromPairCancellationNoGo :
  ((w : ExchangeWorld) →
    strongMagnitude w ≡ 2 →
    weakMagnitude w ≡ 1 →
    forward w ≡ outflow) → ⊥
universalStrongToWeakFromPairCancellationNoGo universal =
  inflowCannotBeOutflow (universal reverseWorld refl refl)

------------------------------------------------------------------------
-- B. Integrated Poynting conservation, conditional on physical producers.
--
-- delta U + outward flux + integral(J dot E) = 0.
-- This is an algebraic inference from a supplied balance, NOT a derivation
-- of Maxwell PDE, vector calculus, units or physical boundary conditions.
------------------------------------------------------------------------

record IntegratedPoyntingBudget : Set₁ where
  constructor integrated-poynting-budget
  infixl 6 _⊕_
  field
    Scalar : Set
    _⊕_ : Scalar → Scalar → Scalar
    zero : Scalar
    rightZero : (x : Scalar) → _⊕_ x zero ≡ x
    energyDelta fluxOut jDotE : Scalar
    balance : _⊕_ (_⊕_ energyDelta fluxOut) jDotE ≡ zero

open IntegratedPoyntingBudget public

zeroFluxImpliesSignedWork :
  (b : IntegratedPoyntingBudget) →
  fluxOut b ≡ zero b →
  _⊕_ b (energyDelta b) (jDotE b) ≡ zero b
zeroFluxImpliesSignedWork b noBoundary
  rewrite noBoundary | rightZero b (energyDelta b) = balance b

------------------------------------------------------------------------
-- C. Nuclear species identity: separate charge and neutron accounting.
-- He4+He4+He4 -> C12 (intermediate Be8 / gamma / Q not modelled).
-- N14+n -> C14+p.  All are STOICHIOMETRIC checks, not rate predictions.
------------------------------------------------------------------------

record Nuclide : Set where
  constructor nuclide
  field
    protons neutrons : Nat

open Nuclide public

hydrogen1 helium4 carbon12 carbon14 nitrogen14 freeNeutron freeProton :
  Nuclide
hydrogen1 = nuclide 1 0
helium4 = nuclide 2 2
carbon12 = nuclide 6 6
carbon14 = nuclide 6 8
nitrogen14 = nuclide 7 7
freeNeutron = nuclide 0 1
freeProton = nuclide 1 0

tripleAlphaCharge :
  protons helium4 + protons helium4 + protons helium4
  ≡ protons carbon12
tripleAlphaCharge = refl

tripleAlphaNeutrons :
  neutrons helium4 + neutrons helium4 + neutrons helium4
  ≡ neutrons carbon12
tripleAlphaNeutrons = refl

nitrogenCarbon14Charge :
  protons nitrogen14 + protons freeNeutron
  ≡ protons carbon14 + protons freeProton
nitrogenCarbon14Charge = refl

nitrogenCarbon14Neutrons :
  neutrons nitrogen14 + neutrons freeNeutron
  ≡ neutrons carbon14 + neutrons freeProton
nitrogenCarbon14Neutrons = refl

sixHydrogenNucleiCannotDirectlySupplyCarbon12Neutrons :
  (neutrons hydrogen1 + neutrons hydrogen1 + neutrons hydrogen1 +
   neutrons hydrogen1 + neutrons hydrogen1 + neutrons hydrogen1)
  ≡ neutrons carbon12 → ⊥
sixHydrogenNucleiCannotDirectlySupplyCarbon12Neutrons ()

------------------------------------------------------------------------
-- D. Correlation without signalling. This finite constant local marginal
-- cannot encode a remote binary choice. It is NOT a general quantum theorem.
------------------------------------------------------------------------

data RemoteChoice : Set where
  choice0 choice1 : RemoteChoice

data LocalOutcome : Set where
  baseline pulse : LocalOutcome

localMarginal : RemoteChoice → LocalOutcome
localMarginal _ = baseline

localMarginalChoiceInvariant :
  localMarginal choice0 ≡ localMarginal choice1
localMarginalChoiceInvariant = refl

record OperationalBitChannel (observe : RemoteChoice → LocalOutcome) : Set where
  constructor operational-bit-channel
  field
    zeroMessage : observe choice0 ≡ baseline
    oneMessage : observe choice1 ≡ pulse

baselineCannotBePulse : baseline ≡ pulse → ⊥
baselineCannotBePulse ()

conditionedFieldNoSignalInConstantMarginal :
  OperationalBitChannel localMarginal → ⊥
conditionedFieldNoSignalInConstantMarginal channel =
  baselineCannotBePulse (OperationalBitChannel.oneMessage channel)

------------------------------------------------------------------------
-- E. Same observed isotope trace, two distinct causal mechanisms.
-- This is a finite identifiability counterexample, not an experiment.
------------------------------------------------------------------------

data Mechanism : Set where
  metabolicRedistribution nuclearConversion : Mechanism

data IsotopeTrace : Set where
  sameMeasuredTrace : IsotopeTrace

record CausalWorld : Set where
  constructor causal-world
  field
    mechanism : Mechanism
    trace : IsotopeTrace

open CausalWorld public

redistributionWorld : CausalWorld
redistributionWorld = causal-world metabolicRedistribution sameMeasuredTrace

nuclearWorld : CausalWorld
nuclearWorld = causal-world nuclearConversion sameMeasuredTrace

sameObservations :
  trace redistributionWorld ≡ trace nuclearWorld
sameObservations = refl

redistributionIsNotNuclear :
  metabolicRedistribution ≡ nuclearConversion → ⊥
redistributionIsNotNuclear ()

emotionIsotopeCausalIdentificationNoGo :
  (classifier : IsotopeTrace → Mechanism) →
  classifier (trace redistributionWorld) ≡ metabolicRedistribution →
  classifier (trace nuclearWorld) ≡ nuclearConversion → ⊥
emotionIsotopeCausalIdentificationNoGo classifier identifiesA identifiesB =
  redistributionIsNotNuclear (trans (sym identifiesA) identifiesB)
