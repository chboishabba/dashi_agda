module DASHI.Analysis.DissipationPathMonotonicity where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Energy.Core as EC

------------------------------------------------------------------------
-- Energy/free-energy descent from an exact dissipation identity.
--
-- If
--
--   F(x) = F(step i x) + D(i,x)
--
-- and D is nonnegative, then F(step i x) <= F(x).  Transitivity gives the same
-- result for every finite input path.
--
-- This is deliberately weaker than detailed balance.  Detailed balance,
-- gradient-flow structure, a discrete H-theorem, or another concrete mechanism
-- may supply the identity in a domain instance.
------------------------------------------------------------------------

record OrderedAdditiveEnergy
    {e : Level}
    (Energy : Set e)
    (P : EC.Preorder Energy)
    : Set (lsuc e) where
  field
    zero : Energy
    _⊕_ : Energy → Energy → Energy

    zeroLower :
      (value : Energy) →
      EC.Preorder._≤_ P zero value

    rightIdentity :
      (value : Energy) →
      value ⊕ zero ≡ value

    addMonotoneLeft :
      (fixed : Energy) →
      ∀ {left right} →
      EC.Preorder._≤_ P left right →
      EC.Preorder._≤_ P
        (fixed ⊕ left)
        (fixed ⊕ right)

open OrderedAdditiveEnergy public

record DissipativeTransition
    {x e i : Level}
    {State : Set x}
    {Energy : Set e}
    (ES : EC.EnergySpace State Energy)
    (Input : Set i)
    : Set (lsuc (x ⊔ e ⊔ i)) where
  field
    additive :
      OrderedAdditiveEnergy Energy (EC.EnergySpace.P ES)

    step : Input → State → State
    dissipation : Input → State → Energy

    energyBalance :
      (input : Input) →
      (state : State) →
      EC.EnergySpace.energy ES state
        ≡ _⊕_ additive
            (EC.EnergySpace.energy ES (step input state))
            (dissipation input state)

open DissipativeTransition public

transitionEnergyDescends :
  ∀ {x e i}
    {State : Set x}
    {Energy : Set e}
    {Input : Set i}
    {ES : EC.EnergySpace State Energy} →
  (D : DissipativeTransition ES Input) →
  (input : Input) →
  (state : State) →
  EC.Preorder._≤_ (EC.EnergySpace.P ES)
    (EC.EnergySpace.energy ES (step D input state))
    (EC.EnergySpace.energy ES state)
transitionEnergyDescends {ES = ES} D input state =
  subst
    (λ right →
      EC.Preorder._≤_ (EC.EnergySpace.P ES)
        (EC.EnergySpace.energy ES (step D input state))
        right)
    (sym (energyBalance D input state))
    afterIdentity
  where
  stepEnergy : Energy
  stepEnergy = EC.EnergySpace.energy ES (step D input state)

  dissipated : Energy
  dissipated = dissipation D input state

  withZero :
    EC.Preorder._≤_ (EC.EnergySpace.P ES)
      (_⊕_ (additive D) stepEnergy (zero (additive D)))
      (_⊕_ (additive D) stepEnergy dissipated)
  withZero =
    addMonotoneLeft (additive D) stepEnergy
      (zeroLower (additive D) dissipated)

  afterIdentity :
    EC.Preorder._≤_ (EC.EnergySpace.P ES)
      stepEnergy
      (_⊕_ (additive D) stepEnergy dissipated)
  afterIdentity =
    subst
      (λ left →
        EC.Preorder._≤_ (EC.EnergySpace.P ES)
          left
          (_⊕_ (additive D) stepEnergy dissipated))
      (rightIdentity (additive D) stepEnergy)
      withZero

runDissipativePath :
  ∀ {x e i}
    {State : Set x}
    {Energy : Set e}
    {Input : Set i}
    {ES : EC.EnergySpace State Energy} →
  DissipativeTransition ES Input →
  List Input →
  State →
  State
runDissipativePath D [] state = state
runDissipativePath D (input ∷ inputs) state =
  runDissipativePath D inputs (step D input state)

pathEnergyDescends :
  ∀ {x e i}
    {State : Set x}
    {Energy : Set e}
    {Input : Set i}
    {ES : EC.EnergySpace State Energy} →
  (D : DissipativeTransition ES Input) →
  (inputs : List Input) →
  (state : State) →
  EC.Preorder._≤_ (EC.EnergySpace.P ES)
    (EC.EnergySpace.energy ES (runDissipativePath D inputs state))
    (EC.EnergySpace.energy ES state)
pathEnergyDescends {ES = ES} D [] state =
  EC.Preorder.refl (EC.EnergySpace.P ES)
    (EC.EnergySpace.energy ES state)
pathEnergyDescends {ES = ES} D (input ∷ inputs) state =
  EC.Preorder.trans (EC.EnergySpace.P ES)
    (pathEnergyDescends D inputs (step D input state))
    (transitionEnergyDescends D input state)

record DissipationMonotonicityCertificate
    {x e i : Level}
    {State : Set x}
    {Energy : Set e}
    {Input : Set i}
    {ES : EC.EnergySpace State Energy}
    (D : DissipativeTransition ES Input)
    : Set (lsuc (x ⊔ e ⊔ i)) where
  field
    oneStep :
      (input : Input) →
      (state : State) →
      EC.Preorder._≤_ (EC.EnergySpace.P ES)
        (EC.EnergySpace.energy ES (step D input state))
        (EC.EnergySpace.energy ES state)

    finitePath :
      (inputs : List Input) →
      (state : State) →
      EC.Preorder._≤_ (EC.EnergySpace.P ES)
        (EC.EnergySpace.energy ES (runDissipativePath D inputs state))
        (EC.EnergySpace.energy ES state)

open DissipationMonotonicityCertificate public

certifyDissipationMonotonicity :
  ∀ {x e i}
    {State : Set x}
    {Energy : Set e}
    {Input : Set i}
    {ES : EC.EnergySpace State Energy} →
  (D : DissipativeTransition ES Input) →
  DissipationMonotonicityCertificate D
certifyDissipationMonotonicity D = record
  { oneStep = transitionEnergyDescends D
  ; finitePath = pathEnergyDescends D
  }
