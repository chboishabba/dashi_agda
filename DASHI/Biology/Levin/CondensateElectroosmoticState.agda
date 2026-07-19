module DASHI.Biology.Levin.CondensateElectroosmoticState where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Candidate physical-state surface for membraneless condensates.
--
-- The point is to keep phase composition, ion partition, hydration,
-- osmotic balance, and electric potential as distinct observables.
-- No field is identified with semantic information by definition.

record CondensateState : Set where
  field
    denseFraction      : Bool
    ionPartitioned     : Bool
    hydrationShifted   : Bool
    osmoticBalanced    : Bool
    electricPotential  : Bool
    reversible         : Bool

open CondensateState public

record ElectroosmoticCondensateWitness : Set where
  field
    state : CondensateState

    phaseSeparated : denseFraction state ≡ true
    partitionObserved : ionPartitioned state ≡ true
    hydrationObserved : hydrationShifted state ≡ true
    osmoticBalanceObserved : osmoticBalanced state ≡ true
    potentialObserved : electricPotential state ≡ true

    notSemanticCodeByDefinition : Bool
    notSemanticCodeByDefinitionIsFalse :
      notSemanticCodeByDefinition ≡ false

    notUniversalCellMechanism : Bool
    notUniversalCellMechanismIsFalse :
      notUniversalCellMechanism ≡ false

    reading : String

open ElectroosmoticCondensateWitness public

canonicalCondensateState : CondensateState
canonicalCondensateState = record
  { denseFraction = true
  ; ionPartitioned = true
  ; hydrationShifted = true
  ; osmoticBalanced = true
  ; electricPotential = true
  ; reversible = true
  }

canonicalElectroosmoticCondensateWitness :
  ElectroosmoticCondensateWitness
canonicalElectroosmoticCondensateWitness = record
  { state = canonicalCondensateState
  ; phaseSeparated = refl
  ; partitionObserved = refl
  ; hydrationObserved = refl
  ; osmoticBalanceObserved = refl
  ; potentialObserved = refl
  ; notSemanticCodeByDefinition = false
  ; notSemanticCodeByDefinitionIsFalse = refl
  ; notUniversalCellMechanism = false
  ; notUniversalCellMechanismIsFalse = refl
  ; reading =
      "Condensate composition, hydration, ion partition, osmotic balance, and voltage remain separately typed candidate observables"
  }
