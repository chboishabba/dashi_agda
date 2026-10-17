module DASHI.Unified.TOEConcreteInhabitantsValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Unified.TOEConcreteInhabitantsExact as Inhabitants

atomicC3OrderThree :
  (x : Inhabitants.AtomicP2Basis) →
  Inhabitants.atomicP2C3
    (Inhabitants.atomicP2C3
      (Inhabitants.atomicP2C3 x)) ≡ x
atomicC3OrderThree = Inhabitants.atomicP2C3OrderThree

atomicCoulombIsConcrete :
  Inhabitants.numerator Inhabitants.atomicP2CoulombEnergy ≡ 21
atomicCoulombIsConcrete = refl

atomicCoulombCommutesWithC3 :
  (a b : Inhabitants.AtomicP2Basis) →
  Inhabitants.atomicP2CoulombMatrix
    (Inhabitants.atomicP2C3 a)
    (Inhabitants.atomicP2C3 b)
  ≡
  Inhabitants.atomicP2CoulombMatrix a b
atomicCoulombCommutesWithC3 = Inhabitants.atomicP2CoulombC3Invariant

rtReceiptIsImportedFormalInhabitant :
  Inhabitants.authority Inhabitants.lean68RTInhabitant
  ≡ Inhabitants.importedFormalInhabitant
rtReceiptIsImportedFormalInhabitant = refl

jacobsonReceiptIsImportedFormalInhabitant :
  Inhabitants.authority Inhabitants.lean68JacobsonInhabitant
  ≡ Inhabitants.importedFormalInhabitant
jacobsonReceiptIsImportedFormalInhabitant = refl

cmReceiptIsImportedFormalInhabitant :
  Inhabitants.authority Inhabitants.lean73CMInhabitant
  ≡ Inhabitants.importedFormalInhabitant
cmReceiptIsImportedFormalInhabitant = refl
