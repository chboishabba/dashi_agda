module DASHI.Moonshine.Monster3BHZetaCharacterTransportCompilerValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Moonshine.Monster3BHZetaCharacterTransportCompilerExact as Compiler

fixedPhaseIsoCompilerAvailable :
  Compiler.fixedPhaseIsoCompilerAvailable Compiler.canonicalBoundary ≡ true
fixedPhaseIsoCompilerAvailable = refl

paidHZetaCompilerAvailable :
  Compiler.paidHZetaRecognitionCompilerAvailable Compiler.canonicalBoundary ≡ true
paidHZetaCompilerAvailable = refl

literalSchrodingerCharacterDerived :
  Compiler.literalSchrodingerCharacterDerivedExecutable Compiler.canonicalBoundary ≡ true
literalSchrodingerCharacterDerived = refl

literalSchrodingerCharacterMatchesCanonicalSignature :
  Compiler.literalSchrodingerCharacterMatchesCanonicalSignatureExecutable
    Compiler.canonicalBoundary ≡ true
literalSchrodingerCharacterMatchesCanonicalSignature = refl

concreteSchrodingerRepresentationTransportStillOpen :
  Compiler.concreteSchrodingerRepresentationTransportPaidHere Compiler.canonicalBoundary ≡ false
concreteSchrodingerRepresentationTransportStillOpen = refl

concreteActualConstituentTransportStillOpen :
  Compiler.concreteActualConstituentTransportPaidHere Compiler.canonicalBoundary ≡ false
concreteActualConstituentTransportStillOpen = refl

concreteCharacterEqualityTransportStillOpen :
  Compiler.concreteDashiToTheoryCharacterTransportPaidHere Compiler.canonicalBoundary ≡ false
concreteCharacterEqualityTransportStillOpen = refl

actualHZetaNotManufacturedHere :
  Compiler.actualHZetaSameObjectInhabitedHere Compiler.canonicalBoundary ≡ false
actualHZetaNotManufacturedHere = refl
