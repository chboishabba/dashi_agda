module DASHI.Base369Monster3BCompletedMultiplicityCompilerValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Fin.Base using (Fin; zero)

import DASHI.Moonshine.Base369Monster3BMultiplicityCompletedTenTritSquareCompilerExact as Compiler
import DASHI.Moonshine.Base369Monster3BMultiplicityProductActionFactorisationBidiExact as Factor
import DASHI.Moonshine.Base369Monster3BRepresentationBidiSearchRound15Exact as Round15

fin90RoundTrip :
  (multiplicity : Fin 90) →
  Compiler.completedToFin90 (Compiler.fin90ToCompleted multiplicity) ≡ multiplicity
fin90RoundTrip = Compiler.completedAfterFin90

zeroRoundTrip :
  Compiler.completedToFin90 (Compiler.fin90ToCompleted zero) ≡ zero
zeroRoundTrip = Compiler.completedAfterFin90 zero

mixedRadixOwned :
  Round15.Round15Status.mixedRadixFin90ToFin10TimesFin9
    Round15.canonicalRound15Status ≡ true
mixedRadixOwned = refl

separateRecognitionPruned :
  Round15.Round15Status.separateNinetyCarrierRecognitionStillNeeded
    Round15.canonicalRound15Status ≡ false
separateRecognitionPruned = refl

productFactorisationStillLive :
  Round15.Round15Status.productActionFactorisationProved
    Round15.canonicalRound15Status ≡ false
productFactorisationStillLive = refl

couplingInfrastructureOwned :
  Round15.Round15Status.couplingWitnessInfrastructureOwned
    Round15.canonicalRound15Status ≡ true
couplingInfrastructureOwned = refl

factorisationNotPromotedByCarrier :
  Factor.ProductActionBoundary.actualFactorisationInhabitedHere
    Factor.canonicalProductActionBoundary ≡ false
factorisationNotPromotedByCarrier = refl
