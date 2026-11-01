module DASHI.Analysis.SupportMomentDominationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

record PositiveSupportedMomentFamily : Set₁ where
  field
    Scalar : Set
    radius : Scalar
    moment1 moment3 moment5 : Scalar
    square fourth : Scalar → Scalar
    multiply : Scalar → Scalar → Scalar
    LessOrEqual : Scalar → Scalar → Set
    moment3Dominated :
      LessOrEqual moment3 (multiply (square radius) moment1)
    moment5Dominated :
      LessOrEqual moment5 (multiply (fourth radius) moment1)
    reading : String

open PositiveSupportedMomentFamily public

------------------------------------------------------------------------
-- Equality-saturated finite regression.  This avoids a long closed Nat-order
-- proof while still showing the radius-power domination shape is executable.
------------------------------------------------------------------------

finiteRadius finiteMoment1 finiteMoment3 finiteMoment5 : Nat
finiteRadius = 2
finiteMoment1 = 1
finiteMoment3 = 4
finiteMoment5 = 16

finiteMoment3BoundExact :
  finiteMoment3 ≡ finiteRadius ^ 2 * finiteMoment1
finiteMoment3BoundExact = refl

finiteMoment5BoundExact :
  finiteMoment5 ≡ finiteRadius ^ 4 * finiteMoment1
finiteMoment5BoundExact = refl

record SupportMomentDominationBoundary : Set where
  constructor supportMomentDominationBoundary
  field
    genericSupportDominationInterfaceConstructed : Bool
    genericSupportDominationInterfaceConstructedIsTrue :
      genericSupportDominationInterfaceConstructed ≡ true
    finiteDominationRegressionConstructed : Bool
    finiteDominationRegressionConstructedIsTrue :
      finiteDominationRegressionConstructed ≡ true
    actualTaperN3DominationDerivedInAgda : Bool
    actualTaperN3DominationDerivedInAgdaIsFalse :
      actualTaperN3DominationDerivedInAgda ≡ false
    actualTaperN5DominationDerivedInAgda : Bool
    actualTaperN5DominationDerivedInAgdaIsFalse :
      actualTaperN5DominationDerivedInAgda ≡ false

canonicalSupportMomentDominationBoundary : SupportMomentDominationBoundary
canonicalSupportMomentDominationBoundary =
  supportMomentDominationBoundary true refl true refl false refl false refl
