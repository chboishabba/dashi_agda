module DASHI.Analysis.SupportMomentDominationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Generic compact-support moment domination.
--
-- For a positive measure supported on 0 <= u <= R,
--
--   M_{k+2} <= R^2 M_k,
--
-- and iterating once more gives
--
--   M_{k+4} <= R^4 M_k.
--
-- G21 uses k=1 for the odd taper moments:
--
--   N3(y) <= R^2 N1(y),
--   N5(y) <= R^4 N1(y),
--
-- with R=L/2.  This owner records the reusable theorem shape and a finite
-- exact regression; the actual continuum integral monotonicity remains a
-- producer obligation until connected to the companion real-analysis layer.
------------------------------------------------------------------------

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
-- Finite regression over Nat: support {0,1,2} lies in radius 2, and the
-- displayed moments satisfy M3 <= 2^2 M1 and M5 <= 2^4 M1.
------------------------------------------------------------------------

finiteMoment1 finiteMoment3 finiteMoment5 : Nat
finiteMoment1 = 3
finiteMoment3 = 9
finiteMoment5 = 33

finiteRadius : Nat
finiteRadius = 2

finiteMoment3Bound : finiteMoment3 ≤ finiteRadius ^ 2 * finiteMoment1
finiteMoment3Bound = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))

finiteMoment5Bound : finiteMoment5 ≤ finiteRadius ^ 4 * finiteMoment1
finiteMoment5Bound =
  s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s
  (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s
  (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s
  (s≤s (s≤s (s≤s z≤n))))))))))))))))))))))))))))))))

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
