module DASHI.Cubical.NavierStokesCandidate where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.List using (List; _∷_; [])
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Fail-closed Cubical adapter compatibility surface.
--
-- The intended Cubical wrapper must import these real receipt variables:
--
--   DASHI.Physics.Closure.NavierStokesRegularityTowerReceipt
--     canonicalNavierStokesRegularityTowerReceipt
--     navierStokesRegularityTowerKeepsClayFalse
--     navierStokesRegularityTowerKeepsContinuumLiftFalse
--
--   DASHI.Physics.Closure.MillenniumTowerNavierStokesInstanceReceipt
--     canonicalMillenniumTowerNavierStokesInstanceReceipt
--     millenniumTowerNavierStokesNoClayPromotion
--
-- A module using --cubical or --erased-cubical cannot import those receipt
-- modules because they were checked without --cubical-compatible and without
-- --without-K.  This module deliberately does not fabricate Cubical paths.

record NavierStokesCubicalAdapterIncompatibility : Set where
  field
    candidateModule :
      String

    regularityTowerModule :
      String

    millenniumInstanceModule :
      String

    requiredExistingVars :
      List String

    exactAgdaIncompatibility :
      List String

    cubicalWrapperConstructed :
      Bool

open NavierStokesCubicalAdapterIncompatibility public

navierStokesCubicalAdapterIncompatibility :
  NavierStokesCubicalAdapterIncompatibility
navierStokesCubicalAdapterIncompatibility =
  record
    { candidateModule =
        "DASHI.Cubical.NavierStokesCandidate"
    ; regularityTowerModule =
        "DASHI.Physics.Closure.NavierStokesRegularityTowerReceipt"
    ; millenniumInstanceModule =
        "DASHI.Physics.Closure.MillenniumTowerNavierStokesInstanceReceipt"
    ; requiredExistingVars =
        "canonicalNavierStokesRegularityTowerReceipt"
        ∷ "navierStokesRegularityTowerKeepsClayFalse"
        ∷ "navierStokesRegularityTowerKeepsContinuumLiftFalse"
        ∷ "canonicalMillenniumTowerNavierStokesInstanceReceipt"
        ∷ "millenniumTowerNavierStokesNoClayPromotion"
        ∷ []
    ; exactAgdaIncompatibility =
        "Importing DASHI.Physics.Closure.NavierStokesRegularityTowerReceipt from a --cubical module fails because the imported module does not use --without-K."
        ∷ "Importing DASHI.Physics.Closure.NavierStokesRegularityTowerReceipt from a --cubical module fails because the imported module does not use --cubical-compatible."
        ∷ "The same restriction applies under --erased-cubical."
        ∷ []
    ; cubicalWrapperConstructed =
        false
    }
