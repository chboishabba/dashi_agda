module DASHI.Algebra.Quantum.ShorCyclicDFTLeanCrossProverWeldRegression where

open import DASHI.Core.Prelude

import DASHI.Algebra.Quantum.ShorCyclicDFTLeanCrossProverWeldExact as Weld

------------------------------------------------------------------------
-- RED regression: retain the exact Lean DFT source and expose the unpaid
-- same-object weld rather than promoting external theorem authority into Agda.
------------------------------------------------------------------------

crossProverBoundaryExists : Weld.CyclicDFTLeanCrossProverWeldBoundary
crossProverBoundaryExists = Weld.canonicalCyclicDFTLeanCrossProverWeldBoundary

agdaResolutionNotPromoted :
  Weld.CyclicDFTLeanCrossProverWeldBoundary.agdaCharacterResolutionInhabited
    Weld.canonicalCyclicDFTLeanCrossProverWeldBoundary
  ≡ false
agdaResolutionNotPromoted = refl
