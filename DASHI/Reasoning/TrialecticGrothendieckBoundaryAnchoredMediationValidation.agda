module DASHI.Reasoning.TrialecticGrothendieckBoundaryAnchoredMediationValidation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Reasoning.TrialecticGrothendieckBoundaryAnchoredMediationExact as Anchored

boundary : Anchored.TrialecticGrothendieckBoundaryAnchoredMediationBoundary
boundary = Anchored.canonicalTrialecticGrothendieckBoundaryAnchoredMediationBoundary

allThreeEdgesAnchored : Anchored.allThreeEdgeArgumentsAnchored boundary ≡ true
allThreeEdgesAnchored = refl

faceLawRetained : Anchored.originalFaceLawRetained boundary ≡ true
faceLawRetained = refl

strongAdapterConstructed : Anchored.strongSecondOrderAdapterConstructed boundary ≡ true
strongAdapterConstructed = refl

arbitraryEdgesRejected : Anchored.arbitraryUnrelatedEdgesAccepted boundary ≡ false
arbitraryEdgesRejected = refl
