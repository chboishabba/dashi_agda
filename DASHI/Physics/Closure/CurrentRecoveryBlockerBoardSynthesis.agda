module DASHI.Physics.Closure.CurrentRecoveryBlockerBoardSynthesis where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.ChemistryRightLimitsCrossBandClosurePackage as Chemistry
import DASHI.Physics.Closure.CanonicalToNoncanonicalMdlRetargetedSeamPackage as MDL
import Ontology.BrainDNA.BrainDNACodecChannelBoundaryPackage as BrainDNA

------------------------------------------------------------------------
-- Minimal current synthesis for the lanes discussed in the blocker thread.
--
-- Chemistry and retargeted MDL have theorem-bearing owners.  Brain-DNA is a
-- theorem-bearing adjacent boundary package, but is deliberately not promoted
-- into physics closure evidence.

record CurrentRecoveryBlockerBoardSynthesis : Setω where
  field
    chemistryRightLimits :
      Chemistry.ChemistryRightLimitsCrossBandClosurePackage

    canonicalToNoncanonicalMdl :
      MDL.CanonicalToNoncanonicalMdlRetargetedSeamPackage

    brainDNACodecChannelBoundary :
      BrainDNA.BrainDNACodecChannelBoundaryPackage

    remainingBoundary : List String

currentRecoveryBlockerBoardSynthesis :
  CurrentRecoveryBlockerBoardSynthesis
currentRecoveryBlockerBoardSynthesis =
  record
    { chemistryRightLimits =
        Chemistry.canonicalChemistryRightLimitsCrossBandClosurePackage
    ; canonicalToNoncanonicalMdl =
        MDL.canonicalToNoncanonicalMdlRetargetedSeamPackage
    ; brainDNACodecChannelBoundary =
        BrainDNA.brainDNACodecChannelBoundaryPackage
    ; remainingBoundary =
        "Chemistry is closed only at the quotient-visible pre-spectral cross-band law"
        ∷ "MDL is closed only on the accepted retargeted schedule channel; the old carrier remains obstructed"
        ∷ "Brain-DNA remains an adjacent storage/channel theorem surface, not closure evidence"
        ∷ "Spectral, scale-setting, biological-dynamics, and empirical-promotion theorems remain separate work"
        ∷ []
    }
