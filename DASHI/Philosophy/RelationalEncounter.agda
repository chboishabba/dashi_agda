module DASHI.Philosophy.RelationalEncounter where

open import Agda.Primitive using (Set₁)

import DASHI.Philosophy.SituatedState as Situated

------------------------------------------------------------------------
-- Encounter replaces guaranteed synthesis.
--
-- Every interpretation exposes what was preserved, distinguished,
-- unresolved, and lost.  Voice preservation and repair remain explicit.

record Interpretation
       (A B : Situated.SituatedState) : Set₁ where
  field
    translate :
      Situated.Commitment A →
      Situated.Commitment B

    Preserved :
      Set

    Distinguished :
      Set

    Unresolved :
      Set

    Lost :
      Set

    residualReceipt :
      Set

    authority :
      Set

    nonClaimBoundary :
      Set

open Interpretation public

record RelationalEncounter
       (A B C : Situated.SituatedState) : Set₁ where
  field
    interpretationAB :
      Interpretation A C

    interpretationBA :
      Interpretation B C

    voiceAIsTracked :
      Set

    voiceBIsTracked :
      Set

    unresolvedDifference :
      Set

    repairObligation :
      Set

    noGuaranteedUnity :
      Set

open RelationalEncounter public

record TransformationWithoutUnrecordedErasure
       {A B : Situated.SituatedState}
       (T : Interpretation A B) : Set₁ where
  field
    preservedVisible :
      Preserved T

    distinguishedVisible :
      Distinguished T

    unresolvedVisible :
      Unresolved T

    lostVisible :
      Lost T

    residualVisible :
      residualReceipt T

open TransformationWithoutUnrecordedErasure public
