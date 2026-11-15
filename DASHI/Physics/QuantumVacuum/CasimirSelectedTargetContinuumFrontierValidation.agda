module DASHI.Physics.QuantumVacuum.CasimirSelectedTargetContinuumFrontierValidation where

open import DASHI.Core.Prelude

import DASHI.Physics.QuantumVacuum.CasimirSelectedTargetContinuumFrontierExact as M

splitCompilerOwnedRegression :
  M.splitContinuumAndSchwingerBuildMinimalAttachmentCompilerOwned
    M.canonicalSelectedTargetContinuumBoundary ≡ true
splitCompilerOwnedRegression = refl

continuumStillRequiredRegression :
  M.selectedTargetContinuumLimitStillRequired
    M.canonicalSelectedTargetContinuumBoundary ≡ true
continuumStillRequiredRegression = refl

schwingerStillRequiredRegression :
  M.selectedTargetSchwingerMembershipStillRequired
    M.canonicalSelectedTargetContinuumBoundary ≡ true
schwingerStillRequiredRegression = refl

combinedAttachmentNotIndependentRegression :
  M.combinedMinimalAttachmentRequiredAfterTwoLeaves
    M.canonicalSelectedTargetContinuumBoundary ≡ false
combinedAttachmentNotIndependentRegression = refl

firstLeafRegression :
  M.firstSelectedTargetContinuumLeaf
  ≡ M.missingSelectedTargetContinuumLimit
firstLeafRegression = refl

secondLeafRegression :
  M.secondSelectedTargetContinuumLeaf
  ≡ M.missingSelectedTargetSchwingerMembership
secondLeafRegression = refl
