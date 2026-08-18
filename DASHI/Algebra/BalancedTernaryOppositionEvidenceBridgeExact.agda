module DASHI.Algebra.BalancedTernaryOppositionEvidenceBridgeExact where

------------------------------------------------------------------------
-- CROSS-POLLINATION
--
-- The strict geometric antipode on {-1,0,+1} is a declared orientation
-- reversal in the claim-indexed evidence system.  It is NOT silently promoted
-- to logical negation.  This is the evidence-side counterpart of the geometric
-- rule that -1 is the antipode of +1 while 0 is the fixed centre.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.List.Base using ([])

import DASHI.Algebra.ClaimIndexedEvidencePolarityExact as Indexed
import DASHI.Algebra.DisagreementFourViewBoundary as Four
import DASHI.Foundations.BalancedTernaryAntipodalOrbitExact as Orbit
import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Reasoning.RelationalLensSynthesisCore as Lens

positiveStrictAntipodeOpposition : Indexed.OppositionDescriptor SSP.SSPTrit
positiveStrictAntipodeOpposition =
  Indexed.oppositionDescriptor
    SSP.sspPosOne
    SSP.sspNegOne
    Lens.orientationReversalRole
    Orbit.strictAntipode
    refl

negativeStrictAntipodeOpposition : Indexed.OppositionDescriptor SSP.SSPTrit
negativeStrictAntipodeOpposition =
  Indexed.oppositionDescriptor
    SSP.sspNegOne
    SSP.sspPosOne
    Lens.orientationReversalRole
    Orbit.strictAntipode
    refl

positiveAntipodeCannotSelfQualifyAsLogicalNegation :
  Indexed.LogicalNegationQualified positiveStrictAntipodeOpposition → ⊥
positiveAntipodeCannotSelfQualifyAsLogicalNegation qualification =
  Indexed.orientationReversalRoleIsNotLogicalNegation
    (Indexed.roleIsLogicalNegation qualification)

negativeAntipodeCannotSelfQualifyAsLogicalNegation :
  Indexed.LogicalNegationQualified negativeStrictAntipodeOpposition → ⊥
negativeAntipodeCannotSelfQualifyAsLogicalNegation qualification =
  Indexed.orientationReversalRoleIsNotLogicalNegation
    (Indexed.roleIsLogicalNegation qualification)

geometricAntipodeEvidence :
  Indexed.ClaimFibreEvidence
    SSP.SSPTrit ⊤ positiveStrictAntipodeOpposition tt
geometricAntipodeEvidence =
  Indexed.claimFibreEvidence (Four.assess true true) []

geometricConflictSupportsDeclaredAntipode :
  Indexed.supportsOpposingClaim geometricAntipodeEvidence ≡ true
geometricConflictSupportsDeclaredAntipode = refl

record BalancedTernaryOppositionEvidenceBoundary : Set where
  field
    strictAntipodeIsOrientationQualified : Bool
    strictAntipodeIsLogicalNegationByCarrierShape : Bool
    fixedCentreIsOpposingPole : Bool

canonicalBalancedTernaryOppositionEvidenceBoundary :
  BalancedTernaryOppositionEvidenceBoundary
canonicalBalancedTernaryOppositionEvidenceBoundary = record
  { strictAntipodeIsOrientationQualified = true
  ; strictAntipodeIsLogicalNegationByCarrierShape = false
  ; fixedCentreIsOpposingPole = false
  }
