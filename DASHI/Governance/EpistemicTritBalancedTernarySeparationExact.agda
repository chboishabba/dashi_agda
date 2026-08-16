module DASHI.Governance.EpistemicTritBalancedTernarySeparationExact where

------------------------------------------------------------------------
-- CROSS-POLLINATION CALIBRATION
--
-- Internal producer pollen:
--   * DASHI.Ontology.EpistemicTrit uses supported / unresolved / contradicted
--     as evidence states;
--   * PR #555 / LeanWikidataRelationalLensBridge refuses to map unresolved
--     evidence automatically to `tri-mid` merely because both carriers are
--     ternary;
--   * BalancedTernaryStageSymmetryExact uses neg / zeroDigit / pos as signed
--     orientation/amplitude coordinates.
--
-- Therefore cardinality 3 is not a semantic identification.  Only resolved
-- epistemic states are mapped canonically here; any treatment of unresolved as
-- neutral/zero/mid requires an explicit additional bridge policy.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)

import DASHI.Ontology.EpistemicTrit as Epistemic
import DASHI.Foundations.BalancedTernaryStageSymmetryExact as BT

data ResolvedPolarity : Set where
  resolvedAgainst resolvedFor : ResolvedPolarity

resolvedState : ResolvedPolarity → Epistemic.EpistemicTrit
resolvedState resolvedAgainst = Epistemic.contradicted
resolvedState resolvedFor = Epistemic.supported

resolvedDigit : ResolvedPolarity → BT.BalancedDigit
resolvedDigit resolvedAgainst = BT.neg
resolvedDigit resolvedFor = BT.pos

record ResolvedEpistemicView : Set where
  constructor resolvedEpistemicView
  field
    state : Epistemic.EpistemicTrit
    polarity : ResolvedPolarity
    stateExact : state ≡ resolvedState polarity

open ResolvedEpistemicView public

resolvedViewToDigit : ResolvedEpistemicView → BT.BalancedDigit
resolvedViewToDigit view = resolvedDigit (polarity view)

supportedView : ResolvedEpistemicView
supportedView = resolvedEpistemicView Epistemic.supported resolvedFor refl

contradictedView : ResolvedEpistemicView
contradictedView =
  resolvedEpistemicView Epistemic.contradicted resolvedAgainst refl

supportedMapsPositive : resolvedViewToDigit supportedView ≡ BT.pos
supportedMapsPositive = refl

contradictedMapsNegative : resolvedViewToDigit contradictedView ≡ BT.neg
contradictedMapsNegative = refl

unresolvedCannotResolveFor :
  Epistemic.unresolved ≡ resolvedState resolvedFor → ⊥
unresolvedCannotResolveFor ()

unresolvedCannotResolveAgainst :
  Epistemic.unresolved ≡ resolvedState resolvedAgainst → ⊥
unresolvedCannotResolveAgainst ()

record TotalEpistemicDigitPolicy : Set where
  constructor totalEpistemicDigitPolicy
  field
    unresolvedDigit : BT.BalancedDigit

open TotalEpistemicDigitPolicy public

encodeWithPolicy :
  TotalEpistemicDigitPolicy →
  Epistemic.EpistemicTrit →
  BT.BalancedDigit
encodeWithPolicy policy Epistemic.contradicted = BT.neg
encodeWithPolicy policy Epistemic.unresolved = unresolvedDigit policy
encodeWithPolicy policy Epistemic.supported = BT.pos

neutralUnresolvedPolicy : TotalEpistemicDigitPolicy
neutralUnresolvedPolicy = totalEpistemicDigitPolicy BT.zeroDigit

negativeUnresolvedPolicy : TotalEpistemicDigitPolicy
negativeUnresolvedPolicy = totalEpistemicDigitPolicy BT.neg

positiveUnresolvedPolicy : TotalEpistemicDigitPolicy
positiveUnresolvedPolicy = totalEpistemicDigitPolicy BT.pos

unresolvedEncodingDependsOnPolicy :
  encodeWithPolicy neutralUnresolvedPolicy Epistemic.unresolved ≡ BT.zeroDigit
  × encodeWithPolicy negativeUnresolvedPolicy Epistemic.unresolved ≡ BT.neg
  × encodeWithPolicy positiveUnresolvedPolicy Epistemic.unresolved ≡ BT.pos
unresolvedEncodingDependsOnPolicy = refl , refl , refl

record EpistemicTernarySeparationBoundary : Set where
  constructor epistemicTernarySeparationBoundary
  field
    unresolvedDefinitionallyEqualsNeutralDigit : Bool
    equalCardinalityCreatesSemanticIsomorphism : Bool
    resolvedSupportOppositionCanBeMappedExplicitly : Bool
    totalUnresolvedEncodingRequiresPolicy : Bool
    unresolvedMayBeAutomaticallyFedToLensMidpoint : Bool

canonicalEpistemicTernarySeparationBoundary :
  EpistemicTernarySeparationBoundary
canonicalEpistemicTernarySeparationBoundary =
  epistemicTernarySeparationBoundary false false true true false
