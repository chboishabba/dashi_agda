module DASHI.Reasoning.TrialecticSetEffectiveDescentExact where

------------------------------------------------------------------------
-- SET-LEVEL EFFECTIVE DESCENT FOR THE STRUCTURED TRIALECTIC COVER
--
-- The existing triadic sheaf already glues every compatible local T^9 family
-- to a global T^18 boundary and recovers all three locals.  This owner packages
-- that fact as an explicit realization object and proves uniqueness at the
-- observational level determined by those three restrictions.
--
-- No proof-irrelevance assumption is used for the compatibility fields inside
-- the global boundary record, so strict record equality is deliberately not
-- claimed.  This is Set/object-level effective descent, not groupoid-valued
-- morphism descent or an effective higher stack.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Core.Prelude

import DASHI.Foundations.RelationalStageTwelveSiteExact as RelSheaf
import DASHI.Reasoning.TrialecticGrothendieckThreeCellDescentExact as Descent
import DASHI.Reasoning.TrialecticThreeCellHyperformSynthesisExact as Cell

record GlobalRealization
    (locals : RelSheaf.TriadicLocals Cell.CellDialectic) : Set where
  constructor global-realization
  field
    globalBoundary : Cell.CompatibleThreeCellTrialecticBoundary
    realizesAB :
      Descent.restrictStructuredAB globalBoundary
      ≡ RelSheaf.localAB locals
    realizesBC :
      Descent.restrictStructuredBC globalBoundary
      ≡ RelSheaf.localBC locals
    realizesCA :
      Descent.restrictStructuredCA globalBoundary
      ≡ RelSheaf.localCA locals

open GlobalRealization public

realizeCompatibleLocals :
  (locals : RelSheaf.TriadicLocals Cell.CellDialectic) →
  (compatibility :
    RelSheaf.CompatibleOnTriadicCover Descent.cellOverlapSystem locals) →
  GlobalRealization locals
realizeCompatibleLocals locals compatibility =
  global-realization
    (Descent.glueStructured locals compatibility)
    (Descent.glueStructuredRestrictsAB locals compatibility)
    (Descent.glueStructuredRestrictsBC locals compatibility)
    (Descent.glueStructuredRestrictsCA locals compatibility)

record BoundaryObservationalEquivalence
    (left right : Cell.CompatibleThreeCellTrialecticBoundary) : Set where
  constructor boundary-observational-equivalence
  field
    sameAB :
      Descent.restrictStructuredAB left
      ≡ Descent.restrictStructuredAB right
    sameBC :
      Descent.restrictStructuredBC left
      ≡ Descent.restrictStructuredBC right
    sameCA :
      Descent.restrictStructuredCA left
      ≡ Descent.restrictStructuredCA right

open BoundaryObservationalEquivalence public

realizationsObservationallyUnique :
  ∀ {locals : RelSheaf.TriadicLocals Cell.CellDialectic} →
  (left right : GlobalRealization locals) →
  BoundaryObservationalEquivalence
    (globalBoundary left)
    (globalBoundary right)
realizationsObservationallyUnique left right =
  boundary-observational-equivalence
    (trans (realizesAB left) (sym (realizesAB right)))
    (trans (realizesBC left) (sym (realizesBC right)))
    (trans (realizesCA left) (sym (realizesCA right)))

canonicalRealization :
  GlobalRealization
    (Descent.structuredLocals Cell.canonicalCompatibleThreeCellBoundary)
canonicalRealization =
  realizeCompatibleLocals
    (Descent.structuredLocals Cell.canonicalCompatibleThreeCellBoundary)
    (Descent.structuredCompatibility Cell.canonicalCompatibleThreeCellBoundary)

canonicalRealizationRecoversAB :
  Descent.restrictStructuredAB (globalBoundary canonicalRealization)
  ≡
  RelSheaf.localAB
    (Descent.structuredLocals Cell.canonicalCompatibleThreeCellBoundary)
canonicalRealizationRecoversAB = realizesAB canonicalRealization

------------------------------------------------------------------------
-- Promotion firewall.
------------------------------------------------------------------------

data SetEffectiveDescentImpliesStrictRecordEquality : Set where
data SetEffectiveDescentImpliesGroupoidMorphismDescent : Set where

doesNotClaimStrictRecordEquality :
  SetEffectiveDescentImpliesStrictRecordEquality → ⊥
doesNotClaimStrictRecordEquality ()

doesNotClaimGroupoidMorphismDescent :
  SetEffectiveDescentImpliesGroupoidMorphismDescent → ⊥
doesNotClaimGroupoidMorphismDescent ()

record TrialecticSetEffectiveDescentBoundary : Set where
  constructor trialectic-set-effective-descent-boundary
  field
    compatibleLocalsHaveGlobalRealization : Bool
    globalRealizationConstructed : Bool
    allThreeRestrictionsRecovered : Bool
    observationalUniquenessPaid : Bool
    strictRecordEqualityUniquenessClaimed : Bool
    groupoidMorphismDescentPaid : Bool
    effectiveHigherStackClaimed : Bool

open TrialecticSetEffectiveDescentBoundary public

canonicalTrialecticSetEffectiveDescentBoundary :
  TrialecticSetEffectiveDescentBoundary
canonicalTrialecticSetEffectiveDescentBoundary =
  trialectic-set-effective-descent-boundary
    true
    true
    true
    true
    false
    false
    false
