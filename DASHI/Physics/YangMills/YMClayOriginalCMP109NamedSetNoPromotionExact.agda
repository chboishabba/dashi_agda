module DASHI.Physics.YangMills.YMClayOriginalCMP109NamedSetNoPromotionExact where

------------------------------------------------------------------------
-- CONCRETE ORIGINAL owner: not merely a generic toy BareNamedField.
-- The real Balaban round-six CMP109 contract has five fields : Set.
-- Choosing the UNINHABITED type for each yields a valid CMP109
-- record, even though it proves NO executable holonomy proposition.
--
-- This is a precise source-native proof that the first five original
-- A-family obligation *names* cannot themselves be evidence of physics.
-- The real physical implication is available only after an AnchoredField
-- carries BOTH an exact chosen same-Y predicate equality and its proof.
-- Do not declare the whole 219 cut closed from a record with Set fields.
--
-- No postulates or holes. Agda typecheck/transitive trust PENDING.
------------------------------------------------------------------------

import DASHI.Physics.YangMills.BalabanClayGate4PhysicalClosureRound6ExactCutset as Gate4
import DASHI.Physics.YangMills.YMClayProofRelevantFieldAnchoringSafeExact as Safe

actualOriginalCMP109WithFiveEmptyTypeSelections :
  Gate4.CMP109Round6Cutset
actualOriginalCMP109WithFiveEmptyTypeSelections = record
  { Gate4.CMP109Round6Cutset.executableWordHolonomyIdentification = Safe.NoProof
  ; Gate4.CMP109Round6Cutset.rectangleCurvatureProductIdentification = Safe.NoProof
  ; Gate4.CMP109Round6Cutset.adjacentSwapCurvatureEstimate = Safe.NoProof
  ; Gate4.CMP109Round6Cutset.sixSwapBoundInsideGroupAverageDiameter = Safe.NoProof
  ; Gate4.CMP109Round6Cutset.principalLogChartOnAveragedContour = Safe.NoProof
  }

-- There cannot be a proof of every chosen field proposition merely
-- from its valid original CMP109 record: instantiate the valid record
-- above with a demonstrably uninhabited chosen type.
actualOriginalCMP109CannotUniformlyProveChosenHolonomy :
  ((contract : Gate4.CMP109Round6Cutset) →
    Gate4.executableWordHolonomyIdentification contract) →
  Safe.NoProof
actualOriginalCMP109CannotUniformlyProveChosenHolonomy pretend =
  pretend actualOriginalCMP109WithFiveEmptyTypeSelections

-- The correct proof-relevant SAME-OBJECT route on the actual original
-- field projection, with an externally fixed physical predicate.
originalCMP109HolonomyProofGivenPhysicalAnchoring :
  ∀ {Physical : Set} {Y : Physical}
    (selectedPredicate : Physical → Set)
    (contract : Gate4.CMP109Round6Cutset) →
  Safe.AnchoredField
    (Gate4.executableWordHolonomyIdentification contract)
    Y selectedPredicate →
  selectedPredicate Y
originalCMP109HolonomyProofGivenPhysicalAnchoring predicate contract =
  Safe.anchoredFieldGivesSelectedPhysicalProof
