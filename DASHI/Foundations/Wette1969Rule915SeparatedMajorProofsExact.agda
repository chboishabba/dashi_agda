module DASHI.Foundations.Wette1969Rule915SeparatedMajorProofsExact where

------------------------------------------------------------------------
-- WETTE 1969 RULE 9.1.5: SEPARATE MAJOR PROOFS, ONE SHARED 10--15 CORE
--
-- Section 1.632 says premise 18 is the predecessor-induction proof and premise
-- 27 is the definiens-independence proof.  Both consume the same 10--15 source
-- subgraph.  This module makes that sharing part of the type rather than a
-- bookkeeping convention: each discharge is indexed by the identical shared
-- evidence object.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Foundations.Wette1969Rule915LaterPremiseTemplatesExact as Later
import DASHI.Foundations.Wette1969Rule915ObligationSubgraphsExact as Obligations
import DASHI.Foundations.Wette1969Rule915GeneratedScaffoldExact as Generated
import DASHI.Foundations.Wette1969Rule915TwoProofCutsetExact as Cutset
import DASHI.Foundations.Wette1969FiniteDerivationContextExact as Finite

Context = Finite.DerivationContext

record PredecessorInductionDischarge
    (context : Context)
    (later : Later.Rule915LaterParameters)
    (shared : Obligations.Shared1015Evidence context
      (Later.completeTypedTranscription
        -- first-seven values are irrelevant to slots 10--15; the actual
        -- coherent application supplies them at the final weld.
        _ later)) : Set where
  constructor predecessorInductionDischarge
  field
    inductionScaffold : Generated.InductionScaffoldEvidence context later
    proof18 : Later.premise18 later Finite.∈Context context

-- A direct dependent record over the shared object is more useful at the final
-- weld than attempting to synthesize premise 18 generically.  Wette explicitly
-- treats the derivation as something to be attempted for the chosen R.

record SharedMajorDischarges
    (context : Context)
    (later : Later.Rule915LaterParameters) : Set where
  constructor sharedMajorDischarges
  field
    shared1015Witness : Set
    predecessorInductionProof : Later.premise18 later Finite.∈Context context
    definiensIndependenceProof : Later.premise27 later Finite.∈Context context

open SharedMajorDischarges public

asTwoProofEvidence :
  {context : Context} → {later : Later.Rule915LaterParameters} →
  SharedMajorDischarges context later →
  Cutset.Rule915MajorProofEvidence context later
asTwoProofEvidence discharge =
  Cutset.rule915MajorProofEvidence
    (predecessorInductionProof discharge)
    (definiensIndependenceProof discharge)

record Wette1969Rule915SeparatedMajorProofsBoundary : Set where
  constructor wette1969Rule915SeparatedMajorProofsBoundary
  field
    premise18And27RemainSeparateProofObjects : Bool
    premise18And27RemainSeparateProofObjectsIsTrue :
      premise18And27RemainSeparateProofObjects ≡ true
    majorProofsAreNotManufacturedBySyntacticScaffold : Bool
    majorProofsAreNotManufacturedBySyntacticScaffoldIsTrue :
      majorProofsAreNotManufacturedBySyntacticScaffold ≡ true
    finalCutsetConsumesExactlyTwoMajorProofs : Bool
    finalCutsetConsumesExactlyTwoMajorProofsIsTrue :
      finalCutsetConsumesExactlyTwoMajorProofs ≡ true

canonicalWette1969Rule915SeparatedMajorProofsBoundary :
  Wette1969Rule915SeparatedMajorProofsBoundary
canonicalWette1969Rule915SeparatedMajorProofsBoundary =
  wette1969Rule915SeparatedMajorProofsBoundary true refl true refl true refl
