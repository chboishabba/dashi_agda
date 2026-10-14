module DASHI.Biology.IIT4FiniteDistinctionExact where

open import DASHI.Core.Prelude

import DASHI.Biology.IIT4FiniteCausalStructureExact as IIT4

------------------------------------------------------------------------
-- IIT-4 FINITE DISTINCTION SURFACE
--
-- A distinction is not system phi.  It belongs to one nonempty mechanism and
-- records its maximally irreducible cause/effect purviews, their specified
-- states, directional mechanism integrated information, and
-- phi_d = min(phi_c, phi_e).
--
-- Numerical repertoire/MIP search may be supplied by an executable backend;
-- this owner keeps the finite composition object and its receipts typed.
------------------------------------------------------------------------

record MechanismPurviewIrreducibility
    (system : IIT4.FiniteCausalSystem)
    (Score : Set) : Set₁ where
  constructor mechanismPurviewIrreducibility
  field
    mechanism : IIT4.Mechanism system
    purview : IIT4.Purview system
    specifiedPurviewState : IIT4.StateOf system
    intrinsicSpecification : Score
    mechanismPhi : Score
    disintegratingPartitionReceipt : String
    purviewStateSelectionReceipt : String
    mipReceipt : String

open MechanismPurviewIrreducibility public

record FiniteDistinction
    (system : IIT4.FiniteCausalSystem)
    (Score : Set) : Set₁ where
  constructor finiteDistinction
  field
    structuralDistinction : IIT4.CausalDistinction system
    causeAnalysis : MechanismPurviewIrreducibility system Score
    effectAnalysis : MechanismPurviewIrreducibility system Score
    sameMechanismReceipt : String
    phiCause : Score
    phiEffect : Score
    phiDistinction : Score
    distinctionMinimumReceipt : String
    congruenceReceipt : String

open FiniteDistinction public

record DistinctionSearchReceipt
    (system : IIT4.FiniteCausalSystem)
    (Score : Set) : Set₁ where
  constructor distinctionSearchReceipt
  field
    nonemptyMechanismsEnumerated : Bool
    nonemptyPurviewsEnumerated : Bool
    mechanismOutsideUnitsCausallyMarginalized : Bool
    disintegratingPartitionsEnumerated : Bool
    causeAndEffectPurviewsSelectedSeparately : Bool
    retainedDistinctions : List (FiniteDistinction system Score)
    searchReceipt : String

open DistinctionSearchReceipt public

record IIT4DistinctionBoundary : Set where
  constructor iit4DistinctionBoundary
  field
    mechanismAndPurviewAreFiniteMasks : Bool
    outsideMechanismUnitsRequireCausalMarginalization : Bool
    disintegratingPartitionAllowsEmptyParts : Bool
    causeAndEffectMechanismPhiRemainSeparate : Bool
    phiDIsMinimumDirectionalMechanismIntegration : Bool
    systemPhiEqualsDistinctionPhiByDefinition : Bool
    distinctionSetExistsWithoutMechanismSearchByDefinition : Bool

open IIT4DistinctionBoundary public

canonicalIIT4DistinctionBoundary : IIT4DistinctionBoundary
canonicalIIT4DistinctionBoundary =
  iit4DistinctionBoundary true true true true true false false

systemPhiNotDistinctionPhi :
  systemPhiEqualsDistinctionPhiByDefinition canonicalIIT4DistinctionBoundary ≡ false
systemPhiNotDistinctionPhi = refl

mechanismSearchCannotBeSkipped :
  distinctionSetExistsWithoutMechanismSearchByDefinition
    canonicalIIT4DistinctionBoundary ≡ false
mechanismSearchCannotBeSkipped = refl
