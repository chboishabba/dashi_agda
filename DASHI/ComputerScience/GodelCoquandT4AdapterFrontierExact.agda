module DASHI.ComputerScience.GodelCoquandT4AdapterFrontierExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- COQUAND T4 -> DASHI ARITHMETISED FORMAL-SYSTEM ADAPTER FRONTIER
--
-- This file does not import coquand/agda-godel-tree.  It records the exact
-- same-object coordinates observed in that external source and the local weld
-- still required before its machine-checked results can inhabit DASHI's ABI.
------------------------------------------------------------------------

data T4ObservedCoordinate : Set where
  t4Term
  t4Formula
  t4DerivIndexedByFormula
  t4NotFreeF
  t4MetaSubstF
  t4ObjectSubstitutionSbf
  t4CodeFormula
  t4CodeFormulaNat
  t4Num
  t4Sub
  t4SubEquation
  t4ProvabilityVerifierThmT
  t4LobTheorem : T4ObservedCoordinate

observedT4Coordinates : List T4ObservedCoordinate
observedT4Coordinates =
  t4Term ∷ t4Formula ∷ t4DerivIndexedByFormula ∷ t4NotFreeF ∷
  t4MetaSubstF ∷ t4ObjectSubstitutionSbf ∷ t4CodeFormula ∷
  t4CodeFormulaNat ∷ t4Num ∷ t4Sub ∷ t4SubEquation ∷
  t4ProvabilityVerifierThmT ∷ t4LobTheorem ∷ []

------------------------------------------------------------------------
-- The local ABI has distinct Term / Formula / BinaryFormula / Sentence / Proof
-- carriers.  T4 has Term / Formula and an indexed derivation family Deriv P.
-- Therefore the adapter should use restricted/subtype fibres rather than
-- identify all formula-shaped carriers.
------------------------------------------------------------------------

data T4AdapterResidual : Set where
  unaryFormulaSubtype
  binaryFormulaSubtype
  closedSentenceSubtype
  existentialProofCarrier
  codeProjectionForRestrictedCarriers
  numeralProjection
  unaryInstantiationClosure
  binaryInstantiationClosure
  provableProjection
  provesProjection
  negationClosure
  implicationClosure
  biconditionalClosure
  consistencySentenceSelection
  substitutionSameObjectWeld
  shapeAuthorityWeld : T4AdapterResidual

canonicalT4AdapterResiduals : List T4AdapterResidual
canonicalT4AdapterResiduals =
  unaryFormulaSubtype ∷ binaryFormulaSubtype ∷ closedSentenceSubtype ∷
  existentialProofCarrier ∷ codeProjectionForRestrictedCarriers ∷
  numeralProjection ∷ unaryInstantiationClosure ∷ binaryInstantiationClosure ∷
  provableProjection ∷ provesProjection ∷ negationClosure ∷ implicationClosure ∷
  biconditionalClosure ∷ consistencySentenceSelection ∷
  substitutionSameObjectWeld ∷ shapeAuthorityWeld ∷ []

------------------------------------------------------------------------
-- Minimal exact receipt expected from an implementation.
------------------------------------------------------------------------

record CoquandT4AdapterReceipt : Set where
  constructor coquandT4AdapterReceipt
  field
    sourceRevisionPinned : Bool
    sourceSafeModeObserved : Bool
    termCarrierSameObject : Bool
    formulaCarrierRestrictedBySourceFreeVariableRelation : Bool
    binaryFormulaCarrierRestrictedBySourceFreeVariableRelation : Bool
    sentenceCarrierRestrictedBySourceClosedness : Bool
    proofCarrierRetainsDerivedFormula : Bool
    codeFormulaProjectionExact : Bool
    numeralProjectionExact : Bool
    instantiateUsesT4Substitution : Bool
    provableMeansT4Derivability : Bool
    substituteCodeUsesT4Sub : Bool
    substitutionExactTransported : Bool
    shapeAuthorityPaid : Bool
    localKernelReplayObserved : Bool

currentCoquandT4AdapterReceipt : CoquandT4AdapterReceipt
currentCoquandT4AdapterReceipt =
  coquandT4AdapterReceipt
    false true
    true false false false false
    false false false false false false false false

------------------------------------------------------------------------
-- Why this route is high-alpha:
--
-- T4.Lob already constructs a Guard-style diagonal identity internally from
-- sub / num / codeFormula and derives the Loeb theorem.  Therefore a completed
-- adapter may provide much more than the current diagonal seam.  But until the
-- exact carrier/proof/substitution weld is present, those theorems remain
-- external source facts rather than DASHI theorem inhabitants.
------------------------------------------------------------------------

data T4LobImpliesLocalLobWithoutAdapter : Set where
data T4DerivImpliesLocalProvableWithoutCarrierWeld : Set where
data T4SubImpliesLocalSubstituteCodeWithoutExactness : Set where

t4LobDoesNotCrossABIByName : T4LobImpliesLocalLobWithoutAdapter → ⊥
t4LobDoesNotCrossABIByName ()

t4DerivNeedsCarrierWeld : T4DerivImpliesLocalProvableWithoutCarrierWeld → ⊥
t4DerivNeedsCarrierWeld ()

t4SubNeedsExactTransport : T4SubImpliesLocalSubstituteCodeWithoutExactness → ⊥
t4SubNeedsExactTransport ()

record CoquandT4AdapterBoundary : Set where
  constructor coquandT4AdapterBoundary
  field
    externalSourceContainsDiagonalInfrastructure : Bool
    externalSourceContainsLob : Bool
    externalSourceSafeFlagObserved : Bool
    localAdapterStructurallyPlausible : Bool
    localAdapterComplete : Bool
    localKernelReplayComplete : Bool

canonicalCoquandT4AdapterBoundary : CoquandT4AdapterBoundary
canonicalCoquandT4AdapterBoundary =
  coquandT4AdapterBoundary true true true true false false
