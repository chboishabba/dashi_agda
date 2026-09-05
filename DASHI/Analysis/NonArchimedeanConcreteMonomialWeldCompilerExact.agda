module DASHI.Analysis.NonArchimedeanConcreteMonomialWeldCompilerExact where

------------------------------------------------------------------------
-- CONCRETE MONOMIAL WELD COMPILER
--
-- After the reuse pass, odd-character/tau-odd semantics, canonical odd-orbit
-- classification, and signed orbit return are compiler outputs from existing
-- source/repo mathematics.  The remaining spatial task is therefore the one
-- same-object chain
--
--   literal twisted coordinate
--      -> tau-odd full function
--      -> corrected odd-character basis
--      -> source D_n character action
--      -> equality on a complete basis
--      -> literal monomial matrix equality.
--
-- Finite matrix faithfulness is reused rather than re-proved.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)

import DASHI.Analysis.NonArchimedeanCharacterBasisMatrixFaithfulnessReuseExact as Faithful

record ConcreteCharacterActionCompilerInput : Set₁ where
  field
    basisActionWeld : Faithful.SpectralBasisActionWeld

    sourceCharacterActionOwned : Bool
    sourceTauOddPreservationOwned : Bool
    oddCharacterIffTauOddCompiled : Bool
    canonicalOddOrbitChartCompiled : Bool
    twistedRestrictionIntertwinerOwned : Bool
    correctedOddCharacterDFTInstantiated : Bool
    actionEqualityDerivedOnCompleteBasis : Bool

open ConcreteCharacterActionCompilerInput public

compiledConcreteMatrixEquality :
  (input : ConcreteCharacterActionCompilerInput) →
  Faithful.SpectralBasisActionWeld.conjugatedMatrix (basisActionWeld input)
  ≡ Faithful.SpectralBasisActionWeld.monomialMatrix (basisActionWeld input)
compiledConcreteMatrixEquality input =
  Faithful.basisActionWeldClosesMatrixEquality (basisActionWeld input)


data ConcreteWeldLeaf : Set where
  instantiateConcreteSheetAdapter : ConcreteWeldLeaf
  composeTwistedRestrictionWithOddCharacterDFT : ConcreteWeldLeaf
  completeBasisActionEquality : ConcreteWeldLeaf
  oddCharacterTauOddIff : ConcreteWeldLeaf
  arithmeticOddOrbitRechart : ConcreteWeldLeaf
  signedOrbitReturn : ConcreteWeldLeaf
  finiteMatrixActionFaithfulness : ConcreteWeldLeaf
  entrywiseConjugatedMatrixExpansion : ConcreteWeldLeaf
  rebuildDFTUnitarity : ConcreteWeldLeaf
  rebuildCharacterAction : ConcreteWeldLeaf


data LeafDisposition : Set where
  live : LeafDisposition
  downstream : LeafDisposition
  compiled : LeafDisposition
  pruned : LeafDisposition

leafDisposition : ConcreteWeldLeaf → LeafDisposition
leafDisposition instantiateConcreteSheetAdapter = live
leafDisposition composeTwistedRestrictionWithOddCharacterDFT = downstream
leafDisposition completeBasisActionEquality = downstream
leafDisposition oddCharacterTauOddIff = compiled
leafDisposition arithmeticOddOrbitRechart = compiled
leafDisposition signedOrbitReturn = compiled
leafDisposition finiteMatrixActionFaithfulness = pruned
leafDisposition entrywiseConjugatedMatrixExpansion = pruned
leafDisposition rebuildDFTUnitarity = pruned
leafDisposition rebuildCharacterAction = pruned

highestAlphaConcreteWeldPath : List ConcreteWeldLeaf
highestAlphaConcreteWeldPath =
  instantiateConcreteSheetAdapter ∷
  composeTwistedRestrictionWithOddCharacterDFT ∷
  completeBasisActionEquality ∷
  []

record WeldFanout : Set where
  constructor weldFanout
  field
    closesSpatialSpectrumTransport : Bool
    closesSpatialTraceTransport : Bool
    closesSpatialPowerTransport : Bool
    signedOrbitLaneAlreadyClosedIndependently : Bool
    canonicalOrbitPartitionAlreadyClosedIndependently : Bool

canonicalWeldFanout : WeldFanout
canonicalWeldFanout = weldFanout true true true true true

oneWeldFeedsThreeConsumers :
  WeldFanout.closesSpatialSpectrumTransport canonicalWeldFanout ≡ true
oneWeldFeedsThreeConsumers = refl

phaseNoLongerBlocksSpatialWeld :
  WeldFanout.signedOrbitLaneAlreadyClosedIndependently canonicalWeldFanout ≡ true
phaseNoLongerBlocksSpatialWeld = refl
