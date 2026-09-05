module DASHI.Analysis.NonArchimedeanConcreteMonomialWeldCompilerExact where

------------------------------------------------------------------------
-- CONCRETE MONOMIAL WELD COMPILER
--
-- Highest-alpha route after the source audit:
--
--   tau-odd/odd-character identification
--   + arithmetic odd-orbit chart (j,b) <-> +/-3^j
--   + source D_n character action
--   + concrete twisted-coordinate <-> character-basis identification
--   + equality of the two operators on each complete basis vector
--   + existing finite matrix-action faithfulness
--       => literal conjugated-matrix = monomial-matrix equality.
--
-- This is deliberately a compiler from source-specific receipts into a matrix
-- equality.  It does not rebuild DFT algebra or finite matrix extensionality.
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
    oddCharacterIffTauOddReceiptOwned : Bool
    arithmeticOddOrbitChartOwned : Bool
    twistedCoordinateCharacterReceiptOwned : Bool
    concreteDFTBasisReceiptOwned : Bool
    actionEqualityDerivedOnCompleteBasis : Bool

open ConcreteCharacterActionCompilerInput public

compiledConcreteMatrixEquality :
  (input : ConcreteCharacterActionCompilerInput) →
  Faithful.SpectralBasisActionWeld.conjugatedMatrix (basisActionWeld input)
  ≡ Faithful.SpectralBasisActionWeld.monomialMatrix (basisActionWeld input)
compiledConcreteMatrixEquality input =
  Faithful.basisActionWeldClosesMatrixEquality (basisActionWeld input)


data ConcreteWeldLeaf : Set where
  oddCharacterTauOddIff : ConcreteWeldLeaf
  arithmeticOddOrbitRechart : ConcreteWeldLeaf
  twistedCoordinateCharacterIdentification : ConcreteWeldLeaf
  completeBasisActionEquality : ConcreteWeldLeaf
  finiteMatrixActionFaithfulness : ConcreteWeldLeaf
  entrywiseConjugatedMatrixExpansion : ConcreteWeldLeaf
  rebuildDFTUnitarity : ConcreteWeldLeaf
  rebuildCharacterAction : ConcreteWeldLeaf


data LeafDisposition : Set where
  live : LeafDisposition
  downstream : LeafDisposition
  pruned : LeafDisposition

leafDisposition : ConcreteWeldLeaf → LeafDisposition
leafDisposition oddCharacterTauOddIff = live
leafDisposition arithmeticOddOrbitRechart = live
leafDisposition twistedCoordinateCharacterIdentification = live
leafDisposition completeBasisActionEquality = downstream
leafDisposition finiteMatrixActionFaithfulness = pruned
leafDisposition entrywiseConjugatedMatrixExpansion = pruned
leafDisposition rebuildDFTUnitarity = pruned
leafDisposition rebuildCharacterAction = pruned

highestAlphaConcreteWeldPath : List ConcreteWeldLeaf
highestAlphaConcreteWeldPath =
  arithmeticOddOrbitRechart ∷
  oddCharacterTauOddIff ∷
  twistedCoordinateCharacterIdentification ∷
  completeBasisActionEquality ∷
  []

record WeldFanout : Set where
  constructor weldFanout
  field
    closesSpatialSpectrumTransport : Bool
    closesSpatialTraceTransport : Bool
    closesSpatialPowerTransport : Bool
    closesOrbitPhaseSignReceipt : Bool
    closesCanonicalOrbitPartitionReceipt : Bool

canonicalWeldFanout : WeldFanout
canonicalWeldFanout = weldFanout true true true false false

oneWeldFeedsThreeConsumers :
  WeldFanout.closesSpatialSpectrumTransport canonicalWeldFanout ≡ true
oneWeldFeedsThreeConsumers = refl

phaseRemainsIndependent :
  WeldFanout.closesOrbitPhaseSignReceipt canonicalWeldFanout ≡ false
phaseRemainsIndependent = refl
