module DASHI.Analysis.RiemannG2SourceNativePhiHatModulationAdapterExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAnalyticSubstrate as Analytic
import DASHI.Analysis.WeilTestSpace as Weil
import DASHI.Analysis.RiemannExplicitFormula as Explicit
import DASHI.Analysis.RiemannFormulaAnalyticCompatibility as Compat
import DASHI.Analysis.RiemannG2GammaMellinImplementationRecoveryExact as Recovery
import DASHI.Analysis.RiemannG2GammaMellinProofRelevantActionCompilerExact as StrongCompiler

------------------------------------------------------------------------
-- SOURCE-NATIVE TAPER / PHIHAT ACTION -> PROOF-RELEVANT H_A
--
-- The later Hermitian source audit already records ownership of a real-even
-- taper, complex phiHat, Fourier conjugation symmetry and source window/tail
-- control.  Under the repo-complete assumption, the remaining work is a
-- representation recovery problem: identify the concrete source test carrier
-- with the canonical Gamma/Mellin Test and reuse the already-owned source
-- character action and transform-shift laws.
--
-- This owner compiles that exact source-native package directly into the
-- repository's strongest proof-relevant H_A implementation surface.  No
-- Set-valued shift socket is accepted as theorem payment here.
------------------------------------------------------------------------

record SourceNativePhiHatModulation
    (analytic : Analytic.AnalyticSubstrate)
    (space : Weil.WeilTestSpace)
    (formula : Explicit.RiemannExplicitFormula space)
    (compat : Compat.RiemannFormulaAnalyticCompatibility analytic space formula)
    : Set₁ where
  private
    MellinTest =
      Analytic.GammaMellinLayer.Test
        (Analytic.AnalyticSubstrate.gammaMellin analytic)
  field
    SourceTest : Set

    -- Same-object realization, not an analogy or arbitrary isomorphism.
    sourceTestIdentity : SourceTest ≡ MellinTest

    sourceReference : String

    -- Existing source-native target-character action.
    act :
      Weil.WeilTestSpace.Scalar space →
      SourceTest → SourceTest

    -- Expected canonical observations after exact transport into Weil Test.
    expectedCharacterAction :
      Weil.WeilTestSpace.Scalar space →
      Weil.WeilTestSpace.Test space →
      Weil.WeilTestSpace.Test space

    expectedShiftedSpectralResponse :
      Weil.WeilTestSpace.Scalar space →
      Weil.WeilTestSpace.Test space →
      Weil.WeilTestSpace.Scalar space

    expectedTransformShift :
      Weil.WeilTestSpace.Scalar space →
      Weil.WeilTestSpace.Test space →
      Weil.WeilTestSpace.TransformValue space

open SourceNativePhiHatModulation public

sourceImplementation :
  ∀ {analytic space formula compat} →
  SourceNativePhiHatModulation analytic space formula compat →
  Recovery.GammaMellinTestImplementation analytic
sourceImplementation P = record
  { Recovery.ImplementationTest = SourceTest P
  ; Recovery.implementationTestIsCanonicalMellinTest = sourceTestIdentity P
  ; Recovery.implementationReference = sourceReference P
  }

sourceTransportedAction :
  ∀ {analytic space formula compat} →
  (P : SourceNativePhiHatModulation analytic space formula compat) →
  Weil.WeilTestSpace.Scalar space →
  Weil.WeilTestSpace.Test space →
  Weil.WeilTestSpace.Test space
sourceTransportedAction P t f =
  StrongCompiler.implementationToWeil (sourceImplementation P)
    (act P t
      (StrongCompiler.weilToImplementation (sourceImplementation P) f))

------------------------------------------------------------------------
-- The theorem-bearing source receipt.  Every field below is an actual proof on
-- the SAME transported action and SAME concrete RiemannExplicitFormula.
------------------------------------------------------------------------

record SourceNativePhiHatModulationProof
    {analytic : Analytic.AnalyticSubstrate}
    {space : Weil.WeilTestSpace}
    {formula : Explicit.RiemannExplicitFormula space}
    {compat : Compat.RiemannFormulaAnalyticCompatibility analytic space formula}
    (P : SourceNativePhiHatModulation analytic space formula compat) : Set₁ where
  field
    preservesCanonicalAdmissibility :
      (t : Weil.WeilTestSpace.Scalar space) →
      (f : Weil.WeilTestSpace.Test space) →
      Weil.WeilTestSpace.admissible space f →
      Weil.WeilTestSpace.admissible space (sourceTransportedAction P t f)

    actionAgreesWithCanonicalHX :
      (t : Weil.WeilTestSpace.Scalar space) →
      (f : Weil.WeilTestSpace.Test space) →
      sourceTransportedAction P t f
      ≡ expectedCharacterAction P t f

    sameFormulaSpectralShift :
      (t : Weil.WeilTestSpace.Scalar space) →
      (f : Weil.WeilTestSpace.Test space) →
      Explicit.RiemannExplicitFormula.spectralZeroForm formula
        (sourceTransportedAction P t f)
      ≡ expectedShiftedSpectralResponse P t f

    sameWeilTransformShift :
      (t : Weil.WeilTestSpace.Scalar space) →
      (f : Weil.WeilTestSpace.Test space) →
      Weil.WeilTestSpace.transform space (sourceTransportedAction P t f)
      ≡ expectedTransformShift P t f

open SourceNativePhiHatModulationProof public

------------------------------------------------------------------------
-- Exact compiler into the already-owned implementation-action carrier.
------------------------------------------------------------------------

toProofRelevantImplementedMellinAction :
  ∀ {analytic space formula compat} →
  (P : SourceNativePhiHatModulation analytic space formula compat) →
  SourceNativePhiHatModulationProof P →
  StrongCompiler.ProofRelevantImplementedMellinAction
    analytic space formula compat (sourceImplementation P)
toProofRelevantImplementedMellinAction P proof = record
  { StrongCompiler.act = act P
  ; StrongCompiler.expectedCharacterAction = expectedCharacterAction P
  ; StrongCompiler.expectedShiftedSpectralResponse =
      expectedShiftedSpectralResponse P
  ; StrongCompiler.expectedTransformShift = expectedTransformShift P
  ; StrongCompiler.preservesPulledBackWeilAdmissibility =
      preservesCanonicalAdmissibility proof
  ; StrongCompiler.actionAgreesWithCanonicalHXAfterTransport =
      actionAgreesWithCanonicalHX proof
  ; StrongCompiler.sameFormulaSpectralShiftAfterTransport =
      sameFormulaSpectralShift proof
  ; StrongCompiler.sameWeilTransformShiftAfterTransport =
      sameWeilTransformShift proof
  ; StrongCompiler.producerReference = sourceReference P
  }

------------------------------------------------------------------------
-- BIDI search pruning after this compiler.
------------------------------------------------------------------------

data SourceNativeSearchAction : Set where
  rebuildGenericFourierTheory
  reuseFiniteC3FourierAsRiemannTest
  searchForAnotherAbstractHAInterface
  recoverConcreteSourceTestImplementation
  identifySourceTestWithCanonicalMellinTest
  recoverSourceCharacterMultiplicationAction
  recoverSourceAdmissibilityProof
  recoverSourceSameFormulaShift
  recoverSourceSameWeilTransformShift
  compileIntoProofRelevantHA
  : SourceNativeSearchAction

SourceNativeRelevant : SourceNativeSearchAction → Set
SourceNativeRelevant rebuildGenericFourierTheory = ⊥
SourceNativeRelevant reuseFiniteC3FourierAsRiemannTest = ⊥
SourceNativeRelevant searchForAnotherAbstractHAInterface = ⊥
SourceNativeRelevant recoverConcreteSourceTestImplementation = ⊤
SourceNativeRelevant identifySourceTestWithCanonicalMellinTest = ⊤
SourceNativeRelevant recoverSourceCharacterMultiplicationAction = ⊤
SourceNativeRelevant recoverSourceAdmissibilityProof = ⊤
SourceNativeRelevant recoverSourceSameFormulaShift = ⊤
SourceNativeRelevant recoverSourceSameWeilTransformShift = ⊤
SourceNativeRelevant compileIntoProofRelevantHA = ⊤

rebuildGenericFourierTheoryPruned :
  SourceNativeRelevant rebuildGenericFourierTheory → ⊥
rebuildGenericFourierTheoryPruned x = x

finiteC3AsRiemannTestPruned :
  SourceNativeRelevant reuseFiniteC3FourierAsRiemannTest → ⊥
finiteC3AsRiemannTestPruned x = x

anotherAbstractHAInterfacePruned :
  SourceNativeRelevant searchForAnotherAbstractHAInterface → ⊥
anotherAbstractHAInterfacePruned x = x

record SourceNativePhiHatModulationBoundary : Set where
  constructor source-native-phihat-modulation-boundary
  field
    sourceComplexPhiHatAndTaperInfrastructureAlreadyOwned : Bool
    sourceComplexPhiHatAndTaperInfrastructureAlreadyOwnedIsTrue :
      sourceComplexPhiHatAndTaperInfrastructureAlreadyOwned ≡ true

    sourceTestMustBeMerelyIsomorphicToCanonicalMellinTest : Bool
    sourceTestMustBeMerelyIsomorphicToCanonicalMellinTestIsFalse :
      sourceTestMustBeMerelyIsomorphicToCanonicalMellinTest ≡ false

    exactSourceTestEqualitySupportsActionTransport : Bool
    exactSourceTestEqualitySupportsActionTransportIsTrue :
      exactSourceTestEqualitySupportsActionTransport ≡ true

    sourceShiftMustBeProofRelevant : Bool
    sourceShiftMustBeProofRelevantIsTrue : sourceShiftMustBeProofRelevant ≡ true

    sourceWeilTransformShiftMustBeProofRelevant : Bool
    sourceWeilTransformShiftMustBeProofRelevantIsTrue :
      sourceWeilTransformShiftMustBeProofRelevant ≡ true

    strongerProofRelevantHACompilerAlreadyOwned : Bool
    strongerProofRelevantHACompilerAlreadyOwnedIsTrue :
      strongerProofRelevantHACompilerAlreadyOwned ≡ true

    anotherHAInterfaceNeeded : Bool
    anotherHAInterfaceNeededIsFalse : anotherHAInterfaceNeeded ≡ false

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

canonicalSourceNativePhiHatModulationBoundary :
  SourceNativePhiHatModulationBoundary
canonicalSourceNativePhiHatModulationBoundary =
  source-native-phihat-modulation-boundary
    true refl
    false refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
