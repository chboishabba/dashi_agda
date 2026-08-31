module DASHI.Analysis.RiemannG2SourceNativePhiHatModulationAdapterExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAnalyticSubstrate as Analytic
import DASHI.Analysis.WeilTestSpace as Weil
import DASHI.Analysis.RiemannExplicitFormula as Explicit
import DASHI.Analysis.RiemannFormulaAnalyticCompatibility as Compat
import DASHI.Analysis.RiemannG2MellinTestActionTransportExact as MellinAction

------------------------------------------------------------------------
-- SOURCE-NATIVE TAPER / PHIHAT ACTION -> CANONICAL MELLIN TEST ACTION
--
-- Later Riemann/Hermitian owners already record source ownership of a real-even
-- taper, complex phiHat, Fourier conjugation symmetry and window/tail control.
-- The remaining representation seam is not another harmonic identity: it is
-- the identification of the concrete source test implementation with the
-- GammaMellinLayer.Test selected by the same AnalyticSubstrate.
--
-- This owner makes that recovery executable.  A source-native action may be
-- authored on its actual implementation carrier SourceTest.  One propositional
-- equality SourceTest == canonical Mellin Test transports the action into the
-- existing H_A compiler.  Unlike earlier receipt-only interfaces, the spectral
-- shift below is carried as an actual typed equality for the SAME concrete
-- RiemannExplicitFormula.spectralZeroForm.
------------------------------------------------------------------------

transport : ∀ {A B : Set} → A ≡ B → A → B
transport refl x = x

sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

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

    -- Same-object payment: the source taper/function implementation is the
    -- literal canonical Mellin test carrier, not merely analogous/isomorphic.
    sourceTestIdentity : SourceTest ≡ MellinTest

    -- The target parameter is already fixed by compatibility to the canonical
    -- Weil scalar / analytic real carrier.
    modulateSource :
      Weil.WeilTestSpace.Scalar space → SourceTest → SourceTest

    -- Admissibility is stated on the exact eventual Weil object, after the two
    -- owned equality transports SourceTest -> MellinTest -> WeilTest.
    modulationPreservesCanonicalAdmissibility :
      (t : Weil.WeilTestSpace.Scalar space) →
      (f : SourceTest) →
      Weil.WeilTestSpace.admissible space
        (MellinAction.mellinToWeil {compat = compat}
          (transport sourceTestIdentity f)) →
      Weil.WeilTestSpace.admissible space
        (MellinAction.mellinToWeil {compat = compat}
          (transport sourceTestIdentity (modulateSource t f)))

    -- The source may package its shift response in its own coordinates, but the
    -- theorem must identify the actual spectralZeroForm of THIS formula.
    shiftedSpectralResponse :
      Weil.WeilTestSpace.Scalar space → SourceTest →
      Weil.WeilTestSpace.Scalar space

    sourceSpectralShiftLaw :
      (t : Weil.WeilTestSpace.Scalar space) →
      (f : SourceTest) →
      Explicit.RiemannExplicitFormula.spectralZeroForm formula
        (MellinAction.mellinToWeil {compat = compat}
          (transport sourceTestIdentity (modulateSource t f)))
      ≡ shiftedSpectralResponse t f

    -- H_X agreement remains a separate same-action seam; the shift theorem
    -- itself is now proof-bearing rather than represented only by Set metadata.
    targetCharacterActionUsesCanonicalHX : Set
    sourceReference : String

open SourceNativePhiHatModulation public

sourceToMellin :
  ∀ {analytic space formula compat} →
  (R : SourceNativePhiHatModulation analytic space formula compat) →
  SourceTest R →
  Analytic.GammaMellinLayer.Test
    (Analytic.AnalyticSubstrate.gammaMellin analytic)
sourceToMellin R = transport (sourceTestIdentity R)

mellinToSource :
  ∀ {analytic space formula compat} →
  (R : SourceNativePhiHatModulation analytic space formula compat) →
  Analytic.GammaMellinLayer.Test
    (Analytic.AnalyticSubstrate.gammaMellin analytic) →
  SourceTest R
mellinToSource R = transport (sym (sourceTestIdentity R))

sourceTransportedMellinAction :
  ∀ {analytic space formula compat} →
  SourceNativePhiHatModulation analytic space formula compat →
  Weil.WeilTestSpace.Scalar space →
  Analytic.GammaMellinLayer.Test
    (Analytic.AnalyticSubstrate.gammaMellin analytic) →
  Analytic.GammaMellinLayer.Test
    (Analytic.AnalyticSubstrate.gammaMellin analytic)
sourceTransportedMellinAction R t f =
  sourceToMellin R (modulateSource R t (mellinToSource R f))

sourceTransportedPreservesAdmissibility :
  ∀ {analytic space formula compat} →
  (R : SourceNativePhiHatModulation analytic space formula compat) →
  (t : Weil.WeilTestSpace.Scalar space) →
  (f : Analytic.GammaMellinLayer.Test
    (Analytic.AnalyticSubstrate.gammaMellin analytic)) →
  Weil.WeilTestSpace.admissible space
    (MellinAction.mellinToWeil {compat = compat} f) →
  Weil.WeilTestSpace.admissible space
    (MellinAction.mellinToWeil {compat = compat}
      (sourceTransportedMellinAction R t f))
sourceTransportedPreservesAdmissibility {compat = compat} R t f admissibleF
  with sourceTestIdentity R
... | refl = modulationPreservesCanonicalAdmissibility R t f admissibleF

------------------------------------------------------------------------
-- Proof-bearing shift survives the same-object transports.
------------------------------------------------------------------------

sourceTransportedSpectralShift :
  ∀ {analytic space formula compat} →
  (R : SourceNativePhiHatModulation analytic space formula compat) →
  (t : Weil.WeilTestSpace.Scalar space) →
  (f : Analytic.GammaMellinLayer.Test
    (Analytic.AnalyticSubstrate.gammaMellin analytic)) →
  Explicit.RiemannExplicitFormula.spectralZeroForm formula
    (MellinAction.mellinToWeil {compat = compat}
      (sourceTransportedMellinAction R t f))
  ≡ shiftedSpectralResponse R t (mellinToSource R f)
sourceTransportedSpectralShift {compat = compat} R t f
  with sourceTestIdentity R
... | refl = sourceSpectralShiftLaw R t f

------------------------------------------------------------------------
-- Compile into the existing canonical Mellin action.  The older H_A interface
-- stores shift surfaces as Set-valued metadata; the stronger typed theorem is
-- retained above and can be consumed directly by later strengthened compilers.
------------------------------------------------------------------------

toCanonicalMellinTestAction :
  ∀ {analytic space formula compat} →
  SourceNativePhiHatModulation analytic space formula compat →
  MellinAction.CanonicalMellinTestAction analytic space formula compat
toCanonicalMellinTestAction {space = space} {formula = formula} R = record
  { MellinAction.modulateMellin = sourceTransportedMellinAction R
  ; MellinAction.preservesTransportedWeilAdmissibility =
      sourceTransportedPreservesAdmissibility R
  ; MellinAction.targetCharacterActionUsesCanonicalHX =
      targetCharacterActionUsesCanonicalHX R
  ; MellinAction.spectralShiftLawForSameFormula =
      (t : Weil.WeilTestSpace.Scalar space) →
      (f : Analytic.GammaMellinLayer.Test
        (Analytic.AnalyticSubstrate.gammaMellin _)) →
      Explicit.RiemannExplicitFormula.spectralZeroForm formula
        (MellinAction.mellinToWeil
          (sourceTransportedMellinAction R t f))
      ≡ shiftedSpectralResponse R t (mellinToSource R f)
  ; MellinAction.shiftedResponseIsConcreteFormulaSpectralResponse = ⊤
  ; MellinAction.transformShiftUsesCanonicalWeilTransform = ⊤
  ; MellinAction.producerReference = sourceReference R
  }

------------------------------------------------------------------------
-- BIDI search pruning after source-native realization.
------------------------------------------------------------------------

data SourceNativeSearchAction : Set where
  rebuildGenericFourierTheory
  reuseFiniteC3FourierAsRiemannTest
  recoverConcreteSourceTestImplementation
  identifySourceTestWithCanonicalMellinTest
  recoverSourceCharacterMultiplicationAction
  retainTypedSameFormulaShift
  continueThroughMellinToWeilCompiler
  : SourceNativeSearchAction

SourceNativeRelevant : SourceNativeSearchAction → Set
SourceNativeRelevant rebuildGenericFourierTheory = ⊥
SourceNativeRelevant reuseFiniteC3FourierAsRiemannTest = ⊥
SourceNativeRelevant recoverConcreteSourceTestImplementation = ⊤
SourceNativeRelevant identifySourceTestWithCanonicalMellinTest = ⊤
SourceNativeRelevant recoverSourceCharacterMultiplicationAction = ⊤
SourceNativeRelevant retainTypedSameFormulaShift = ⊤
SourceNativeRelevant continueThroughMellinToWeilCompiler = ⊤

rebuildGenericFourierTheoryPruned :
  SourceNativeRelevant rebuildGenericFourierTheory → ⊥
rebuildGenericFourierTheoryPruned x = x

finiteC3AsRiemannTestPruned :
  SourceNativeRelevant reuseFiniteC3FourierAsRiemannTest → ⊥
finiteC3AsRiemannTestPruned x = x

record SourceNativePhiHatModulationBoundary : Set where
  constructor source-native-phihat-modulation-boundary
  field
    sourceComplexPhiHatAndTaperInfrastructureAlreadyOwned : Bool
    sourceComplexPhiHatAndTaperInfrastructureAlreadyOwnedIsTrue :
      sourceComplexPhiHatAndTaperInfrastructureAlreadyOwned ≡ true

    sourceTestMustBeMerelyIsomorphicToCanonicalMellinTest : Bool
    sourceTestMustBeMerelyIsomorphicToCanonicalMellinTestIsFalse :
      sourceTestMustBeMerelyIsomorphicToCanonicalMellinTest ≡ false

    exactSourceTestEqualityIsSufficientForActionTransport : Bool
    exactSourceTestEqualityIsSufficientForActionTransportIsTrue :
      exactSourceTestEqualityIsSufficientForActionTransport ≡ true

    sameFormulaSpectralShiftIsProofBearingHere : Bool
    sameFormulaSpectralShiftIsProofBearingHereIsTrue :
      sameFormulaSpectralShiftIsProofBearingHere ≡ true

    carrierTransportAloneProvesShift : Bool
    carrierTransportAloneProvesShiftIsFalse :
      carrierTransportAloneProvesShift ≡ false

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
    false refl
    false refl
