{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanLiteralStressCompletionRound115Exact where

------------------------------------------------------------------------
-- ROUND115: ONE LITERAL STRESS COORDINATE COMPILES ALL DOWNSTREAM MACHINERY
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (_≤_; _*_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanLiteralStressCoordinateRound114Exact as R114
import DASHI.Physics.YangMills.BalabanStressSameObjectProvenanceRound110Exact as R110
import DASHI.Physics.YangMills.BalabanStressShellEnergyToHilbertRound112Exact as R112
import DASHI.Physics.YangMills.BalabanSameFamilyStressCauchySchwingerRound109Exact as R109
import DASHI.Physics.YangMills.BalabanContinuumScaleLocalObservableCauchyExact as Scale
import DASHI.Physics.YangMills.BalabanTopDownSummableRGIncrementExact as Sum
import DASHI.Physics.YangMills.BalabanCMP119CompatibleLocalExpectationFlowExact as Source
import DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact as Geo
import DASHI.Physics.YangMills.BalabanMarkedSourceCoefficientEnergyHilbertCompilerExact as Hilbert
import DASHI.Physics.YangMills.BalabanMarkedSourceNuclearCompositeFieldExact as Marked
import DASHI.Physics.YangMills.BalabanMarkedSourceCompositeStressFieldExact as StressMarked
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top

record CompiledLiteralStressCompletion
    {C : Top.LiteralYangMillsCarriers}
    {S : Top.LiteralYangMillsSemantics C}
    {Y : Top.LiteralYangMillsConstruction C S}
    {group : Top.CompactSimpleGroup C}
    (coordinate : R114.LiteralStressCoordinate Y group) : Set₁ where
  field
    provenance : R110.LiteralStressSameObjectProvenance Y group
    coefficientShell : R112.LiteralStressCoefficientShellIdentification
open CompiledLiteralStressCompletion public

compileLiteralStressCoordinate :
  ∀ {C S}
    {Y : Top.LiteralYangMillsConstruction C S}
    {group : Top.CompactSimpleGroup C}
    (coordinate : R114.LiteralStressCoordinate Y group) →
  CompiledLiteralStressCompletion coordinate
compileLiteralStressCoordinate coordinate = record
  { provenance = R114.asSameObjectProvenance coordinate
  ; coefficientShell = R114.asStressCoefficientShellIdentification coordinate
  }

compiledStressCauchyModulus :
  ∀ {C S}
    {Y : Top.LiteralYangMillsConstruction C S}
    {group : Top.CompactSimpleGroup C}
    (coordinate : R114.LiteralStressCoordinate Y group) →
  ∀ start count →
  R109.stressDifference
    (R110.sourceCauchy (provenance (compileLiteralStressCoordinate coordinate)))
    start count
  ≤ Scale.coefficient
      (Sum.commonMajorant
        (Source.sourceCompatibleSameFamilyIncrement
          (R109.source
            (R110.sourceCauchy
              (provenance (compileLiteralStressCoordinate coordinate))))
          (R109.smallHistory
            (R110.sourceCauchy
              (provenance (compileLiteralStressCoordinate coordinate))))
          (R109.stressInsertion
            (R110.sourceCauchy
              (provenance (compileLiteralStressCoordinate coordinate))))))
      * (Geo.half * Geo.halfPower start)
compiledStressCauchyModulus coordinate =
  R110.stressDifferenceCauchyModulus
    (provenance (compileLiteralStressCoordinate coordinate))

compiledStressFiniteHilbertData :
  ∀ {C S}
    {Y : Top.LiteralYangMillsConstruction C S}
    {group : Top.CompactSimpleGroup C}
    (coordinate : R114.LiteralStressCoordinate Y group) →
  Nat → Hilbert.FiniteMarkedSourceHilbertData
compiledStressFiniteHilbertData coordinate =
  R112.stressFiniteHilbertData
    (coefficientShell (compileLiteralStressCoordinate coordinate))

compiledStressCompletionIsLiteralClayStressDerivative :
  ∀ {C S}
    {Y : Top.LiteralYangMillsConstruction C S}
    {group : Top.CompactSimpleGroup C}
    (coordinate : R114.LiteralStressCoordinate Y group) →
  let selectedCompletion =
        R114.asMarkedCompletion coordinate (R114.coordinate coordinate)
      sources = R109.completedSources selectedCompletion
      stressData = StressMarked.stressData sources
  in
  R114.cmp119CompletedResponse coordinate
  ≡ Marked.sourceDerivative stressData (Top.stressTensor Y group)
compiledStressCompletionIsLiteralClayStressDerivative coordinate =
  R114.sameCoordinateCompletedResponseIsLiteralStressDerivative coordinate

literalStressCompletionCompilerLevel : ProofLevel
literalStressCompletionCompilerLevel = machineChecked

literalStressCoordinatePhysicalInstantiationRound115Level : ProofLevel
literalStressCoordinatePhysicalInstantiationRound115Level = conditional
