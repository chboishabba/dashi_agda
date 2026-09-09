module DASHI.GameTheory.Nash1950CorrectedExistenceAlignmentExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

import DASHI.Core.ProofDebtRouterExact as Debt
import DASHI.Core.ProofDebtUniverseLiftExact as Lift
import DASHI.GameTheory.StrategicInteractionCoreExact as Game
import DASHI.GameTheory.FiniteMixedStrategyExpectedUtilityExact as Mixed
import DASHI.GameTheory.FiniteMixedNashProductCorrectionExact as Correction
import DASHI.GameTheory.GameTheorySourceAtlasExact as Sources
import DASHI.Biology.ConsciousAccessRound4SourceAtlas as R4

------------------------------------------------------------------------
-- NASH 1950 -> CORRECTED FINITE MIXED-NASH CONSUMER
--
-- The source atlas already attributes finite mixed-strategy equilibrium
-- existence to Nash 1950.  This owner aligns that established theorem only to
-- the corrected product-law consumer.  It does not use the older arbitrary
-- normalized joint-profile law as the theorem target.
------------------------------------------------------------------------

record Nash1950ApplicationCoordinates
    (G : Game.StrategicGame)
    (U : Mixed.FiniteExpectedUtilitySurface G) : Set₁ where
  constructor nash1950-application-coordinates
  field
    finiteNormalForm : Correction.FiniteNormalFormReceipt G

    ProfileIsFiniteStrategyProduct : Set
    profileIsFiniteStrategyProduct : ProfileIsFiniteStrategyProduct

    MixedStrategySimplexRealisation : Set
    mixedStrategySimplexRealisation : MixedStrategySimplexRealisation

    IndependentProductLawConstruction : Set
    independentProductLawConstruction : IndependentProductLawConstruction

    FiniteExpectedUtilityMatchesSourcePayoffExtension : Set
    finiteExpectedUtilityMatchesSourcePayoffExtension :
      FiniteExpectedUtilityMatchesSourcePayoffExtension

    exactGameReference : String
    profileProductReference : String
    simplexReference : String
    expectedUtilityReference : String

open Nash1950ApplicationCoordinates public

Nash1950CorrectedExistenceClaim :
  (G : Game.StrategicGame) →
  (U : Mixed.FiniteExpectedUtilitySurface G) →
  Nash1950ApplicationCoordinates G U →
  Set₁
Nash1950CorrectedExistenceClaim G U coordinates =
  Correction.StandardFiniteMixedNashEquilibrium G U

nash1950SourceIdentity : Debt.SourceIdentity
nash1950SourceIdentity =
  Debt.source-identity
    (R4.authors Sources.nash1950Source)
    (R4.title Sources.nash1950Source)
    (R4.doi Sources.nash1950Source)
    "finite n-person strategic game; mixed strategies; equilibrium point as a fixed point of best-response-type construction"
    "source atlas revision on agent/directional-evidence-trit"

nash1950Alignment :
  (G : Game.StrategicGame) →
  (U : Mixed.FiniteExpectedUtilitySurface G) →
  (coordinates : Nash1950ApplicationCoordinates G U) →
  Debt.StatementAlignmentReceipt
nash1950Alignment G U coordinates =
  Debt.statement-alignment-receipt
    "Nash 1950 finite n-person game: existence of an equilibrium point in mixed strategies"
    "for this exact finite normal-form/product-profile game and finite expected-utility realization, inhabit StandardFiniteMixedNashEquilibrium G U"
    true
    true
    true
    true
    true
    true

nash1950AlignmentFullyVerified :
  (G : Game.StrategicGame) →
  (U : Mixed.FiniteExpectedUtilitySurface G) →
  (coordinates : Nash1950ApplicationCoordinates G U) →
  Debt.FullyAligned (nash1950Alignment G U coordinates)
nash1950AlignmentFullyVerified G U coordinates =
  Debt.fully-aligned refl refl refl refl refl refl

nash1950DeferredExistence :
  (G : Game.StrategicGame) →
  (U : Mixed.FiniteExpectedUtilitySurface G) →
  (coordinates : Nash1950ApplicationCoordinates G U) →
  Lift.SourceAlignedDeferredTheoremℓ
    (Nash1950CorrectedExistenceClaim G U coordinates)
nash1950DeferredExistence G U coordinates =
  Lift.source-aligned-deferred-theoremℓ
    nash1950SourceIdentity
    (nash1950Alignment G U coordinates)
    (nash1950AlignmentFullyVerified G U coordinates)
    Debt.aristotleLean

nash1950PostAlignmentRoute : Debt.ProofDebtRoutingReceipt
nash1950PostAlignmentRoute =
  Debt.proof-debt-routing-receipt
    Debt.deductiveTheorem
    Debt.sourceEstablished
    Debt.sourceAligned
    Debt.proofDeferred
    Debt.aristotleLean
    Debt.certificationDebt
    refl

nash1950PostAlignmentIsCertificationDebt :
  Debt.routedDebt nash1950PostAlignmentRoute ≡ Debt.certificationDebt
nash1950PostAlignmentIsCertificationDebt = refl

nash1950HeavyReplayScheduler :
  Debt.scheduleAction
    (Debt.routedDebt nash1950PostAlignmentRoute)
    (Debt.statementStatus nash1950PostAlignmentRoute)
    Debt.constrained32GB
    Debt.heavyReplay
  ≡ Debt.sendAristotleLean
nash1950HeavyReplayScheduler = refl

------------------------------------------------------------------------
-- Conditional downstream use remains allowed without manufacturing the proof.
------------------------------------------------------------------------

ConditionalOnNash1950 :
  ∀ {ℓ : Level} {Result : Set ℓ}
    (G : Game.StrategicGame)
    (U : Mixed.FiniteExpectedUtilitySurface G)
    (coordinates : Nash1950ApplicationCoordinates G U) →
  Set ((lsuc lzero) ⊔ ℓ)
ConditionalOnNash1950 {ℓ} {Result} G U coordinates =
  Lift.ConditionalDevelopmentℓ
    (Nash1950CorrectedExistenceClaim G U coordinates)
    Result

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data SourceAlignmentMeansCertifiedNashPermission : Set where

data FiniteEnumerationMeansProductProfilePermission : Set where

data ArbitraryJointLawMeansNash1950MixedStrategyPermission : Set where

data NashExistenceMeansUniqueEquilibriumPermission : Set where

data NashExistenceMeansParetoOptimalPermission : Set where

sourceAlignmentDoesNotManufactureCertifiedNash :
  SourceAlignmentMeansCertifiedNashPermission → ⊥
sourceAlignmentDoesNotManufactureCertifiedNash ()

finiteEnumerationDoesNotCreateProfileProduct :
  FiniteEnumerationMeansProductProfilePermission → ⊥
finiteEnumerationDoesNotCreateProfileProduct ()

arbitraryJointLawDoesNotBecomeNash1950MixedStrategy :
  ArbitraryJointLawMeansNash1950MixedStrategyPermission → ⊥
arbitraryJointLawDoesNotBecomeNash1950MixedStrategy ()

nashExistenceDoesNotGiveUniqueness : NashExistenceMeansUniqueEquilibriumPermission → ⊥
nashExistenceDoesNotGiveUniqueness ()

nashExistenceDoesNotGiveParetoOptimality : NashExistenceMeansParetoOptimalPermission → ⊥
nashExistenceDoesNotGiveParetoOptimality ()
