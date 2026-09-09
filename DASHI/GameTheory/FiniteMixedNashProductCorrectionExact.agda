module DASHI.GameTheory.FiniteMixedNashProductCorrectionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.GameTheory.StrategicInteractionCoreExact as Game
import DASHI.GameTheory.FiniteMixedStrategyExpectedUtilityExact as Mixed
import DASHI.Core.ProofDebtRouterExact as Debt

------------------------------------------------------------------------
-- MIXED-NASH PRODUCT-LAW CORRECTION
--
-- The earlier FiniteMixedNashEquilibrium carrier is a useful finite joint-law
-- unilateral-stability surface, but an arbitrary normalized law on complete
-- profiles is not by itself the independent product of player mixed strategies
-- used by the standard finite mixed-Nash theorem.  This owner preserves the old
-- carrier and adds the missing source-alignment coordinates explicitly.
------------------------------------------------------------------------

record FiniteNormalFormReceipt (G : Game.StrategicGame) : Set₁ where
  constructor finite-normal-form-receipt
  field
    playerEnumeration : List (Game.Player G)
    strategyEnumeration :
      (player : Game.Player G) → List (Game.Strategy G player)

    PlayerEnumerationComplete : Set
    playerEnumerationComplete : PlayerEnumerationComplete

    StrategyEnumerationComplete : Set
    strategyEnumerationComplete : StrategyEnumerationComplete

    finiteGameReference : String

open FiniteNormalFormReceipt public

record IndependentProductProfileReceipt
    (G : Game.StrategicGame)
    (law : Mixed.FiniteMixedProfileLaw G) : Set₁ where
  constructor independent-product-profile-receipt
  field
    playerMarginal :
      (player : Game.Player G) → Mixed.FiniteMixedStrategy G player

    ProductProfileLawSemantics : Set
    productProfileLawSemantics : ProductProfileLawSemantics

    LawEqualsIndependentProduct : Set
    lawEqualsIndependentProduct : LawEqualsIndependentProduct

    independenceReference : String
    productConstructionReference : String

open IndependentProductProfileReceipt public

record StandardFiniteMixedNashEquilibrium
    (G : Game.StrategicGame)
    (U : Mixed.FiniteExpectedUtilitySurface G) : Set₁ where
  constructor standard-finite-mixed-nash-equilibrium
  field
    finiteNormalForm : FiniteNormalFormReceipt G

    jointStability : Mixed.FiniteMixedNashEquilibrium G U

    independentProduct :
      IndependentProductProfileReceipt G
        (Mixed.FiniteMixedNashEquilibrium.profileLaw jointStability)

    sourceAlignmentReference : String

open StandardFiniteMixedNashEquilibrium public

------------------------------------------------------------------------
-- The consumer-minimal theorem target.  The producer-useful route may expose
-- simplex/fixed-point machinery, but the downstream consumer only needs an
-- inhabitant of the corrected equilibrium object for the exact finite game.
------------------------------------------------------------------------

FiniteMixedNashExistenceConsumer :
  (G : Game.StrategicGame) →
  Mixed.FiniteExpectedUtilitySurface G → Set₁
FiniteMixedNashExistenceConsumer = StandardFiniteMixedNashEquilibrium

record FiniteMixedNashExistenceSourceDemand
    (G : Game.StrategicGame)
    (U : Mixed.FiniteExpectedUtilitySurface G) : Set₁ where
  constructor finite-mixed-nash-existence-source-demand
  field
    finiteNormalForm : FiniteNormalFormReceipt G
    exactConsumer : Set₁
    exactConsumerIsCorrectedMixedNash :
      exactConsumer ≡ FiniteMixedNashExistenceConsumer G U

    fixedPointProducerReference : String
    simplexRealisationReference : String
    sourceTheoremReference : String

open FiniteMixedNashExistenceSourceDemand public

finiteMixedNashExistenceDebt : Debt.ProofDebtRoutingReceipt
finiteMixedNashExistenceDebt =
  Debt.proof-debt-routing-receipt
    Debt.deductiveTheorem
    Debt.sourceEstablished
    Debt.notTranscribed
    Debt.uncertified
    Debt.sourceOnly
    Debt.transcriptionDebt
    refl

finiteMixedNashExistenceNextAction :
  Debt.scheduleAction
    (Debt.routedDebt finiteMixedNashExistenceDebt)
    (Debt.statementStatus finiteMixedNashExistenceDebt)
    Debt.constrained32GB
    Debt.heavyReplay
  ≡ Debt.auditTranscription
finiteMixedNashExistenceNextAction = refl

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data NormalizedJointLawMeansIndependentProductPermission : Set where

data JointLawStabilityMeansStandardMixedNashPermission : Set where

data FiniteCarrierMeansNashExistencePermission : Set where

data FixedPointWordMeansBrouwerKakutaniPermission : Set where

data SourceTheoremMeansExactGameInstantiatedPermission : Set where

normalizedJointLawDoesNotProveIndependence :
  NormalizedJointLawMeansIndependentProductPermission → ⊥
normalizedJointLawDoesNotProveIndependence ()

jointLawStabilityDoesNotAutomaticallyGiveStandardMixedNash :
  JointLawStabilityMeansStandardMixedNashPermission → ⊥
jointLawStabilityDoesNotAutomaticallyGiveStandardMixedNash ()

finiteCarrierDoesNotProveNashExistence :
  FiniteCarrierMeansNashExistencePermission → ⊥
finiteCarrierDoesNotProveNashExistence ()

unrelatedFixedPointDoesNotPayNashFixedPointTheorem :
  FixedPointWordMeansBrouwerKakutaniPermission → ⊥
unrelatedFixedPointDoesNotPayNashFixedPointTheorem ()

sourceTheoremDoesNotInstantiateExactGameByCitation :
  SourceTheoremMeansExactGameInstantiatedPermission → ⊥
sourceTheoremDoesNotInstantiateExactGameByCitation ()

record FiniteMixedNashCorrectionBoundary : Set where
  constructor finite-mixed-nash-correction-boundary
  field
    oldJointLawCarrierRetained : Bool
    normalizedJointLawTreatedAsIndependentByDefinition : Bool
    independentProductReceiptRequired : Bool
    finiteNormalFormReceiptRequired : Bool
    standardExistenceTheoremAlreadyCertified : Bool
    existenceRoutesToTranscriptionAudit : Bool

canonicalFiniteMixedNashCorrectionBoundary : FiniteMixedNashCorrectionBoundary
canonicalFiniteMixedNashCorrectionBoundary =
  finite-mixed-nash-correction-boundary
    true false true true false true
