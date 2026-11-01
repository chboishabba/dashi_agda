module DASHI.ComputerScience.RSA260BidiProductionGeneratorResidualAdapterExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.ComputerScience.RSA260CADOBlockWiedemannArtifactSchemaSnowballExact as CADO
import DASHI.ComputerScience.RSA260BidiProductionAStarDiagnosticAdapterExact as AStar
import DASHI.ComputerScience.RSA260BidiAStarCoefficientResidualReopeningExact as Reopening

------------------------------------------------------------------------
-- RSA-260 BIDI PRODUCTION GENERATOR-RESIDUAL ADAPTER
--
-- The synthetic collision search showed that scalar/rank summaries do not
-- determine recovered generator identity.  The downstream interface therefore
-- retains generator coefficient data as a relative-fine residual.
--
-- CADO exposes two useful production artifact routes:
--
--   A<n1>-<n2>.<j1>-<j2>   projected Krylov sequence
--   F.sols<s1>-<s2>.<j1>-<j2>   lingen generator artifact
--
-- They are not equivalent acquisition states.  A* must first be converted by
-- an executed same-object sequence->generator derivation; F.sols* can provide
-- generator bytes directly once custody/format identity is authenticated.
-- Both routes compile to the same downstream generator-residual capability.
------------------------------------------------------------------------

cadoArtifactSchema : CADO.CADOBlockWiedemannArtifactSchema
cadoArtifactSchema = CADO.currentCADOBlockWiedemannArtifactSchema

astarPattern : String
astarPattern = CADO.krylovSequencePattern cadoArtifactSchema

fsolsPattern : String
fsolsPattern = CADO.generatorPattern cadoArtifactSchema

astarBoundary : AStar.ProductionAStarAdapterBoundary
astarBoundary = AStar.canonicalProductionAStarAdapterBoundary

reopeningBoundary : Reopening.CoefficientResidualReopeningBoundary
reopeningBoundary = Reopening.canonicalCoefficientResidualReopeningBoundary

data GeneratorResidualRoute : Set where
  projectedSequenceAStar : GeneratorResidualRoute
  lingenGeneratorFSols : GeneratorResidualRoute

------------------------------------------------------------------------
-- A* route: sequence custody is necessary but not sufficient.  The actual
-- sequence->generator derivation must execute on the same-object bytes.
------------------------------------------------------------------------

record AStarGeneratorDerivationReceipt
    (sequence : AStar.SameObjectProjectedSequenceCustody) : Set where
  constructor astar-generator-derivation-receipt
  field
    derivationImplementationReference : String
    sameObjectSequenceDecoded : Bool
    sharedMatrixGeneratorRecovered : Bool
    recurrenceValidatedAgainstSequence : Bool
    generatorCoefficientBytesAvailable : Bool

    decodePaid : sameObjectSequenceDecoded ≡ true
    recoveryPaid : sharedMatrixGeneratorRecovered ≡ true
    recurrenceValidationPaid : recurrenceValidatedAgainstSequence ≡ true
    coefficientBytesPaid : generatorCoefficientBytesAvailable ≡ true
open AStarGeneratorDerivationReceipt public

------------------------------------------------------------------------
-- F.sols route: direct generator artifact custody still requires same-object
-- authentication and an exact decode/format receipt.
------------------------------------------------------------------------

record SameObjectFSolsCustody : Set where
  constructor same-object-fsols-custody
  field
    artifactPath : String
    sameObjectRSA260Identity : Bool
    generatorBytesAvailable : Bool
    sourceObjectIdentityBound : Bool
    generatorFormatDecoded : Bool

    sameObjectIdentityPaid : sameObjectRSA260Identity ≡ true
    generatorBytesPaid : generatorBytesAvailable ≡ true
    sourceObjectBindingPaid : sourceObjectIdentityBound ≡ true
    formatDecodePaid : generatorFormatDecoded ≡ true
open SameObjectFSolsCustody public

------------------------------------------------------------------------
-- Unified downstream capability.
------------------------------------------------------------------------

record GeneratorCoefficientResidualCustody : Set where
  constructor generator-coefficient-residual-custody
  field
    route : GeneratorResidualRoute
    sourceArtifactPath : String
    sameObjectIdentityPaid : Bool
    coefficientBytesAvailable : Bool
    coefficientInterpretationPaid : Bool

    sameObjectPaid : sameObjectIdentityPaid ≡ true
    bytesPaid : coefficientBytesAvailable ≡ true
    interpretationPaid : coefficientInterpretationPaid ≡ true
open GeneratorCoefficientResidualCustody public

astarDerivationPaysGeneratorResidual :
  (sequence : AStar.SameObjectProjectedSequenceCustody) →
  AStarGeneratorDerivationReceipt sequence →
  GeneratorCoefficientResidualCustody
astarDerivationPaysGeneratorResidual sequence derivation =
  generator-coefficient-residual-custody
    projectedSequenceAStar
    (AStar.artifactPath sequence)
    true true true
    refl refl refl

fsolsCustodyPaysGeneratorResidual :
  SameObjectFSolsCustody → GeneratorCoefficientResidualCustody
fsolsCustodyPaysGeneratorResidual custody =
  generator-coefficient-residual-custody
    lingenGeneratorFSols
    (artifactPath custody)
    true true true
    refl refl refl

record GeneratorResidualConsumerAdmission
    (custody : GeneratorCoefficientResidualCustody) : Set where
  constructor generator-residual-consumer-admission
  field
    generatorIdentityConsumerAdmitted : Bool
    coarseFineReopeningConsumerAdmitted : Bool
    compareAgainstSyntheticGeneratorPortfolioAdmitted : Bool

    generatorIdentityPaid : generatorIdentityConsumerAdmitted ≡ true
    reopeningPaid : coarseFineReopeningConsumerAdmitted ≡ true
    portfolioComparisonPaid : compareAgainstSyntheticGeneratorPortfolioAdmitted ≡ true
open GeneratorResidualConsumerAdmission public

generatorResidualCustodyPaysConsumers :
  (custody : GeneratorCoefficientResidualCustody) →
  GeneratorResidualConsumerAdmission custody
generatorResidualCustodyPaysConsumers custody =
  generator-residual-consumer-admission
    true true true
    refl refl refl

------------------------------------------------------------------------
-- Current production state remains unpaid.
------------------------------------------------------------------------

record CurrentProductionGeneratorResidualState : Set where
  constructor current-production-generator-residual-state
  field
    sameObjectAStarBytesPaid : Bool
    sameObjectAStarToGeneratorDerivationPaid : Bool
    sameObjectFSolsBytesPaid : Bool
    sameObjectFSolsFormatDecoded : Bool
    unifiedGeneratorResidualCustodyPaid : Bool
open CurrentProductionGeneratorResidualState public

currentProductionGeneratorResidualState : CurrentProductionGeneratorResidualState
currentProductionGeneratorResidualState =
  current-production-generator-residual-state
    false false false false false

------------------------------------------------------------------------
-- Boundary and global roadmap.
------------------------------------------------------------------------

record ProductionGeneratorResidualBoundary : Set where
  constructor production-generator-residual-boundary
  field
    cadoAStarSchemaPaid : Bool
    cadoFSolsSchemaPaid : Bool
    astarRequiresExecutedGeneratorDerivation : Bool
    fsolsCanSupplyDirectGeneratorResidual : Bool
    bothRoutesCompileToCommonResidualInterface : Bool
    scalarRankPacketStillRetainedAsCoarseCoordinate : Bool
    coefficientResidualRequiredForGeneratorIdentityConsumer : Bool
    currentAStarRoutePaid : Bool
    currentFSolsRoutePaid : Bool
    currentUnifiedResidualPaid : Bool
    adapterCreatesMissingArtifactBytes : Bool
    commonInterfaceProvesRoutesByteIdentical : Bool
open ProductionGeneratorResidualBoundary public

canonicalProductionGeneratorResidualBoundary : ProductionGeneratorResidualBoundary
canonicalProductionGeneratorResidualBoundary =
  production-generator-residual-boundary
    true
    true
    true
    true
    true
    true
    true
    false
    false
    false
    false
    false

data ProductionGeneratorResidualResidual : Set where
  acquireSameObjectProjectedAStarBytes : ProductionGeneratorResidualResidual
  orAcquireSameObjectFSolsBytes : ProductionGeneratorResidualResidual
  authenticateArtifactSameObjectIdentity : ProductionGeneratorResidualResidual
  executeAStarToGeneratorDerivationIfAStarRoute : ProductionGeneratorResidualResidual
  decodeFSolsGeneratorFormatIfFSolsRoute : ProductionGeneratorResidualResidual
  instantiateGeneratorCoefficientResidual : ProductionGeneratorResidualResidual
  compareProductionResidualAgainstFrozenSyntheticPortfolio : ProductionGeneratorResidualResidual
  continueKernelRecoveryTowardFactorCertificate : ProductionGeneratorResidualResidual

firstProductionGeneratorResidualResidual : ProductionGeneratorResidualResidual
firstProductionGeneratorResidualResidual = acquireSameObjectProjectedAStarBytes

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data AStarBytesAloneMeanGeneratorRecovered : Set where
data FSolsFilenameMeansSameObjectGenerator : Set where
data CommonResidualInterfaceMeansArtifactRoutesIdentical : Set where
data GeneratorResidualCustodyMeansFactorCertificate : Set where

astarBytesAloneDoNotCreateGenerator :
  AStarBytesAloneMeanGeneratorRecovered → ⊥
astarBytesAloneDoNotCreateGenerator ()

fsolsFilenameDoesNotCreateSameObjectGenerator :
  FSolsFilenameMeansSameObjectGenerator → ⊥
fsolsFilenameDoesNotCreateSameObjectGenerator ()

commonInterfaceDoesNotMakeRoutesIdentical :
  CommonResidualInterfaceMeansArtifactRoutesIdentical → ⊥
commonInterfaceDoesNotMakeRoutesIdentical ()

generatorResidualDoesNotCreateFactorCertificate :
  GeneratorResidualCustodyMeansFactorCertificate → ⊥
generatorResidualDoesNotCreateFactorCertificate ()
