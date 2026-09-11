module DASHI.Physics.Chemistry.AtomicPeriodicTable369Validation where

open import DASHI.Core.Prelude

import DASHI.Physics.Chemistry.AtomicPeriodicTable369GenerativeExact as G
import DASHI.Physics.Chemistry.AtomicPeriodicTable369ProvenanceSnowballExact as P
import DASHI.Physics.Chemistry.AtomicPeriodicTable369ChronologyStatusExact as C
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AttributionLedgerExact as A
import DASHI.Physics.Chemistry.AtomicPeriodicTable369CrossRepoRegressionExact as X
import DASHI.Physics.Chemistry.AtomicPeriodicTable369CrossRepoAttributionExact as XA
import DASHI.Physics.Chemistry.AtomicPeriodicTable369DashiQFirstPublicSourceExact as DQ
import DASHI.Physics.Foundations.AtomicValenceFermionBridgeExact as V
import DASHI.Promotion.ChemistryFiniteRuleTargets as F

------------------------------------------------------------------------
-- Focused validation root.  Importing this module forces the generative
-- formalism, provenance/snowball companion, chronology/status ledger,
-- DOI/QID/primary/Dewey attribution ledgers, first-public dashiQ source, and
-- cross-repository regression ledger through the Agda checker when this file
-- is actually checked.
--
-- The existence of this file is not itself a typecheck receipt.  See the
-- chronology/status owner for the distinction between authored source and a
-- recorded checker run.

capacityRegression :
  G.subshellCapacity 0 ≡ 2
  × G.subshellCapacity 1 ≡ 6
  × G.subshellCapacity 2 ≡ 10
capacityRegression =
  G.sCapacity , (G.pCapacity , G.dCapacity)

shellCapacityRegression :
  G.shellCapacity 1 ≡ 2
  × G.shellCapacity 2 ≡ 8
  × G.shellCapacity 3 ≡ 18
shellCapacityRegression =
  G.firstShellCapacity , (G.secondShellCapacity , G.thirdShellCapacity)

historicalClosureCoordinateRegression :
  G.historicalClosureZ G.heliumLikeClosure ≡ 2
  × G.historicalClosureZ G.neonLikeClosure ≡ 10
  × G.historicalClosureZ G.argonLikeClosure ≡ 18
historicalClosureCoordinateRegression =
  G.heliumLikeZ , (G.neonLikeZ , G.argonLikeZ)

closedValenceRegression :
  G.valenceClass V.closedValencePattern ≡ V.nobleLikeClass
closedValenceRegression = G.closedValenceIsNobleLike

nonPromotionRegression :
  G.Atomic369NonPromotionBoundary.triadicCardinalityDerivesOrbitalQuantumNumbers
    G.canonicalAtomic369NonPromotionBoundary
  ≡ false
nonPromotionRegression = refl

snowballRegression :
  P.SnowballDiscipline.acquisitionMayBeOutOfDependencyOrder
    P.canonicalSnowballDiscipline
  ≡ true
  ×
  P.SnowballDiscipline.retainedLaterEvidencePaysEarlierMissingDependency
    P.canonicalSnowballDiscipline
  ≡ false
snowballRegression = refl , refl

publicationDisciplineRegression :
  C.PublicationDiscipline.repoCommitEqualsExternalPublication
    C.canonicalPublicationDiscipline
  ≡ false
  ×
  C.PublicationDiscipline.historicalConversationDateEqualsPublicationDate
    C.canonicalPublicationDiscipline
  ≡ false
publicationDisciplineRegression = refl , refl

attributionDisciplineRegression :
  A.AttributionDiscipline.qidImpliesPrimaryAuthority
    A.canonicalAttributionDiscipline
  ≡ false
  ×
  A.AttributionDiscipline.deweyImpliesScientificTruth
    A.canonicalAttributionDiscipline
  ≡ false
  ×
  A.AttributionDiscipline.sourcePresenceImpliesTypechecked
    A.canonicalAttributionDiscipline
  ≡ false
attributionDisciplineRegression = refl , (refl , refl)

finiteHistoricalTargetRegression :
  X.finiteTargetCount ≡ 10
  ×
  F.occupationElectronCount
    (F.finiteAufbauOccupation F.hydrogen) ≡ 1
  ×
  F.occupationElectronCount
    (F.finiteAufbauOccupation F.neon) ≡ 10
finiteHistoricalTargetRegression =
  X.finiteTargetCountIs10 ,
  (X.hydrogenTargetElectronCountIs1 , X.neonTargetElectronCountIs10)

crossRepoNonCollapseRegression :
  X.CrossRepoRegressionDiscipline.full118VisualizationEqualsGenerativeDerivation
    X.canonicalCrossRepoRegressionDiscipline
  ≡ false
  ×
  X.CrossRepoRegressionDiscipline.firstTenFormalTargetsEqualFullPeriodicTable
    X.canonicalCrossRepoRegressionDiscipline
  ≡ false
  ×
  X.CrossRepoRegressionDiscipline.genericConstructorEqualsEmpiricalRecovery
    X.canonicalCrossRepoRegressionDiscipline
  ≡ false
crossRepoNonCollapseRegression = refl , (refl , refl)

crossRepoAttributionRegression :
  XA.CrossRepoAttributionWeld.qidPromotesGenerativeDerivation
    XA.canonicalCrossRepoAttributionWeld
  ≡ false
  ×
  XA.CrossRepoAttributionWeld.tableWideBreadthPromotesPhysicalRecovery
    XA.canonicalCrossRepoAttributionWeld
  ≡ false
crossRepoAttributionRegression = refl , refl

firstPublicSourceRegression :
  DQ.FirstPublicSourceChronology.periodicProgrammePredatesDashiAgdaInit
    DQ.canonicalFirstPublicSourceChronology
  ≡ true
  ×
  DQ.FirstPublicSourceBoundary.publicRepoStatementEqualsPeerReviewedPublication
    DQ.canonicalFirstPublicSourceBoundary
  ≡ false
  ×
  DQ.FirstPublicSourceBoundary.historicalWeDidEqualsKernelCheckedTheorem
    DQ.canonicalFirstPublicSourceBoundary
  ≡ false
firstPublicSourceRegression = refl , (refl , refl)
