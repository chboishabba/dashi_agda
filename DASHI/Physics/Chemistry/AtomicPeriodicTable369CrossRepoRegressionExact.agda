module DASHI.Physics.Chemistry.AtomicPeriodicTable369CrossRepoRegressionExact where

open import DASHI.Core.Prelude

import DASHI.Promotion.ChemistryFiniteRuleTargets as Finite
import DASHI.Physics.Chemistry.AtomicPeriodicTable369GenerativeExact as Generative

------------------------------------------------------------------------
-- Cross-repository regression ledger.
--
-- This owner separates three historical objects that are easy to conflate:
--   (1) a full-118 periodic-table data visualization in dashifine;
--   (2) an exact first-ten finite shell-filling target in dashi_agda;
--   (3) the generic Nat-indexed atom constructor assembled in PR #886.
--
-- The first has breadth but reads an existing periodic-table CSV.  The second
-- has theorem-checkable finite occupations but covers only Z=1..10.  The third
-- is generic but leaves physical spectra/nuclear stability/empirical recovery
-- as typed obligations.  None is silently promoted into the others.

data CrossRepoEvidenceClass : Set where
  fullTableDataVisualization : CrossRepoEvidenceClass
  finiteFormalShellRegression : CrossRepoEvidenceClass
  genericGenerativeConstructor : CrossRepoEvidenceClass
  historicalReportedExecution : CrossRepoEvidenceClass

record CrossRepoRegressionReceipt : Set where
  constructor crossRepoRegressionReceipt
  field
    evidenceClass : CrossRepoEvidenceClass
    repository : String
    date : String
    locator : String
    carrier : String
    mechanicallyPresent : Bool
    executionReceiptLocated : Bool
    generativeFromFirstPrinciples : Bool
    physicalPromotion : Bool
    reading : String

open CrossRepoRegressionReceipt public

full118DashifineVisualization : CrossRepoRegressionReceipt
full118DashifineVisualization =
  crossRepoRegressionReceipt
    fullTableDataVisualization
    "chboishabba/dashifine"
    "authored 2026-02-21T02:00:50Z; committed 2026-03-05T04:02:00Z"
    "commit 9f1430ab7fe7c4ae480e93bc9f7549f4b758950e; bangerz.py and bangerz2.py"
    "existing PeriodicTableCSV.csv fields number/symbol/name/period/group/electronegativity/atomic_mass; script labels full 118 and animates every row"
    true
    false
    false
    false
    "This pays an early full-118 table-wide computational/visual surface. It consumes an existing periodic-table CSV and therefore does not pay a generative periodic-table theorem. The source contains an animation save path but this audit has not located the original generated GIF/run receipt."

finiteFirstTenFormalTarget : CrossRepoRegressionReceipt
finiteFirstTenFormalTarget =
  crossRepoRegressionReceipt
    finiteFormalShellRegression
    "chboishabba/dashi_agda"
    "2026-06-07T11:07:55Z"
    "commit 062ccb611c6d93fa7228a73d1557c8c934ea89d5; DASHI/Promotion/ChemistryFiniteRuleTargets.agda"
    "H through Ne with explicit 1s/2s/2p occupations plus finite Aufbau/Pauli/Hund target surfaces"
    true
    false
    false
    false
    "The commit adds the module from zero lines. Electron-count regressions for hydrogen and neon are definitional proofs, while measured constants, spectroscopy, thermochemistry and wet-lab authority are explicitly false."

generic369Constructor : CrossRepoRegressionReceipt
generic369Constructor =
  crossRepoRegressionReceipt
    genericGenerativeConstructor
    "chboishabba/dashi_agda"
    "2026-09-11"
    "draft PR #886; AtomicPeriodicTable369GenerativeExact.agda"
    "Nat-indexed GeneratedAtom / periodic-table recovery contract over existing 369, fermion, valence and recurrence owners"
    true
    false
    true
    false
    "The current formalism is generative at the type/interface level rather than a finite lookup. Its physical spectrum, nuclear stability, scale calibration, ionisation and empirical-observable obligations remain separate."

------------------------------------------------------------------------
-- Exact reuse of the June finite formal target.

finiteTargetCount : Nat
finiteTargetCount = Finite.elementCount Finite.canonicalChemistryFiniteRuleTargets

finiteTargetCountIs10 : finiteTargetCount ≡ 10
finiteTargetCountIs10 = Finite.canonicalFiniteElementCountIs10

hydrogenTargetElectronCountIs1 :
  Finite.occupationElectronCount
    (Finite.finiteAufbauOccupation Finite.hydrogen) ≡ 1
hydrogenTargetElectronCountIs1 = Finite.canonicalHydrogenElectronCountIs1

neonTargetElectronCountIs10 :
  Finite.occupationElectronCount
    (Finite.finiteAufbauOccupation Finite.neon) ≡ 10
neonTargetElectronCountIs10 = Finite.canonicalNeonElectronCountIs10

finiteTargetPhysicalPromotionIsFalse :
  Finite.promotesPhysicalChemistry Finite.canonicalChemistryFiniteRuleTargets
  ≡ false
finiteTargetPhysicalPromotionIsFalse =
  Finite.canonicalPhysicalChemistryPromotionIsFalse

------------------------------------------------------------------------
-- Non-collapse discipline.

record CrossRepoRegressionDiscipline : Set where
  constructor crossRepoRegressionDiscipline
  field
    full118VisualizationEqualsGenerativeDerivation : Bool
    full118VisualizationEqualsGenerativeDerivationIsFalse :
      full118VisualizationEqualsGenerativeDerivation ≡ false

    firstTenFormalTargetsEqualFullPeriodicTable : Bool
    firstTenFormalTargetsEqualFullPeriodicTableIsFalse :
      firstTenFormalTargetsEqualFullPeriodicTable ≡ false

    genericConstructorEqualsEmpiricalRecovery : Bool
    genericConstructorEqualsEmpiricalRecoveryIsFalse :
      genericConstructorEqualsEmpiricalRecovery ≡ false

    sourceSaveCallEqualsLocatedExecutionArtifact : Bool
    sourceSaveCallEqualsLocatedExecutionArtifactIsFalse :
      sourceSaveCallEqualsLocatedExecutionArtifact ≡ false

canonicalCrossRepoRegressionDiscipline : CrossRepoRegressionDiscipline
canonicalCrossRepoRegressionDiscipline =
  crossRepoRegressionDiscipline false refl false refl false refl false refl

------------------------------------------------------------------------
-- Current conclusion: breadth, finite exactness, and genericity are three
-- different axes and are now held simultaneously rather than rewritten into
-- one retrospective claim.

record CrossRepoAtomicDashboard : Set₁ where
  field
    full118Surface : CrossRepoRegressionReceipt
    finiteFormalSurface : CrossRepoRegressionReceipt
    generativeSurface : CrossRepoRegressionReceipt
    generativeStatement : Set₁
    generativeStatementIs :
      generativeStatement ≡ Generative.CanonicalAtomicPeriodicTableStatement
    discipline : CrossRepoRegressionDiscipline

canonicalCrossRepoAtomicDashboard : CrossRepoAtomicDashboard
canonicalCrossRepoAtomicDashboard =
  record
    { full118Surface = full118DashifineVisualization
    ; finiteFormalSurface = finiteFirstTenFormalTarget
    ; generativeSurface = generic369Constructor
    ; generativeStatement = Generative.CanonicalAtomicPeriodicTableStatement
    ; generativeStatementIs = refl
    ; discipline = canonicalCrossRepoRegressionDiscipline
    }
