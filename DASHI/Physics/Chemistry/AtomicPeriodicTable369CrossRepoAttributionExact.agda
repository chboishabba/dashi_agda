module DASHI.Physics.Chemistry.AtomicPeriodicTable369CrossRepoAttributionExact where

open import DASHI.Core.Prelude

import DASHI.Physics.Chemistry.AtomicPeriodicTable369AttributionLedgerExact as A
import DASHI.Physics.Chemistry.AtomicPeriodicTable369CrossRepoRegressionExact as X

------------------------------------------------------------------------
-- Identifier-rich attribution for the two strongest newly located
-- computational archaeology objects.  The shared attribution grammar comes
-- from AtomicPeriodicTable369AttributionLedgerExact so DOI/QID/primary/Dewey/
-- link fields remain uniform across historical, formal, semantic and external
-- sources.

full118DashifineAttribution : A.AttributionReceipt
full118DashifineAttribution =
  A.attributionReceipt
    "Johl Brown"
    "Periodic Table Cloud (full 118)"
    "authored 2026-02-21; committed 2026-03-05"
    "unassigned"
    "periodic table Q10693; atom Q9121"
    "primary repository computational source; consumes existing periodic-table CSV"
    "546 / 539.7 classification cues"
    "https://github.com/chboishabba/dashifine/commit/9f1430ab7fe7c4ae480e93bc9f7549f4b758950e"
    "bangerz.py and bangerz2.py; full-118 animation source"
    "implementation chronology and table-wide computational breadth only"
    "renders all 118 CSV rows through period/group/electronegativity/mass features; not a first-principles derivation of those rows"

finiteHNeShellTargetAttribution : A.AttributionReceipt
finiteHNeShellTargetAttribution =
  A.attributionReceipt
    "Johl Brown"
    "ChemistryFiniteRuleTargets"
    "2026-06-07"
    "unassigned"
    "atom Q9121; periodic table Q10693; Pauli exclusion principle Q131594"
    "primary repository formal source"
    "539.7 / 546 classification cues"
    "https://github.com/chboishabba/dashi_agda/commit/062ccb611c6d93fa7228a73d1557c8c934ea89d5"
    "DASHI/Promotion/ChemistryFiniteRuleTargets.agda added from zero lines"
    "formal finite-target authority for its stated H-through-Ne occupations and regression equalities"
    "explicit Z=1..10 Aufbau/Pauli/Hund target carrier; spectroscopy, thermochemistry, wet-lab and physical-chemistry promotion remain false"

------------------------------------------------------------------------
-- Same-object joins to the cross-repository regression owner.

record CrossRepoAttributionWeld : Set where
  constructor crossRepoAttributionWeld
  field
    full118Receipt : A.AttributionReceipt
    full118Regression : X.CrossRepoRegressionReceipt
    finiteHNeReceipt : A.AttributionReceipt
    finiteHNeRegression : X.CrossRepoRegressionReceipt
    qidPromotesGenerativeDerivation : Bool
    qidPromotesGenerativeDerivationIsFalse :
      qidPromotesGenerativeDerivation ≡ false
    tableWideBreadthPromotesPhysicalRecovery : Bool
    tableWideBreadthPromotesPhysicalRecoveryIsFalse :
      tableWideBreadthPromotesPhysicalRecovery ≡ false

canonicalCrossRepoAttributionWeld : CrossRepoAttributionWeld
canonicalCrossRepoAttributionWeld =
  crossRepoAttributionWeld
    full118DashifineAttribution
    X.full118DashifineVisualization
    finiteHNeShellTargetAttribution
    X.finiteFirstTenFormalTarget
    false refl false refl
