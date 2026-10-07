module DASHI.Governance.BoloBoloIncidenceCompressionRegression where

open import DASHI.Core.Prelude

import DASHI.Governance.BoloBoloIncidenceCompressionExact as Compression

kanaLowerGlobalPinned : Compression.globalIncidenceEdges Compression.kanaLowerScenario ≡ 6000
kanaLowerGlobalPinned = refl

kanaLowerLocalPinned : Compression.localIncidenceEdges Compression.kanaLowerScenario ≡ 300
kanaLowerLocalPinned = refl

kanaUpperGlobalPinned : Compression.globalIncidenceEdges Compression.kanaUpperScenario ≡ 12000
kanaUpperGlobalPinned = refl

kanaUpperLocalPinned : Compression.localIncidenceEdges Compression.kanaUpperScenario ≡ 600
kanaUpperLocalPinned = refl

tegaTenGlobalPinned : Compression.globalIncidenceEdges Compression.tegaTenBoloScenario ≡ 50000
tegaTenGlobalPinned = refl

tegaTenLocalPinned : Compression.localIncidenceEdges Compression.tegaTenBoloScenario ≡ 5000
tegaTenLocalPinned = refl

scenarioNotEmpiricalLaw :
  Compression.combinatorialScenarioIsEmpiricalScalingLaw Compression.canonicalIncidenceCompressionBoundary ≡ false
scenarioNotEmpiricalLaw = refl

sourceDidNotStateQuadraticFormula :
  Compression.quadraticIncidenceFormulaAttributedToPM Compression.canonicalIncidenceCompressionBoundary ≡ false
sourceDidNotStateQuadraticFormula = refl
