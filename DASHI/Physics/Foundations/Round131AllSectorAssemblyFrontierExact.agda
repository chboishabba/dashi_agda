{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.Round131AllSectorAssemblyFrontierExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Round131 closes one native YM sector.  The generic all-sector producer is
-- already compiled.  This frontier records the exact application-owned bridge
-- between them, without reopening finite->continuum or stress convergence.
------------------------------------------------------------------------

data Round131AllSectorAssemblyLeaf : Set where
  commonSectorMetricAndScalarConvention :
    Round131AllSectorAssemblyLeaf
  sectorTransportForEveryCompactSimpleGroup :
    Round131AllSectorAssemblyLeaf
  explicitTotalStressAggregation :
    Round131AllSectorAssemblyLeaf
  aggregateStressPairingCommutation :
    Round131AllSectorAssemblyLeaf
  aggregateEqualsDeclaredQFTTotal :
    Round131AllSectorAssemblyLeaf
  aggregationWitnessForUnifiedCandidate :
    Round131AllSectorAssemblyLeaf

canonicalRound131AllSectorAssemblyLeaves :
  List Round131AllSectorAssemblyLeaf
canonicalRound131AllSectorAssemblyLeaves =
  commonSectorMetricAndScalarConvention
  ∷ sectorTransportForEveryCompactSimpleGroup
  ∷ explicitTotalStressAggregation
  ∷ aggregateStressPairingCommutation
  ∷ aggregateEqualsDeclaredQFTTotal
  ∷ aggregationWitnessForUnifiedCandidate
  ∷ []

round131RequiresSecondContinuumTheorem : Bool
round131RequiresSecondContinuumTheorem = false

round131RequiresSecondContinuumTheoremIsFalse :
  round131RequiresSecondContinuumTheorem ≡ false
round131RequiresSecondContinuumTheoremIsFalse = refl

round131RequiresSecondStressConvergenceTheorem : Bool
round131RequiresSecondStressConvergenceTheorem = false

round131RequiresSecondStressConvergenceTheoremIsFalse :
  round131RequiresSecondStressConvergenceTheorem ≡ false
round131RequiresSecondStressConvergenceTheoremIsFalse = refl

frontierStatement : String
frontierStatement =
  "Round131 sector recovery plus explicit all-sector aggregation is the QFT-side max-cut; no second continuum or stress-convergence theorem is admissible."
