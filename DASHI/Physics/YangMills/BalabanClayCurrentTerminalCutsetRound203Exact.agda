{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayCurrentTerminalCutsetRound203Exact where

------------------------------------------------------------------------
-- ROUND203: PREFERRED PATH4 ENERGY ROUTE
--
-- Round202 still listed nonnegativity/coercivity as physical leaves.  The
-- literal Path4 energy realization plus already-owned finite theorems produces
-- both mechanically.  The preferred T1 cut therefore keeps only the actual
-- cross-carrier/analytic seams.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; _∷_; [])

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayCurrentTerminalCutsetRound202Exact as R202
import DASHI.Physics.YangMills.BalabanClayT5Path4GaugeEnergyObservableRealizationExact as Realization
import DASHI.Physics.YangMills.BalabanClayT5Path4GaugeEnergyMarkovBridgeExact as Path4
import DASHI.Physics.YangMills.YMOperatorDomainContinuumFrontier2026Exact as Frontier

data T5PreferredContinuumLeaf203 : Set where
  physicalPath4GaugeEnergyObservableRealization : T5PreferredContinuumLeaf203
  physicalPath4GaugeEnergyRenormalization : T5PreferredContinuumLeaf203
  physicalPath4GaugeEnergyCompactSublevel : T5PreferredContinuumLeaf203
  physicalEveryExtractedClusterPointIsTarget : T5PreferredContinuumLeaf203
  physicalMeasurePropertySequentialClosure : T5PreferredContinuumLeaf203
  physicalGramReflectionMeasureTopologyClosure : T5PreferredContinuumLeaf203
  physicalContinuumSchwingerAxioms : T5PreferredContinuumLeaf203

preferredT5ContinuumCut203 : List T5PreferredContinuumLeaf203
preferredT5ContinuumCut203 =
  physicalPath4GaugeEnergyObservableRealization ∷
  physicalPath4GaugeEnergyRenormalization ∷
  physicalPath4GaugeEnergyCompactSublevel ∷
  physicalEveryExtractedClusterPointIsTarget ∷
  physicalMeasurePropertySequentialClosure ∷
  physicalGramReflectionMeasureTopologyClosure ∷
  physicalContinuumSchwingerAxioms ∷ []

path4GaugeEnergyPointwiseNonnegativeLevel : ProofLevel
path4GaugeEnergyPointwiseNonnegativeLevel =
  Realization.path4GaugeEnergyPointwiseNonnegativeLevel

path4GaugeEnergyPointwiseCoercivityTransportLevel : ProofLevel
path4GaugeEnergyPointwiseCoercivityTransportLevel =
  Realization.path4GaugeEnergyPointwiseCoercivityTransportLevel

path4SelectedMomentContainmentCompilerLevel : ProofLevel
path4SelectedMomentContainmentCompilerLevel =
  Path4.path4SelectedMomentContainmentCompilerLevel

physicalPath4GaugeEnergyObservableRealizationProducerLevel : ProofLevel
physicalPath4GaugeEnergyObservableRealizationProducerLevel =
  Realization.path4GaugeEnergyObservableRealizationLevel

physicalPath4GaugeEnergyRenormalizationProducerLevel : ProofLevel
physicalPath4GaugeEnergyRenormalizationProducerLevel =
  Realization.path4GaugeEnergyRenormalizationLevel

physicalPath4GaugeEnergyCompactSublevelProducerLevel : ProofLevel
physicalPath4GaugeEnergyCompactSublevelProducerLevel =
  Path4.path4GaugeEnergyCompactSublevelLevel

data T1PrerequisiteStatus203 : Set where
  missingPath4GaugeEnergyObservableRealization : T1PrerequisiteStatus203
  missingPath4GaugeEnergyRenormalization : T1PrerequisiteStatus203
  missingPath4GaugeEnergyCompactSublevel : T1PrerequisiteStatus203
  readyForSelectedMomentUniformTightnessCompiler : T1PrerequisiteStatus203

preferredCurrentT1Status203 : T1PrerequisiteStatus203
preferredCurrentT1Status203 = missingPath4GaugeEnergyObservableRealization

round202CutRetainedForCompatibility : ProofLevel
round202CutRetainedForCompatibility = R202.currentYMTerminalCutsetRound202Level

finiteToContinuumYMStillOpen :
  Frontier.finiteToContinuumYMConstructionClosed
    Frontier.canonicalYMOperatorContinuumFrontier ≡ false
finiteToContinuumYMStillOpen = refl

continuumOSWightmanStillOpen :
  Frontier.continuumOSWightmanPackageClosed
    Frontier.canonicalYMOperatorContinuumFrontier ≡ false
continuumOSWightmanStillOpen = refl

currentYMTerminalCutsetRound203Level : ProofLevel
currentYMTerminalCutsetRound203Level = machineChecked

literalPreferredT5ContinuumLeaf203Level : ProofLevel
literalPreferredT5ContinuumLeaf203Level = conditional
