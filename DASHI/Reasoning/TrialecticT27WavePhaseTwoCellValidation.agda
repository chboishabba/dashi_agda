module DASHI.Reasoning.TrialecticT27WavePhaseTwoCellValidation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Foundations.RelationalStageTwelveGrothendieckExtensionExact as Site
import DASHI.Reasoning.TrialecticT9T18T27GraphExtensionExact as Tower
import DASHI.Reasoning.TrialecticT27GraphSitePresheafExact as Graph
import DASHI.Reasoning.TrialecticT27WavePhaseGroupoidPresheafExact as Phase27
import DASHI.Reasoning.TrialecticT27WavePhaseTwoCellExact as Two27

policy : Tower.T27CompletionPolicy
policy = Tower.firstNine

boundary : Two27.TrialecticT27WavePhaseTwoCellBoundary
boundary = Two27.canonicalTrialecticT27WavePhaseTwoCellBoundary

everyFibre : Two27.phaseTwoCellsOnEveryGraphSiteFibre boundary ≡ true
everyFibre = refl

whiskering : Two27.leftRightWhiskeringPaid boundary ≡ true
whiskering = refl

horizontal : Two27.horizontalCompositionPaid boundary ≡ true
horizontal = refl

restriction : Two27.restrictionPreservesTwoCells boundary ≡ true
restriction = refl

cocycle : Two27.arbitraryTriadicOverlapPhaseCocycleReused boundary ≡ true
cocycle = refl

canonicalGlobal : Graph.GraphSection policy Site.globalABC
canonicalGlobal = Graph.canonicalGraphGlobalSection policy

identityHom : Phase27.GraphFibreHom policy canonicalGlobal canonicalGlobal
identityHom = Phase27.graphIdentityHom policy canonicalGlobal

identity2Cell : Two27.GraphPhase2Cell policy identityHom identityHom
identity2Cell = Two27.graphIdentity2Cell
