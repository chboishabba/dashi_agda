module DASHI.Reasoning.TrialecticT27WavePhaseGroupoidPresheafValidation where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Foundations.RelationalStageTwelveGrothendieckExtensionExact as Site
import DASHI.Reasoning.TrialecticT9T18T27GraphExtensionExact as Tower
import DASHI.Reasoning.TrialecticT27GraphSitePresheafExact as Graph
import DASHI.Reasoning.TrialecticT27WavePhaseGroupoidPresheafExact as Phase27

policy : Tower.T27CompletionPolicy
policy = Tower.firstNine

boundary : Phase27.TrialecticT27WavePhaseGroupoidPresheafBoundary
boundary = Phase27.canonicalTrialecticT27WavePhaseGroupoidPresheafBoundary

globalT27Groupoid : Phase27.globalCompletedT27CarriesPhaseGroupoid boundary ≡ true
globalT27Groupoid = refl

localGroupoidsUnchanged : Phase27.localT9T3GroupoidsReused boundary ≡ true
localGroupoidsUnchanged = refl

restrictionFunctorTransported : Phase27.restrictionMorphismFunctorTransported boundary ≡ true
restrictionFunctorTransported = refl

groupoidLawsTransported : Phase27.groupoidLawsTransportedModuloPhaseSetoid boundary ≡ true
groupoidLawsTransported = refl

nontrivialAtGlobal : Phase27.nontrivialPhaseAutomorphismAtCompletedT27 boundary ≡ true
nontrivialAtGlobal = refl

ambientT27StillNotFree : Phase27.unconstrainedAmbientT27PromotedToGroupoidObject boundary ≡ false
ambientT27StillNotFree = refl

canonicalGlobal : Graph.GraphSection policy Site.globalABC
canonicalGlobal = Graph.canonicalGraphGlobalSection policy

identityHom : Phase27.GraphFibreHom policy canonicalGlobal canonicalGlobal
identityHom = Phase27.graphIdentityHom policy canonicalGlobal

positiveHom : Phase27.GraphFibreHom policy canonicalGlobal canonicalGlobal
positiveHom = Phase27.graphPositivePhaseAutomorphism policy canonicalGlobal

positiveNotIdentity :
  Phase27.graphHomEquivalent policy identityHom positiveHom → ⊥
positiveNotIdentity = Phase27.graphPositivePhaseDiffersFromIdentity policy canonicalGlobal
