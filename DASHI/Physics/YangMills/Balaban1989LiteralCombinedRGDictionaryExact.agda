module DASHI.Physics.YangMills.Balaban1989LiteralCombinedRGDictionaryExact where

-- Tadeusz Bałaban, "Convergent Renormalization Expansions for Lattice Gauge
-- Theories", CMP 119 (1988), 243--285. DOI: 10.1007/BF01217741.
-- Tadeusz Bałaban, "Large Field Renormalization. II", CMP 122 (1989),
-- 355--392. DOI: 10.1007/BF01238433.

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.Balaban1989Theorem1UVStabilityExact as S
import DASHI.Physics.YangMills.Balaban1989CompleteDensityToCombinedRGExact as D
import DASHI.Physics.YangMills.BalabanClayGate4CombinedRGUVIterationExact as U

record LiteralCombinedRGDictionary {C Den St B : Set}
  {flow : S.Balaban1989EffectiveDensityFlow C Den}
  {normData : U.CombinedOneStepPolymerNormData St B}
  (adm : U.CombinedRGAdmissibility normData) : Set₁ where
  field
    state : Nat → St
    trajectory : ∀ k → state k ≡ U.stateAt normData (state 0) k
    formToCoupling : ∀ k → S.InSection2DensityClass flow k (S.densityAt flow k) → U.AdmissibleCoupling adm (state k)
    boundsToBoundary : ∀ k → S.Section2ConditionsAndBounds flow k (S.densityAt flow k) → U.BoundaryAdmissible adm (state k)
    boundsToPolymer : ∀ k → S.Section2ConditionsAndBounds flow k (S.densityAt flow k) → U.PolymerNormAdmissible adm (state k)
open LiteralCombinedRGDictionary public

asCombinedDictionary : ∀ {C Den St B} {flow : S.Balaban1989EffectiveDensityFlow C Den}
  {normData : U.CombinedOneStepPolymerNormData St B} {adm : U.CombinedRGAdmissibility normData} →
  LiteralCombinedRGDictionary adm → D.CompleteDensityCombinedRGDictionary adm
asCombinedDictionary x = record { D.CompleteDensityCombinedRGDictionary.sourceState = state x ; D.CompleteDensityCombinedRGDictionary.sourceStateIsRepositoryTrajectory = trajectory x ; D.CompleteDensityCombinedRGDictionary.sourceFormGivesCoupling = formToCoupling x ; D.CompleteDensityCombinedRGDictionary.sourceBoundsGiveBoundary = boundsToBoundary x ; D.CompleteDensityCombinedRGDictionary.sourceBoundsGivePolymerNorm = boundsToPolymer x }

balaban1989LiteralCombinedRGDictionaryTransportLevel : ProofLevel
balaban1989LiteralCombinedRGDictionaryTransportLevel = machineChecked
