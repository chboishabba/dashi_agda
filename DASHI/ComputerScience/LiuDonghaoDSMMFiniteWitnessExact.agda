module DASHI.ComputerScience.LiuDonghaoDSMMFiniteWitnessExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.ComputerScience.LiuDonghaoDSMMBidiExact as Liu

------------------------------------------------------------------------
-- FINITE MATURITY-ASSESSMENT SHAPE
--
-- This is a finite DASHI reconstruction of the lifecycle-evidence shape. It is
-- not asserted to reproduce an official GB/T 37988-2019 score or a Liu Donghao
-- authored assessment instance.
------------------------------------------------------------------------

record FiniteLiuDSMMWitness : Set where
  constructor finite-liu-dsmm-witness
  field
    sourceReference : String
    lifecycleStages : List Liu.DSMMStage
    assessedControlCount : Nat
    retainedEvidenceCount : Nat
    unresolvedControlCount : Nat
    syntheticAssessment : Bool
    officialScoreReproduced : Bool
    authoredRubricPaid : Bool
    nextExactLeaf : String

open FiniteLiuDSMMWitness public

finiteLiuDSMMWitness : FiniteLiuDSMMWitness
finiteLiuDSMMWitness = finite-liu-dsmm-witness
  "GB/T 37988-2019 context; institutional Liu Donghao DSMM lecture surface"
  (Liu.collection ∷ Liu.transmission ∷ Liu.storage ∷ Liu.processing ∷ Liu.exchange ∷ Liu.destruction ∷ [])
  6
  4
  2
  true
  false
  false
  "recover Liu-authored assessment rules, maturity-level scoring and one source-exact assessment example before promoting this finite shape to an official DSMM result"

finiteLifecycleCoveragePresent : Bool
finiteLifecycleCoveragePresent = true

finiteWitnessIsOfficialDSMMScore : Bool
finiteWitnessIsOfficialDSMMScore = false

finiteWitnessImpliesCryptographicPrimitive : Bool
finiteWitnessImpliesCryptographicPrimitive = false
