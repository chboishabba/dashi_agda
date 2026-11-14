{-# OPTIONS --safe #-}
module DASHI.Research.OpenAIMath.OpenAIYangMillsSameWitnessNonEntailmentExact where

------------------------------------------------------------------------
-- OpenAI Yang--Mills 28 October 2026 review: logical provenance gate.
-- External source: yang-mills-group/YM,
-- submissions/openai-20261028/checks/{AcceptanceSpec,OPESpec}.lean.
-- Original source: OpenAI. Review: Douglas, Gross, Jaffe, Klebanov,
-- Nekrasov. This file is a synthetic finite countermodel, not a claim
-- the external witnesses differ or a proof of a Yang--Mills problem.
-- Source-written; pinned Agda 2.9 kernel acceptance is outstanding.
------------------------------------------------------------------------

record Both (A B : Set) : Set where
  constructor both
  field
    first : A
    second : B

record Exists (W : Set) (P : W → Set) : Set where
  constructor exists
  field
    witness : W
    evidence : P witness

data Empty : Set where

data Family : Set where
  firstFamily secondFamily : Family

data ReviewedCombined : Family → Set where
  combinedFirst : ReviewedCombined firstFamily

data SeparateOPE : Family → Set where
  opeSecond : SeparateOPE secondFamily

combinedHasWitness : Exists Family ReviewedCombined
combinedHasWitness = exists firstFamily combinedFirst

opeHasWitness : Exists Family SeparateOPE
opeHasWitness = exists secondFamily opeSecond

bothEndpointsIndividually :
  Both (Exists Family ReviewedCombined) (Exists Family SeparateOPE)
bothEndpointsIndividually = both combinedHasWitness opeHasWitness

-- Two individually inhabited predicates may be disjoint.
noSameWitnessFromSeparateExistences :
  Exists Family (λ f → Both (ReviewedCombined f) (SeparateOPE f)) → Empty
noSameWitnessFromSeparateExistences
  (exists firstFamily (both combinedFirst ()))
noSameWitnessFromSeparateExistences
  (exists secondFamily (both () opeSecond))

-- Correct completion requires a genuinely same-witness transfer.
sameWitnessLift :
  {W : Set} {P Q : W → Set} →
  ((w : W) → P w → Q w) →
  Exists W P →
  Exists W (λ w → Both (P w) (Q w))
sameWitnessLift transfer (exists w pw) =
  exists w (both pw (transfer w pw))

-- Separate finite non-entailment: positive probe does not imply
-- all nonvacuum modes have positive energy. NOT a YM spectral model.
data NonvacuumMode : Set where
  zeroMode positiveMode : NonvacuumMode

data HasPositiveEnergy : NonvacuumMode → Set where
  positiveProbe : HasPositiveEnergy positiveMode

somePositiveProbe : Exists NonvacuumMode HasPositiveEnergy
somePositiveProbe = exists positiveMode positiveProbe

noAllModesPositive :
  ((m : NonvacuumMode) → HasPositiveEnergy m) → Empty
noAllModesPositive h with h zeroMode
... | ()

probeAndNoUniformGap :
  Both (Exists NonvacuumMode HasPositiveEnergy)
       (((m : NonvacuumMode) → HasPositiveEnergy m) → Empty)
probeAndNoUniformGap = both somePositiveProbe noAllModesPositive
