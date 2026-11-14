module DASHI.Research.OpenAIMath.OpenAIMathCrosswalkReview20261114 where

------------------------------------------------------------------------
-- Source-qualified OUTCOME of six OpenAI math ↔ DASHI reviews.
-- Original external authors: OpenAI (lean/formalization.yaml);
-- earlier mathematical authors retain independent attribution.
-- Donor: chboishabba/dashi_lean4 #78,
--   Integration/OpenAIMath/reviewed_cross_corpus_same_object_boundaries_20261101.json
-- at 32a7c06f2795427680173a3e61ec00c55e2e21fe.
-- This is NOT an Agda proof port of any upstream Lean theorem.
------------------------------------------------------------------------
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)

data MathematicalRelation : Set where
  complementaryDifferentCarrier : MathematicalRelation
  distinctScope : MathematicalRelation
  weakerThanOriginalGoal : MathematicalRelation
  strictSubclass : MathematicalRelation
  adjacentPhysicsOnly : MathematicalRelation
  lexicalOnly : MathematicalRelation

record ExactSourceReview : Set where
  constructor review
  field
    externalDeclaration : String
    externalSource : String
    originalDashiOwner : String
    relation : MathematicalRelation
    sameObjectTransportPaid : Bool
    agdaKernelPaid : Bool

open ExactSourceReview public

subexponentialSAT : ExactSourceReview
subexponentialSAT = review
  "OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat"
  "OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/Final.lean"
  "DASHI/Research/OpenAIMath/OpenAIMathFiniteSupportedTseitinModelsExact.agda"
  complementaryDifferentCarrier false false

optimalMaxCut : ExactSourceReview
optimalMaxCut = review
  "OAI.OptimalMaxCut.main"
  "OAI/Computability/MaxCut/Main.lean"
  "DASHI/Combinatorics/GraphColouring369PantsWeightedMaxCutExact.agda"
  distinctScope false false

quasiRiemann : ExactSourceReview
quasiRiemann = review
  "OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re"
  "OAI/NumberTheory/DirichletL/Nonvanishing.lean"
  "DASHI/Research/OpenAIMath/OpenAIMathSourceAtlasExact.agda"
  weakerThanOriginalGoal false false

hodgeCM : ExactSourceReview
hodgeCM = review
  "HodgeCM.hodge_conjecture_for_cm_abelian_varieties"
  "ComparatorChallenges/HodgeConjectureCMAbelianVarieties/Solution.lean"
  "DASHI/Mathematics/AlgebraicGeometry/HodgePrizeBoundaryExact.agda"
  strictSubclass false false

vlasovMaxwell : ExactSourceReview
vlasovMaxwell = review
  "OAI.RVM.global_classical_solution"
  "OAI/Analysis/VlasovMaxwell/Main.lean"
  "DASHI/Physics/YangMills/YMClayDirectSourceOSMassGapFrontierExact.agda"
  adjacentPhysicsOnly false false

exactFourier : ExactSourceReview
exactFourier = review
  "OAI.ExactFourier.main_theorem"
  "OAI/Computability/FourierCircuit/Main.lean"
  "DASHI/Papers/NavierStokes/Everything.agda"
  lexicalOnly false false

-- Regression: no reviewed source claims to prove an Agda theorem.
_ : sameObjectTransportPaid optimalMaxCut ≡ false
_ = refl
_ : agdaKernelPaid subexponentialSAT ≡ false
_ = refl
_ : sameObjectTransportPaid hodgeCM ≡ false
_ = refl
