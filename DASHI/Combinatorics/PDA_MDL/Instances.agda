module DASHI.Combinatorics.PDA_MDL.Instances where

open import DASHI.Combinatorics.PDA_MDL.Prelude
open import DASHI.Combinatorics.PDA_MDL.ExponentVector
open import DASHI.Combinatorics.PDA_MDL.EV_Likelihood
open import DASHI.Combinatorics.PDA_MDL.CICADA71_Model
open import DASHI.Combinatorics.PDA_MDL.PDA
open import DASHI.Combinatorics.PDA_MDL.KernelSelection

record PDAInstanceAxioms : Set₁ where
  field
    S : Set
    extractEV : S → EV
    shardEV : EV → Bucket

open PDAInstanceAxioms public

PDA-EV : (A : PDAInstanceAxioms) → PDA (S A) EV
PDA-EV A = record
  { observe = extractEV A
  ; admissible = λ _ → ⊤
  ; costPDA = 15  -- price of having this lens; refine later
  }

-- EV model turned into an ObsModel
evObsModel : IndepEVModel → ObsModel EV
evObsModel M = record
  { Lmodel = Lmodel M
  ; Ldata| = λ obsList →  -- interpret obsList as DatasetEV and score it
      let
        D : DatasetEV
        D = obsList
      in
      Ldata| M D
  }

-- CICADA-71 PDA: observe bucket directly from extracted exponent vector
-- (lens includes sharding; price it)
PDA-71 : (A : PDAInstanceAxioms) → PDA (S A) Bucket
PDA-71 A = record
  { observe = λ s → shardEV A (extractEV A s)
  ; admissible = λ _ → ⊤
  ; costPDA = 71  -- “limit to 71” lens price placeholder
  }

-- IID71 model turned into an ObsModel
obsModel71 : IID71 → ObsModel Bucket
obsModel71 M = record
  { Lmodel = Lmodel71 M
  ; Ldata| = λ bs → Ldata|71 M (bs)
  }
