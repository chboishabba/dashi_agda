module DASHI.PDA_MDL.Instances where

open import DASHI.PDA_MDL.Prelude
open import DASHI.PDA_MDL.ExponentVector
open import DASHI.PDA_MDL.EV_Likelihood
open import DASHI.PDA_MDL.CICADA71_Model
open import DASHI.PDA_MDL.PDA
open import DASHI.PDA_MDL.KernelSelection

-- Plug your real state type here
postulate
  S : Set

-- PDA that observes exponent-vectors from state
postulate
  extractEV : S → EV

PDA-EV : PDA S EV
PDA-EV = record
  { observe = extractEV
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
postulate
  shardEV : EV → Bucket

PDA-71 : PDA S Bucket
PDA-71 = record
  { observe = λ s → shardEV (extractEV s)
  ; admissible = λ _ → ⊤
  ; costPDA = 71  -- “limit to 71” lens price placeholder
  }

-- IID71 model turned into an ObsModel
obsModel71 : IID71 → ObsModel Bucket
obsModel71 M = record
  { Lmodel = Lmodel71 M
  ; Ldata| = λ bs → Ldata|71 M (bs)
  }
