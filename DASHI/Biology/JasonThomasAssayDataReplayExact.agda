module DASHI.Biology.JasonThomasAssayDataReplayExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Biology.JasonThomasSignallingBidiExact as Base

------------------------------------------------------------------------
-- JASON R. THOMAS / ASSAY-DATA REPLAY SURFACE
--
-- Source objects:
--   ACS Chem Biol 13(4), 1066-1081 (2018), DOI 10.1021/acschembio.7b01060.
--   Nature Cell Biology 16, 1069-1079 (2014), DOI 10.1038/ncb3053.
--
-- Public text exposes the assay/readout/validation topology and specific target
-- identities, but this owner does not invent unpublished per-well counts or
-- concentration-response arrays.
------------------------------------------------------------------------

record ThomasAssayDataReplay : Set where
  constructor thomas-assay-data-replay
  field
    stingSource : String
    assayCellType : String
    primaryReadouts : String
    downstreamActivationNotEquivalentToTranslocation : Bool
    antagonistHitFamily : String
    targetDeconvolutionCandidate : String
    ferritinophagySource : String
    vps34Perturbation : String
    ferritinCargoAdaptor : String
    ferritinBindingTarget : String
    ferritinComplexRelativeMass : Nat
    exactPerWellScreenMatrixPaid : Bool
    exactDoseResponseArrayPaid : Bool
    exactProteomicsTablePaid : Bool

open ThomasAssayDataReplay public

thomasAssayDataReplay : ThomasAssayDataReplay
thomasAssayDataReplay = thomas-assay-data-replay
  "DOI 10.1021/acschembio.7b01060"
  "primary human macrophages"
  "IRF3 and NFkB cytoplasm-to-nucleus translocation"
  true
  "multiple kinase inhibitors in the STING-antagonist screen"
  "MAPKAPK5 / PRAK nominated by SAR plus chemical-proteomics follow-up"
  "DOI 10.1038/ncb3053"
  "PIK-III selective VPS34 inhibition"
  "NCOA4"
  "ferritin heavy chain-1 / FTH1"
  450000
  false
  false
  false

existingThomasBoundary : Base.ThomasMechanismBoundary
existingThomasBoundary = Base.canonicalThomasMechanismBoundary

sourceDataReplayPaysAssayReadoutTopology : Bool
sourceDataReplayPaysAssayReadoutTopology = true

sourceDataReplayPaysNamedPRAKCandidate : Bool
sourceDataReplayPaysNamedPRAKCandidate = true

sourceDataReplayPaysExactScreenMatrix : Bool
sourceDataReplayPaysExactScreenMatrix = false

screenHitPaysDirectTarget : Bool
screenHitPaysDirectTarget = false
