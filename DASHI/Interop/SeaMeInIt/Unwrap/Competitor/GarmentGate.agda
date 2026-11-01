module DASHI.Interop.SeaMeInIt.Unwrap.Competitor.GarmentGate where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)

open import DASHI.Interop.SeaMeInIt.Unwrap.Competitor.Core
open import DASHI.Interop.SeaMeInIt.Unwrap.Competitor.Methods
open import DASHI.Interop.SeaMeInIt.Unwrap.Competitor.Benchmark

------------------------------------------------------------------------
-- Garment promotion wrapper
------------------------------------------------------------------------

data GrainDirection : Set where
  warp : GrainDirection
  weft : GrainDirection
  bias : GrainDirection
  arbitrary : GrainDirection

data DartOp : Set where
  wedgeDart : Nat → Nat → DartOp
  reliefCut : Nat → DartOp
  pleat : Nat → Nat → DartOp
  splitPanel : Nat → DartOp
  stretchEase : Nat → Nat → DartOp

record PanelReceipt : Set where
  field
    panelId : Nat
    topologicalDisk : Bool
    foldoversZero : Bool
    distortionOK : Bool
    grainOK : Bool
    seamRiskOK : Bool
    grainDirection : GrainDirection
    corrections : List DartOp

open PanelReceipt public

PanelOK : PanelReceipt → Set
PanelOK panel =
  topologicalDisk panel ≡ true
  × foldoversZero panel ≡ true
  × distortionOK panel ≡ true
  × grainOK panel ≡ true
  × seamRiskOK panel ≡ true

record GarmentPatternReceipt : Set₁ where
  field
    bodyHash : String
    romHash : Maybe String
    fabricHash : Maybe String
    methodRun : CompetitorRunReceipt
    panels : List PanelReceipt
    seamSetHash : String
    garmentSeverity : MethodSeverityReport
    manufacturingOK : Bool
    notPromotedUnlessAllPanelsOK : Set

open GarmentPatternReceipt public

record GarmentPromoted
    (garment : GarmentPatternReceipt) : Set₁ where
  field
    allPanelsOK : Set
    manufacturingOKWitness :
      manufacturingOK garment ≡ true
    methodBoundaryOK :
      claimsManufacturingAuthority
        (claimBoundary
          (method
            (methodRun garment)))
      ≡ false

open GarmentPromoted public
