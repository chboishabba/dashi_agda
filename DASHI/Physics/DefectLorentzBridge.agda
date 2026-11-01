module DASHI.Physics.DefectLorentzBridge where

open import DASHI.Unifier using (Geometry)
open import DASHI.Geometry.EinsteinFromDefect as EFD
open import DASHI.Physics.LorentzianCoreClosure as LCC

------------------------------------------------------------------------
-- Cross-pollination boundary:
--
-- * LorentzianCoreClosure supplies the earned finite masked geometry.
-- * BianchiBundle supplies the still-assumed differential/defect bridge.
-- * Bianchi-theorem then exposes the corresponding conservation and
--   Einstein-tensor consequences without duplicating either formalism.

record DefectLorentzClosure : Set₁ where
  field
    core : LCC.LorentzianCoreClosure
    geometry : Geometry
    bianchiBundle : EFD.BianchiBundle geometry

  consequences : EFD.BianchiConsequences bianchiBundle
  consequences = EFD.Bianchi-theorem bianchiBundle

open DefectLorentzClosure public

mkDefectLorentzClosure :
  (geometry : Geometry) →
  EFD.BianchiBundle geometry →
  DefectLorentzClosure
mkDefectLorentzClosure geometry bundle =
  record
    { core = LCC.lorentzianCoreClosure
    ; geometry = geometry
    ; bianchiBundle = bundle
    }
