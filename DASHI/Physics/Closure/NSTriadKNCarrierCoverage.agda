module DASHI.Physics.Closure.NSTriadKNCarrierCoverage where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Primitive using (Level; lsuc; _⊔_)

import DASHI.Physics.Closure.NSTriadKNBKMContinuation as BKMCont

------------------------------------------------------------------------
-- Final carrier-to-full-Navier-Stokes coverage surface.
--
-- Even after the triad carrier closes a BKM continuation route, Clay-grade
-- coverage still requires that arbitrary smooth divergence-free initial data
-- enter the carrier, that carrier evolution matches Navier-Stokes, and that
-- the continuation theorem upgrades to a genuine global smooth solution.

record NSTriadKNCarrierCoverageModel
    {ℓS ℓE ℓV ℓR : Level} : Set (lsuc (ℓS ⊔ ℓE ⊔ ℓV ⊔ ℓR)) where
  field
    bkmContinuationModel :
      BKMCont.NSTriadKNBKMContinuationModel {ℓS} {ℓE} {ℓV} {ℓR}

    SmoothDivergenceFreeInitialData : Set ℓR
    TriadCarrierInitialData : Set ℓR
    TriadCarrierSolution : Set ℓR
    NavierStokesSolution : Set ℓR
    CarrierBKMFinite : Set ℓR
    CarrierSmoothContinuation : Set ℓR
    GlobalSmoothSolution : Set ℓR

    allSmoothNSDataEnterCarrier :
      SmoothDivergenceFreeInitialData ->
      TriadCarrierInitialData

    carrierEvolutionMatchesNS :
      TriadCarrierSolution ->
      NavierStokesSolution

    bkmContinuationForCarrier :
      CarrierBKMFinite ->
      CarrierSmoothContinuation

    globalSmoothNSRegularity :
      SmoothDivergenceFreeInitialData ->
      GlobalSmoothSolution

open NSTriadKNCarrierCoverageModel public

carrierCoverageClosed : Bool
carrierCoverageClosed = false

carrierCoverageClosedIsFalse :
  carrierCoverageClosed ≡ false
carrierCoverageClosedIsFalse = refl
