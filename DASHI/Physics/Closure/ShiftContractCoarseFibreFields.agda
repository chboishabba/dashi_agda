module DASHI.Physics.Closure.ShiftContractCoarseFibreFields where

open import Agda.Builtin.Nat using (Nat)
open import Data.Product using (_,_; _×_)

open import MonsterOntos using (SSP)
open import Ontology.GodelLattice using (FactorVec)
import Ontology.Hecke.FactorVecDefectHistograms as FDH
import Ontology.Hecke.FactorVecDefectOrbitSummaries as FOS
open import Ontology.Hecke.PrimeHeckeEigenMotifPipeline as PHEM
open import Ontology.Hecke.Scan as HS

open import DASHI.Physics.Closure.ShiftRGObservableInstance as SRGOI
  using (canonicalShiftHeckeState)
open import DASHI.Physics.Closure.ShiftContractCoarseFibre as SCF
open import DASHI.Physics.Closure.ShiftContractObservableTransportPrimeCompatibilityProfileInstance as SCOT

------------------------------------------------------------------------
-- First noncanonical fibre fields over the ShiftContract coarse package.
-- This mirrors the canonical fibre-field surface without claiming the same
-- control theorems yet.

heckeField :
  ∀ {q} →
  SCF.ShiftContractCoarseFibre q → HS.Sig15
heckeField x =
  SCOT.signatureOnGeo (canonicalShiftHeckeState (SCF.carrier x))

eigenField :
  ∀ {q} →
  SCF.ShiftContractCoarseFibre q → PHEM.EigenProfile
eigenField x =
  SCOT.eigenOnGeo (canonicalShiftHeckeState (SCF.carrier x))

eigenShadowField :
  ∀ {q} →
  SCF.ShiftContractCoarseFibre q → Nat × Nat
eigenShadowField x =
  ( PHEM.EigenProfile.earth (eigenField x)
  , PHEM.EigenProfile.hub (eigenField x)
  )

primeField :
  ∀ {q} →
  SCF.ShiftContractCoarseFibre q → FactorVec
primeField x =
  SCOT.shiftContractObservablePrimeEmbedding (SCF.carrier x)

illegalCountField :
  ∀ {q} →
  SSP → SCF.ShiftContractCoarseFibre q → Nat
illegalCountField p x = FDH.illegalCount p (primeField x)

forcedStableCountField :
  ∀ {q} →
  SSP → SCF.ShiftContractCoarseFibre q → Nat
forcedStableCountField p x = FDH.forcedStableCount p (primeField x)

orbitSummaryField :
  ∀ {q} →
  SSP → SCF.ShiftContractCoarseFibre q → FOS.DefectOrbitSummary
orbitSummaryField p x =
  FOS.profileSummaryAt p (primeField x)
