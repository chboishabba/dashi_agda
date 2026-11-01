module DASHI.Physics.Closure.ShiftContractMdlLevelCoarseFibreFields where

open import Agda.Builtin.Nat using (Nat)
open import Data.Product using (_,_; _×_; proj₁; proj₂)

open import MonsterOntos using (SSP)
open import Ontology.GodelLattice using (FactorVec)
import Ontology.Hecke.FactorVecDefectHistograms as FDH
import Ontology.Hecke.FactorVecDefectOrbitSummaries as FOS
open import Ontology.Hecke.PrimeHeckeEigenMotifPipeline as PHEM
open import Ontology.Hecke.Scan as HS

open import DASHI.Physics.Closure.ShiftContractMdlLevelCoarseFibre as SCMCF
open import DASHI.Physics.Closure.ShiftContractMdlLevelCoarseObservable as SCMCO
open import DASHI.Physics.Closure.ShiftContractCoarseObservable as SCCO
open import DASHI.Physics.Closure.ShiftContractObservableTransportPrimeCompatibilityProfileInstance as SCOT
open import DASHI.Physics.Closure.ShiftRGObservableInstance as SRGOI
  using (canonicalShiftHeckeState)

------------------------------------------------------------------------
-- Normalized fibre fields over the stronger noncanonical package
-- `mdlLevel × π-max`.
--
-- This mirrors the existing coarse-fibre vocabulary, but keeps the mdl-level
-- augmentation explicit as the first component of the normalized observable.

normalizedObservableField :
  ∀ {q} →
  SCMCF.ShiftContractMdlLevelCoarseFibre q → SCMCO.MdlLevelCoarseObservable
normalizedObservableField x = SCMCO.π-mdl-max (SCMCF.carrier x)

mdlLevelField :
  ∀ {q} →
  SCMCF.ShiftContractMdlLevelCoarseFibre q → Nat
mdlLevelField x = proj₁ (normalizedObservableField x)

coarseObservableField :
  ∀ {q} →
  SCMCF.ShiftContractMdlLevelCoarseFibre q → SCCO.MaximalCoarseObservable
coarseObservableField x = proj₂ (normalizedObservableField x)

heckeField :
  ∀ {q} →
  SCMCF.ShiftContractMdlLevelCoarseFibre q → HS.Sig15
heckeField x =
  SCOT.signatureOnGeo (canonicalShiftHeckeState (SCMCF.carrier x))

eigenField :
  ∀ {q} →
  SCMCF.ShiftContractMdlLevelCoarseFibre q → PHEM.EigenProfile
eigenField x =
  SCOT.eigenOnGeo (canonicalShiftHeckeState (SCMCF.carrier x))

eigenShadowField :
  ∀ {q} →
  SCMCF.ShiftContractMdlLevelCoarseFibre q → Nat × Nat
eigenShadowField x =
  ( PHEM.EigenProfile.earth (eigenField x)
  , PHEM.EigenProfile.hub (eigenField x)
  )

primeField :
  ∀ {q} →
  SCMCF.ShiftContractMdlLevelCoarseFibre q → FactorVec
primeField x =
  SCOT.shiftContractObservablePrimeEmbedding (SCMCF.carrier x)

illegalCountField :
  ∀ {q} →
  SSP → SCMCF.ShiftContractMdlLevelCoarseFibre q → Nat
illegalCountField p x = FDH.illegalCount p (primeField x)

forcedStableCountField :
  ∀ {q} →
  SSP → SCMCF.ShiftContractMdlLevelCoarseFibre q → Nat
forcedStableCountField p x = FDH.forcedStableCount p (primeField x)

orbitSummaryField :
  ∀ {q} →
  SSP → SCMCF.ShiftContractMdlLevelCoarseFibre q → FOS.DefectOrbitSummary
orbitSummaryField p x =
  FOS.profileSummaryAt p (primeField x)
