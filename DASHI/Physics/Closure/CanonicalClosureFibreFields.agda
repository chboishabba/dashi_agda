module DASHI.Physics.Closure.CanonicalClosureFibreFields where

open import Agda.Builtin.Sigma using (fst)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Product using (_×_)

open import MonsterOntos using (SSP)
open import Ontology.GodelLattice using (FactorVec)
import Ontology.Hecke.FactorVecTransportChambers as FTC
import Ontology.Hecke.FactorVecDefectHistograms as FDH
import Ontology.Hecke.FactorVecChamberDefectHistograms as FCDH
open import Ontology.Hecke.PrimeHeckeEigenMotifPipeline as PHEM
open import Ontology.Hecke.Scan as HS

open import DASHI.Physics.Closure.CanonicalAbstractGaugeMatterInstance as CA
open import DASHI.Physics.Closure.CanonicalChamberToShiftWitnessBridgeInstance as CCW
open import DASHI.Physics.Closure.CanonicalClosureFibre as CCF

------------------------------------------------------------------------
-- The non-descending channels are reinterpreted as fields over the coarse
-- closure fibre rather than as base observables.

heckeField :
  ∀ {q} →
  CCF.CanonicalFibre q → HS.Sig15
heckeField x = CA.canonicalSignatureLevel (CCF.carrier x)

eigenField :
  ∀ {q} →
  CCF.CanonicalFibre q → PHEM.EigenProfile
eigenField x = CA.canonicalEigenLevel (CCF.carrier x)

eigenShadowField :
  ∀ {q} →
  CCF.CanonicalFibre q → Nat × Nat
eigenShadowField x = CA.canonicalEigenShadowLevel (CCF.carrier x)

primeField :
  ∀ {q} →
  CCF.CanonicalFibre q → FactorVec
primeField x = CCW.closurePrimeEmbedding (CCF.carrier x)

illegalCountField :
  ∀ {q} →
  SSP → CCF.CanonicalFibre q → Agda.Builtin.Nat.Nat
illegalCountField p x = FDH.illegalCount p (primeField x)

forcedStableCountField :
  ∀ {q} →
  SSP → CCF.CanonicalFibre q → Agda.Builtin.Nat.Nat
forcedStableCountField p x = FDH.forcedStableCount p (primeField x)

sameFibreChamber-preserves-illegalCount :
  ∀ {q} p (x y : CCF.CanonicalFibre q) →
  FTC.samePairChamber (primeField x) (primeField y) →
  illegalCountField p x ≡ illegalCountField p y
sameFibreChamber-preserves-illegalCount p x y chamberEq =
  FCDH.samePairChamber-preserves-illegalCount
    p
    (primeField x)
    (primeField y)
    chamberEq

sameFibreChamber-preserves-forcedStableCount :
  ∀ {q} p (x y : CCF.CanonicalFibre q) →
  FTC.samePairChamber (primeField x) (primeField y) →
  forcedStableCountField p x ≡ forcedStableCountField p y
sameFibreChamber-preserves-forcedStableCount p x y chamberEq =
  FCDH.samePairChamber-preserves-forcedStableCount
    p
    (primeField x)
    (primeField y)
    chamberEq
