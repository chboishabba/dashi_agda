module DASHI.Physics.Closure.CanonicalClosureFibreDefectFactorization where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Nat using (zero)
open import Data.Nat using (_≤_)

open import MonsterOntos using (SSP)
import Ontology.Hecke.FactorVecTransportChambers as FTC
import Ontology.Hecke.FactorVecDefectHistograms as FDH
import Ontology.Hecke.FactorVecDefectOrbitSummaries as FOS
import Ontology.Hecke.FactorVecDefectProfileCorrespondence as FDPC
import Ontology.Hecke.FactorVecChamberDefectProfileCorrespondence as FCDPC
open import Ontology.Hecke.FactorVecMultiLaneDefects using
  (PairDefectProfile; PairDefectClass; Stable)
open import Ontology.Hecke.FactorVecOrbitForcedStableLowerBound using
  (forcedStableCount≤orbitForcedStable)
import Ontology.Hecke.FactorVecMultiLaneTransport as FMT
open import Ontology.Hecke.FactorVecMultiLaneTransport using (pairMode)

open import DASHI.Physics.Closure.CanonicalClosureFibre as CCF
open import DASHI.Physics.Closure.CanonicalClosureFibreFields as CCFF

------------------------------------------------------------------------
-- First richer factorization layer on the canonical closure fibre:
-- the non-descending channels now factor through explicit defect-profile and
-- orbit-summary carriers on each transported prime representative.

defectProfileEntryField :
  ∀ {q} →
  SSP → SSP → CCF.CanonicalFibre q → PairDefectProfile
defectProfileEntryField p q' x =
  FDPC.defectProfileAt q' p (CCFF.primeField x)

defectHistogramField :
  ∀ {q} →
  SSP → CCF.CanonicalFibre q → FDH.DefectHistogram
defectHistogramField p x =
  FDH.defectHistogramOf p (CCFF.primeField x)

orbitSummaryField :
  ∀ {q} →
  SSP → CCF.CanonicalFibre q → FOS.DefectOrbitSummary
orbitSummaryField p x =
  FOS.profileSummaryAt p (CCFF.primeField x)

sameFibreChamber-forces-profileStableAt :
  ∀ {q} q' p (x y : CCF.CanonicalFibre q) →
  FTC.samePairChamber (CCFF.primeField x) (CCFF.primeField y) →
  FMT.pairLegal
    (pairMode q' p)
    (CCFF.primeField x)
    ≡
  false →
  PairDefectProfile.defect (defectProfileEntryField p q' y) ≡ Stable
sameFibreChamber-forces-profileStableAt q' p x y chamberEq illegalLeft =
  FCDPC.samePairChamber-forces-profileStableAt
    q'
    p
    (CCFF.primeField x)
    (CCFF.primeField y)
    chamberEq
    illegalLeft

sameFibreChamber-forces-profileDriftZeroAt :
  ∀ {q} q' p (x y : CCF.CanonicalFibre q) →
  FTC.samePairChamber (CCFF.primeField x) (CCFF.primeField y) →
  FMT.pairLegal
    (pairMode q' p)
    (CCFF.primeField x)
    ≡
  false →
  PairDefectProfile.drift (defectProfileEntryField p q' y) ≡ zero
sameFibreChamber-forces-profileDriftZeroAt q' p x y chamberEq illegalLeft =
  FCDPC.samePairChamber-forces-profileDriftZeroAt
    q'
    p
    (CCFF.primeField x)
    (CCFF.primeField y)
    chamberEq
    illegalLeft

forcedStableCountField≤orbitSummaryStableCount :
  ∀ {q} p (x : CCF.CanonicalFibre q) →
  CCFF.forcedStableCountField p x
    ≤
  FOS.DefectOrbitSummary.forcedStableCount (orbitSummaryField p x)
forcedStableCountField≤orbitSummaryStableCount p x =
  forcedStableCount≤orbitForcedStable p (CCFF.primeField x)
