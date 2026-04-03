module DASHI.Physics.Closure.ShiftContractMdlLevelP2PrimeCorollaries where

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (cong)

open import MonsterOntos using (p2)
import Ontology.Hecke.FactorVecDefectOrbitSummaries as FOS

open import DASHI.Physics.Closure.ShiftContractMdlLevelCoarseFibre as SCMCF
open import DASHI.Physics.Closure.ShiftContractMdlLevelCoarseFibreFields as SCMFF
import DASHI.Physics.Closure.ShiftContractMdlLevelP2PrimeBridge as BP

------------------------------------------------------------------------
-- Safe corollaries on the mdl-level fibre.
--
-- The bridge theorem gives equality of the full `p2` orbit summary from
-- equality of the transported prime field.  From that, we can project all of
-- the orbit-summary coordinates that are actually present in the record.
-- No further `eigenShadowField` or `heckeField` consequence is claimed here.

orbitSummaryP2F :
  ∀ {q} →
  SCMCF.ShiftContractMdlLevelCoarseFibre q → FOS.DefectOrbitSummary
orbitSummaryP2F x =
  BP.orbitSummaryP2 BP.canonicalShiftContractMdlLevelP2PrimeBridge x

orbitSummaryP2F-from-primeField :
  ∀ {q} →
  (x y : SCMCF.ShiftContractMdlLevelCoarseFibre q) →
  SCMFF.primeField x ≡ SCMFF.primeField y →
  orbitSummaryP2F x ≡ orbitSummaryP2F y
orbitSummaryP2F-from-primeField x y =
  BP.primeField-controls-orbitSummaryP2
    BP.canonicalShiftContractMdlLevelP2PrimeBridge x y

p2OrbitSummary-forcedStableCount :
  ∀ {q} →
  (x y : SCMCF.ShiftContractMdlLevelCoarseFibre q) →
  SCMFF.primeField x ≡ SCMFF.primeField y →
  FOS.DefectOrbitSummary.forcedStableCount (orbitSummaryP2F x)
    ≡
  FOS.DefectOrbitSummary.forcedStableCount (orbitSummaryP2F y)
p2OrbitSummary-forcedStableCount x y eq =
  cong FOS.DefectOrbitSummary.forcedStableCount
    (orbitSummaryP2F-from-primeField x y eq)

p2OrbitSummary-motifChangeCount :
  ∀ {q} →
  (x y : SCMCF.ShiftContractMdlLevelCoarseFibre q) →
  SCMFF.primeField x ≡ SCMFF.primeField y →
  FOS.DefectOrbitSummary.motifChangeCount (orbitSummaryP2F x)
    ≡
  FOS.DefectOrbitSummary.motifChangeCount (orbitSummaryP2F y)
p2OrbitSummary-motifChangeCount x y eq =
  cong FOS.DefectOrbitSummary.motifChangeCount
    (orbitSummaryP2F-from-primeField x y eq)

p2OrbitSummary-totalDrift :
  ∀ {q} →
  (x y : SCMCF.ShiftContractMdlLevelCoarseFibre q) →
  SCMFF.primeField x ≡ SCMFF.primeField y →
  FOS.DefectOrbitSummary.totalDrift (orbitSummaryP2F x)
    ≡
  FOS.DefectOrbitSummary.totalDrift (orbitSummaryP2F y)
p2OrbitSummary-totalDrift x y eq =
  cong FOS.DefectOrbitSummary.totalDrift
    (orbitSummaryP2F-from-primeField x y eq)

p2OrbitSummary-repatterningCount :
  ∀ {q} →
  (x y : SCMCF.ShiftContractMdlLevelCoarseFibre q) →
  SCMFF.primeField x ≡ SCMFF.primeField y →
  FOS.DefectOrbitSummary.repatterningCount (orbitSummaryP2F x)
    ≡
  FOS.DefectOrbitSummary.repatterningCount (orbitSummaryP2F y)
p2OrbitSummary-repatterningCount x y eq =
  cong FOS.DefectOrbitSummary.repatterningCount
    (orbitSummaryP2F-from-primeField x y eq)

p2OrbitSummary-contractiveCount :
  ∀ {q} →
  (x y : SCMCF.ShiftContractMdlLevelCoarseFibre q) →
  SCMFF.primeField x ≡ SCMFF.primeField y →
  FOS.DefectOrbitSummary.contractiveCount (orbitSummaryP2F x)
    ≡
  FOS.DefectOrbitSummary.contractiveCount (orbitSummaryP2F y)
p2OrbitSummary-contractiveCount x y eq =
  cong FOS.DefectOrbitSummary.contractiveCount
    (orbitSummaryP2F-from-primeField x y eq)

p2OrbitSummary-expansiveCount :
  ∀ {q} →
  (x y : SCMCF.ShiftContractMdlLevelCoarseFibre q) →
  SCMFF.primeField x ≡ SCMFF.primeField y →
  FOS.DefectOrbitSummary.expansiveCount (orbitSummaryP2F x)
    ≡
  FOS.DefectOrbitSummary.expansiveCount (orbitSummaryP2F y)
p2OrbitSummary-expansiveCount x y eq =
  cong FOS.DefectOrbitSummary.expansiveCount
    (orbitSummaryP2F-from-primeField x y eq)

record ShiftContractMdlLevelP2PrimeCorollaries : Set₁ where
  field
    orbitSummaryP2 :
      ∀ {q} →
      SCMCF.ShiftContractMdlLevelCoarseFibre q → FOS.DefectOrbitSummary
    primeField-controls-orbitSummaryP2 :
      ∀ {q} →
      (x y : SCMCF.ShiftContractMdlLevelCoarseFibre q) →
      SCMFF.primeField x ≡ SCMFF.primeField y →
      orbitSummaryP2 x ≡ orbitSummaryP2 y
    primeField-controls-forcedStableCount :
      ∀ {q} →
      (x y : SCMCF.ShiftContractMdlLevelCoarseFibre q) →
      SCMFF.primeField x ≡ SCMFF.primeField y →
      FOS.DefectOrbitSummary.forcedStableCount (orbitSummaryP2 x)
        ≡
      FOS.DefectOrbitSummary.forcedStableCount (orbitSummaryP2 y)
    primeField-controls-motifChangeCount :
      ∀ {q} →
      (x y : SCMCF.ShiftContractMdlLevelCoarseFibre q) →
      SCMFF.primeField x ≡ SCMFF.primeField y →
      FOS.DefectOrbitSummary.motifChangeCount (orbitSummaryP2 x)
        ≡
      FOS.DefectOrbitSummary.motifChangeCount (orbitSummaryP2 y)
    primeField-controls-totalDrift :
      ∀ {q} →
      (x y : SCMCF.ShiftContractMdlLevelCoarseFibre q) →
      SCMFF.primeField x ≡ SCMFF.primeField y →
      FOS.DefectOrbitSummary.totalDrift (orbitSummaryP2 x)
        ≡
      FOS.DefectOrbitSummary.totalDrift (orbitSummaryP2 y)
    primeField-controls-repatterningCount :
      ∀ {q} →
      (x y : SCMCF.ShiftContractMdlLevelCoarseFibre q) →
      SCMFF.primeField x ≡ SCMFF.primeField y →
      FOS.DefectOrbitSummary.repatterningCount (orbitSummaryP2 x)
        ≡
      FOS.DefectOrbitSummary.repatterningCount (orbitSummaryP2 y)
    primeField-controls-contractiveCount :
      ∀ {q} →
      (x y : SCMCF.ShiftContractMdlLevelCoarseFibre q) →
      SCMFF.primeField x ≡ SCMFF.primeField y →
      FOS.DefectOrbitSummary.contractiveCount (orbitSummaryP2 x)
        ≡
      FOS.DefectOrbitSummary.contractiveCount (orbitSummaryP2 y)
    primeField-controls-expansiveCount :
      ∀ {q} →
      (x y : SCMCF.ShiftContractMdlLevelCoarseFibre q) →
      SCMFF.primeField x ≡ SCMFF.primeField y →
      FOS.DefectOrbitSummary.expansiveCount (orbitSummaryP2 x)
        ≡
      FOS.DefectOrbitSummary.expansiveCount (orbitSummaryP2 y)

canonicalShiftContractMdlLevelP2PrimeCorollaries :
  ShiftContractMdlLevelP2PrimeCorollaries
canonicalShiftContractMdlLevelP2PrimeCorollaries =
  record
    { orbitSummaryP2 = orbitSummaryP2F
    ; primeField-controls-orbitSummaryP2 = orbitSummaryP2F-from-primeField
    ; primeField-controls-forcedStableCount = p2OrbitSummary-forcedStableCount
    ; primeField-controls-motifChangeCount = p2OrbitSummary-motifChangeCount
    ; primeField-controls-totalDrift = p2OrbitSummary-totalDrift
    ; primeField-controls-repatterningCount = p2OrbitSummary-repatterningCount
    ; primeField-controls-contractiveCount = p2OrbitSummary-contractiveCount
    ; primeField-controls-expansiveCount = p2OrbitSummary-expansiveCount
    }
