module DASHI.Physics.Closure.ShiftContractMdlLevelP2PrimeBridge where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (cong)

open import MonsterOntos using (p2)
import Ontology.Hecke.FactorVecDefectOrbitSummaries as FOS

open import DASHI.Physics.Closure.ShiftContractMdlLevelCoarseFibre as SCMCF
open import DASHI.Physics.Closure.ShiftContractMdlLevelCoarseFibreFields as SCMFF

------------------------------------------------------------------------
-- Clean bridge on the strengthened `mdlLevel × π-max` fibre.
--
-- The strongest theorem currently supported by the existing lemmas is that
-- equality of the transported prime field on the mdl-level fibre forces
-- equality of the `p2` orbit summary.  From that bridge, we can safely
-- project a few summary coordinates such as forced-stable count and total
-- drift.  No additional `heckeField` or `eigenShadowField` theorem is
-- claimed here.

orbitSummaryAtP2 :
  ∀ {q} →
  SCMCF.ShiftContractMdlLevelCoarseFibre q → FOS.DefectOrbitSummary
orbitSummaryAtP2 x = SCMFF.orbitSummaryField p2 x

orbitSummaryAtP2-from-primeField :
  ∀ {q} →
  (x y : SCMCF.ShiftContractMdlLevelCoarseFibre q) →
  SCMFF.primeField x ≡ SCMFF.primeField y →
  orbitSummaryAtP2 x ≡ orbitSummaryAtP2 y
orbitSummaryAtP2-from-primeField _ _ eq =
  cong (FOS.profileSummaryAt p2) eq

orbitSummaryAtP2-forcedStableCount :
  ∀ {q} →
  (x y : SCMCF.ShiftContractMdlLevelCoarseFibre q) →
  SCMFF.primeField x ≡ SCMFF.primeField y →
  FOS.DefectOrbitSummary.forcedStableCount (orbitSummaryAtP2 x)
    ≡
  FOS.DefectOrbitSummary.forcedStableCount (orbitSummaryAtP2 y)
orbitSummaryAtP2-forcedStableCount x y eq =
  cong FOS.DefectOrbitSummary.forcedStableCount
    (orbitSummaryAtP2-from-primeField x y eq)

orbitSummaryAtP2-totalDrift :
  ∀ {q} →
  (x y : SCMCF.ShiftContractMdlLevelCoarseFibre q) →
  SCMFF.primeField x ≡ SCMFF.primeField y →
  FOS.DefectOrbitSummary.totalDrift (orbitSummaryAtP2 x)
    ≡
  FOS.DefectOrbitSummary.totalDrift (orbitSummaryAtP2 y)
orbitSummaryAtP2-totalDrift x y eq =
  cong FOS.DefectOrbitSummary.totalDrift
    (orbitSummaryAtP2-from-primeField x y eq)

orbitSummaryAtP2-repatterningCount :
  ∀ {q} →
  (x y : SCMCF.ShiftContractMdlLevelCoarseFibre q) →
  SCMFF.primeField x ≡ SCMFF.primeField y →
  FOS.DefectOrbitSummary.repatterningCount (orbitSummaryAtP2 x)
    ≡
  FOS.DefectOrbitSummary.repatterningCount (orbitSummaryAtP2 y)
orbitSummaryAtP2-repatterningCount x y eq =
  cong FOS.DefectOrbitSummary.repatterningCount
    (orbitSummaryAtP2-from-primeField x y eq)

orbitSummaryAtP2-contractveCount :
  ∀ {q} →
  (x y : SCMCF.ShiftContractMdlLevelCoarseFibre q) →
  SCMFF.primeField x ≡ SCMFF.primeField y →
  FOS.DefectOrbitSummary.contractiveCount (orbitSummaryAtP2 x)
    ≡
  FOS.DefectOrbitSummary.contractiveCount (orbitSummaryAtP2 y)
orbitSummaryAtP2-contractveCount x y eq =
  cong FOS.DefectOrbitSummary.contractiveCount
    (orbitSummaryAtP2-from-primeField x y eq)

orbitSummaryAtP2-expansiveCount :
  ∀ {q} →
  (x y : SCMCF.ShiftContractMdlLevelCoarseFibre q) →
  SCMFF.primeField x ≡ SCMFF.primeField y →
  FOS.DefectOrbitSummary.expansiveCount (orbitSummaryAtP2 x)
    ≡
  FOS.DefectOrbitSummary.expansiveCount (orbitSummaryAtP2 y)
orbitSummaryAtP2-expansiveCount x y eq =
  cong FOS.DefectOrbitSummary.expansiveCount
    (orbitSummaryAtP2-from-primeField x y eq)

record ShiftContractMdlLevelP2PrimeBridge : Set₁ where
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
    primeField-controls-totalDrift :
      ∀ {q} →
      (x y : SCMCF.ShiftContractMdlLevelCoarseFibre q) →
      SCMFF.primeField x ≡ SCMFF.primeField y →
      FOS.DefectOrbitSummary.totalDrift (orbitSummaryP2 x)
        ≡
      FOS.DefectOrbitSummary.totalDrift (orbitSummaryP2 y)

canonicalShiftContractMdlLevelP2PrimeBridge :
  ShiftContractMdlLevelP2PrimeBridge
canonicalShiftContractMdlLevelP2PrimeBridge =
  record
    { orbitSummaryP2 = orbitSummaryAtP2
    ; primeField-controls-orbitSummaryP2 = orbitSummaryAtP2-from-primeField
    ; primeField-controls-forcedStableCount = orbitSummaryAtP2-forcedStableCount
    ; primeField-controls-totalDrift = orbitSummaryAtP2-totalDrift
    }

open ShiftContractMdlLevelP2PrimeBridge public

