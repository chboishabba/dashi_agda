module DASHI.Physics.Closure.ShiftContractMdlLevelOrbitSummaryControlAttempt where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (cong)

open import MonsterOntos using (p2)
import Ontology.Hecke.FactorVecDefectOrbitSummaries as FOS

open import DASHI.Physics.Closure.ShiftContractMdlLevelCoarseFibre as SCMCF
open import DASHI.Physics.Closure.ShiftContractMdlLevelCoarseFibreFields as SCMFF
open import DASHI.Physics.Closure.ShiftContractMdlLevelCoarseObservable as SCMCO
open import DASHI.Physics.Closure.ShiftContractMdlLevelCounterexampleAudit as SCMA
open import DASHI.Physics.Closure.ShiftContractNoncanonicalP2ControlObstruction as OB

------------------------------------------------------------------------
-- Orbit-summary control attempt on the normalized surface
-- `mdlLevel × π-max`.
--
-- The exact equality
--   π-mdl-max x ≡ π-mdl-max y
-- is still too weak to derive a positive orbit-summary theorem from the
-- current lemmas alone.  The strongest useful theorem we can support on this
-- surface is that the p2 orbit-summary is stable under equality of the
-- transported prime field.  The old coarse obstruction pair is no longer the
-- relevant blocker on this stronger surface, because it is already separated
-- by the mdl-level package.

private
  _≢_ : {A : Set} → A → A → Set
  x ≢ y = x ≡ y → ⊥

orbitSummaryAtP2 :
  ∀ {q} →
  SCMCF.ShiftContractMdlLevelCoarseFibre q → FOS.DefectOrbitSummary
orbitSummaryAtP2 x = SCMFF.orbitSummaryField p2 x

orbitSummaryAtP2-respects-primeField :
  ∀ {q} →
  (x y : SCMCF.ShiftContractMdlLevelCoarseFibre q) →
  SCMFF.primeField x ≡ SCMFF.primeField y →
  orbitSummaryAtP2 x ≡ orbitSummaryAtP2 y
orbitSummaryAtP2-respects-primeField _ _ eq =
  cong (FOS.profileSummaryAt p2) eq

record ShiftContractMdlLevelOrbitSummaryControlAttempt : Set₁ where
  field
    orbitSummaryP2 :
      ∀ {q} →
      SCMCF.ShiftContractMdlLevelCoarseFibre q → FOS.DefectOrbitSummary
    orbitSummaryP2-from-primeField :
      ∀ {q} →
      (x y : SCMCF.ShiftContractMdlLevelCoarseFibre q) →
      SCMFF.primeField x ≡ SCMFF.primeField y →
      orbitSummaryP2 x ≡ orbitSummaryP2 y
    oldPairSeparatedByMdlLevelSurface :
      SCMCO.π-mdl-max OB.coarseCounterexampleLeft
        ≢
      SCMCO.π-mdl-max OB.coarseCounterexampleRight

canonicalShiftContractMdlLevelOrbitSummaryControlAttempt :
  ShiftContractMdlLevelOrbitSummaryControlAttempt
canonicalShiftContractMdlLevelOrbitSummaryControlAttempt =
  record
    { orbitSummaryP2 = orbitSummaryAtP2
    ; orbitSummaryP2-from-primeField = orbitSummaryAtP2-respects-primeField
    ; oldPairSeparatedByMdlLevelSurface =
        ShiftContractMdlLevelCounterexampleAudit.oldPair-separated
          SCMA.canonicalShiftContractMdlLevelCounterexampleAudit
    }

open ShiftContractMdlLevelOrbitSummaryControlAttempt public
