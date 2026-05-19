module DASHI.Physics.Closure.ShiftContractEigenShadowOrbitSummaryObstruction where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Data.Product using (_,_; _×_)
open import Relation.Binary.PropositionalEquality using (cong₂)

open import MonsterOntos using (p2)
import Ontology.Hecke.FactorVecDefectOrbitSummaries as FOS

open import DASHI.Physics.Closure.CanonicalAbstractGaugeMatterInstance as CA
open import DASHI.Physics.Closure.CanonicalClosureCoarseObservable as CCO
open import DASHI.Physics.Closure.CanonicalClosureFibreFields as CCFF
open import DASHI.Physics.Closure.CanonicalClosureFibreEigenShadowObstruction as CCEO
open import DASHI.Physics.Closure.CanonicalClosureFibreOrbitSummaryControl as CCOC
open import DASHI.Physics.Closure.CanonicalClosureShiftScheduleBridge as CCSB
open import DASHI.Physics.Constraints.ConcreteInstance as CI

private
  _≢_ : {A : Set} → A → A → Set
  x ≢ y = x ≡ y → ⊥

------------------------------------------------------------------------
-- Fallback eigenShadow × π-max lane.
--
-- The canonical CP/CC pair already gives the strongest honest obstruction
-- we can package here: the normalized coarse-plus-eigenShadow surface agrees
-- on that pair, but the p2 orbit-summary key still splits it.

CanonicalEigenShadowNormalizedObservable : Set
CanonicalEigenShadowNormalizedObservable =
  CCO.MaximalCoarseObservable × (Nat × Nat)

canonicalEigenShadowNormalized :
  CCO.CanonicalCarrier → CanonicalEigenShadowNormalizedObservable
canonicalEigenShadowNormalized x =
  CCO.π-max x , CA.canonicalEigenShadowLevel x

sameCanonicalEigenShadowNormalized-CPCC :
  canonicalEigenShadowNormalized CI.CP
    ≡
  canonicalEigenShadowNormalized CI.CC
sameCanonicalEigenShadowNormalized-CPCC =
  cong₂ _,_
    (CCSB.closureMotifObservablePreserved CI.CP)
    (CA.canonicalEigenShadowPreserved CI.CP)

p2OrbitSummary-CPCC-obstructed :
  FOS.profileSummaryAt p2 (CCFF.primeField CCEO.coarseCP-in-CR-fibre)
    ≢
  FOS.profileSummaryAt p2 (CCFF.primeField CCOC.coarseCC-in-CR-fibre)
p2OrbitSummary-CPCC-obstructed =
  CCOC.p2OrbitSummary-sameFibre-CPCC-obstructed

record ShiftContractEigenShadowOrbitSummaryObstruction : Set₁ where
  field
    sameNormalizedSurface :
      canonicalEigenShadowNormalized CI.CP
        ≡
      canonicalEigenShadowNormalized CI.CC
    sameSurfaceButP2OrbitSummaryDiffers :
      FOS.profileSummaryAt p2 (CCFF.primeField CCEO.coarseCP-in-CR-fibre)
        ≢
      FOS.profileSummaryAt p2 (CCFF.primeField CCOC.coarseCC-in-CR-fibre)

canonicalShiftContractEigenShadowOrbitSummaryObstruction :
  ShiftContractEigenShadowOrbitSummaryObstruction
canonicalShiftContractEigenShadowOrbitSummaryObstruction =
  record
    { sameNormalizedSurface = sameCanonicalEigenShadowNormalized-CPCC
    ; sameSurfaceButP2OrbitSummaryDiffers = p2OrbitSummary-CPCC-obstructed
    }
