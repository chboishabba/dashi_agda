module DASHI.Physics.Closure.ShiftContractEigenShadowOrbitSummaryControlAttempt where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)

open import MonsterOntos using (p2)
import Ontology.Hecke.FactorVecDefectOrbitSummaries as FOS

open import DASHI.Physics.Closure.CanonicalClosureCoarseObservable as CCO
open import DASHI.Physics.Closure.CanonicalClosureFibre as CCF
open import DASHI.Physics.Closure.CanonicalClosureFibreFields as CCFF
open import DASHI.Physics.Closure.CanonicalAbstractGaugeMatterInstance as CA
open import DASHI.Physics.Closure.CanonicalClosureFibreEigenShadowObstruction as CCEO
  using (coarseCP-in-CR-fibre)
open import DASHI.Physics.Closure.CanonicalClosureFibreOrbitSummaryControl as CCOC
  using (coarseCC-in-CR-fibre)
open import DASHI.Physics.Closure.ShiftContractEigenShadowOrbitSummaryObstruction as SEOSO
  using
    ( sameCanonicalEigenShadowNormalized-CPCC
    ; p2OrbitSummary-CPCC-obstructed
    )
open import DASHI.Physics.Constraints.ConcreteInstance as CI

------------------------------------------------------------------------
-- Fallback eigenShadow × π-max lane.
--
-- The normalized surface is still not strong enough to recover the p2 orbit
-- summary on the canonical fibre.  This packages the sharpest honest
-- obstruction that is strictly beyond the current projection candidate: the
-- CP/CC witness pair already agrees on the normalized surface, but the p2
-- orbit summary still splits.

private
  _≢_ : {A : Set} → A → A → Set
  x ≢ y = x ≡ y → ⊥

NormalizedEigenShadowSurface : Set
NormalizedEigenShadowSurface =
  CCO.MaximalCoarseObservable × (Nat × Nat)

canonicalNormalizedEigenShadow :
  CCO.CanonicalCarrier → NormalizedEigenShadowSurface
canonicalNormalizedEigenShadow x =
  CCO.π-max x , CA.canonicalEigenShadowLevel x

canonicalSameSurfaceButNoP2OrbitSummaryControl :
  (∀ {q} →
    (x y : CCF.CanonicalFibre q) →
    canonicalNormalizedEigenShadow (CCF.carrier x)
      ≡
    canonicalNormalizedEigenShadow (CCF.carrier y) →
    FOS.profileSummaryAt p2 (CCFF.primeField x)
      ≡
    FOS.profileSummaryAt p2 (CCFF.primeField y)) →
  ⊥
canonicalSameSurfaceButNoP2OrbitSummaryControl controls =
  p2OrbitSummary-CPCC-obstructed
    (controls
      coarseCP-in-CR-fibre
      coarseCC-in-CR-fibre
      sameCanonicalEigenShadowNormalized-CPCC)
