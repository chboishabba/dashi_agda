module DASHI.Physics.Closure.CanonicalClosureFibreOrbitSummaryControl where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (_,_)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (sym)

open import MonsterOntos using (p2)
import Ontology.Hecke.FactorVecDefectOrbitSummaries as FOS

open import DASHI.Physics.Closure.CanonicalClosureFibre as CCF
open import DASHI.Physics.Closure.CanonicalClosureFibreFields as CCFF
open import DASHI.Physics.Closure.CanonicalClosureFibreEigenShadowObstruction as CCEO
open import DASHI.Physics.Constraints.ConcreteInstance as CI

------------------------------------------------------------------------
-- First direct test of whether the richer orbit-summary carrier detects the
-- same-fibre variation already exhibited by `eigenShadow`.

private
  _≢_ : {A : Set} → A → A → Set
  x ≢ y = x ≡ y → ⊥

orbitSummary-sameFibre-CRCP-obstructed :
  FOS.sameOrbitSummary
    (CCFF.primeField CCEO.coarseCR-fibre)
    (CCFF.primeField CCEO.coarseCP-in-CR-fibre)
    → ⊥
orbitSummary-sameFibre-CRCP-obstructed ()

p2OrbitSummary-sameFibre-CRCP-obstructed :
  FOS.profileSummaryAt p2 (CCFF.primeField CCEO.coarseCR-fibre)
    ≡
  FOS.profileSummaryAt p2 (CCFF.primeField CCEO.coarseCP-in-CR-fibre)
    → ⊥
p2OrbitSummary-sameFibre-CRCP-obstructed ()

coarseCC-in-CR-fibre : CCF.CanonicalFibre (CCF.π CI.CR)
coarseCC-in-CR-fibre = CI.CC , refl

p2OrbitSummary-sameFibre-CRCC-obstructed :
  FOS.profileSummaryAt p2 (CCFF.primeField CCEO.coarseCR-fibre)
    ≡
  FOS.profileSummaryAt p2 (CCFF.primeField coarseCC-in-CR-fibre)
    → ⊥
p2OrbitSummary-sameFibre-CRCC-obstructed ()

p2OrbitSummary-sameFibre-CPCC-obstructed :
  FOS.profileSummaryAt p2 (CCFF.primeField CCEO.coarseCP-in-CR-fibre)
    ≡
  FOS.profileSummaryAt p2 (CCFF.primeField coarseCC-in-CR-fibre)
    → ⊥
p2OrbitSummary-sameFibre-CPCC-obstructed ()

p2-controls-eigenShadow-on-canonical-fibre :
  ∀ {q} →
  (x y : CCF.CanonicalFibre q) →
  FOS.profileSummaryAt p2 (CCFF.primeField x)
    ≡
  FOS.profileSummaryAt p2 (CCFF.primeField y) →
  CCFF.eigenShadowField x ≡ CCFF.eigenShadowField y
p2-controls-eigenShadow-on-canonical-fibre (CI.CR , _) (CI.CR , _) _ = refl
p2-controls-eigenShadow-on-canonical-fibre (CI.CR , _) (CI.CP , _) p2eq =
  Data.Empty.⊥-elim (p2OrbitSummary-sameFibre-CRCP-obstructed p2eq)
p2-controls-eigenShadow-on-canonical-fibre (CI.CR , _) (CI.CC , _) p2eq =
  Data.Empty.⊥-elim (p2OrbitSummary-sameFibre-CRCC-obstructed p2eq)
p2-controls-eigenShadow-on-canonical-fibre (CI.CP , _) (CI.CR , _) p2eq =
  Data.Empty.⊥-elim (p2OrbitSummary-sameFibre-CRCP-obstructed (sym p2eq))
p2-controls-eigenShadow-on-canonical-fibre (CI.CP , _) (CI.CP , _) _ = refl
p2-controls-eigenShadow-on-canonical-fibre (CI.CP , _) (CI.CC , _) p2eq =
  Data.Empty.⊥-elim (p2OrbitSummary-sameFibre-CPCC-obstructed p2eq)
p2-controls-eigenShadow-on-canonical-fibre (CI.CC , _) (CI.CR , _) p2eq =
  Data.Empty.⊥-elim (p2OrbitSummary-sameFibre-CRCC-obstructed (sym p2eq))
p2-controls-eigenShadow-on-canonical-fibre (CI.CC , _) (CI.CP , _) p2eq =
  Data.Empty.⊥-elim (p2OrbitSummary-sameFibre-CPCC-obstructed (sym p2eq))
p2-controls-eigenShadow-on-canonical-fibre (CI.CC , _) (CI.CC , _) _ = refl

p2-controls-hecke-on-canonical-fibre :
  ∀ {q} →
  (x y : CCF.CanonicalFibre q) →
  FOS.profileSummaryAt p2 (CCFF.primeField x)
    ≡
  FOS.profileSummaryAt p2 (CCFF.primeField y) →
  CCFF.heckeField x ≡ CCFF.heckeField y
p2-controls-hecke-on-canonical-fibre (CI.CR , _) (CI.CR , _) _ = refl
p2-controls-hecke-on-canonical-fibre (CI.CR , _) (CI.CP , _) p2eq =
  Data.Empty.⊥-elim (p2OrbitSummary-sameFibre-CRCP-obstructed p2eq)
p2-controls-hecke-on-canonical-fibre (CI.CR , _) (CI.CC , _) p2eq =
  Data.Empty.⊥-elim (p2OrbitSummary-sameFibre-CRCC-obstructed p2eq)
p2-controls-hecke-on-canonical-fibre (CI.CP , _) (CI.CR , _) p2eq =
  Data.Empty.⊥-elim (p2OrbitSummary-sameFibre-CRCP-obstructed (sym p2eq))
p2-controls-hecke-on-canonical-fibre (CI.CP , _) (CI.CP , _) _ = refl
p2-controls-hecke-on-canonical-fibre (CI.CP , _) (CI.CC , _) p2eq =
  Data.Empty.⊥-elim (p2OrbitSummary-sameFibre-CPCC-obstructed p2eq)
p2-controls-hecke-on-canonical-fibre (CI.CC , _) (CI.CR , _) p2eq =
  Data.Empty.⊥-elim (p2OrbitSummary-sameFibre-CRCC-obstructed (sym p2eq))
p2-controls-hecke-on-canonical-fibre (CI.CC , _) (CI.CP , _) p2eq =
  Data.Empty.⊥-elim (p2OrbitSummary-sameFibre-CPCC-obstructed (sym p2eq))
p2-controls-hecke-on-canonical-fibre (CI.CC , _) (CI.CC , _) _ = refl

------------------------------------------------------------------------
-- Quotient-facing surface:
-- package the canonical p2 control as an explicit factor law over a key map,
-- rather than only as a standalone implication theorem.

p2-key :
  ∀ {q} →
  CCF.CanonicalFibre q → FOS.DefectOrbitSummary
p2-key x = FOS.profileSummaryAt p2 (CCFF.primeField x)

record P2EigenShadowFactorLaw
  (q : CCF.CanonicalCoarseObservable)
  : Set where
  field
    key : CCF.CanonicalFibre q → FOS.DefectOrbitSummary
    eigenShadow-from-key :
      ∀ x y →
      key x ≡ key y →
      CCFF.eigenShadowField x ≡ CCFF.eigenShadowField y

canonicalP2EigenShadowFactorLaw :
  ∀ {q} →
  P2EigenShadowFactorLaw q
canonicalP2EigenShadowFactorLaw =
  record
    { key = p2-key
    ; eigenShadow-from-key = p2-controls-eigenShadow-on-canonical-fibre
    }

record P2HeckeFactorLaw
  (q : CCF.CanonicalCoarseObservable)
  : Set where
  field
    key : CCF.CanonicalFibre q → FOS.DefectOrbitSummary
    hecke-from-key :
      ∀ x y →
      key x ≡ key y →
      CCFF.heckeField x ≡ CCFF.heckeField y

canonicalP2HeckeFactorLaw :
  ∀ {q} →
  P2HeckeFactorLaw q
canonicalP2HeckeFactorLaw =
  record
    { key = p2-key
    ; hecke-from-key = p2-controls-hecke-on-canonical-fibre
    }
