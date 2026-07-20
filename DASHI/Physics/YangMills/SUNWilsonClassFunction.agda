module DASHI.Physics.YangMills.SUNWilsonClassFunction where

------------------------------------------------------------------------
-- Wilson trace observables for the concrete SU(N) matrix carrier.
-- Cyclicity/conjugation invariance of the finite matrix trace is supplied as a
-- standard imported authority fact; gauge invariance of every closed lattice
-- loop is then inherited from the checked generic holonomy theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.CompactLieGroupDerived using (conjugate)
open import DASHI.Physics.YangMills.CompactLieLatticeGauge
open import DASHI.Physics.YangMills.SUNMatrixCarrier

record SUNWilsonTraceAuthority
    {N : Nat} {Matrix Complex Scalar : Set}
    (theory : CertifiedSUNMatrixTheory N Matrix Complex) : Set₁ where
  field
    normalizedRealTrace : SUNMatrixElement theory → Scalar
    traceConjugationInvariant : ∀ h x →
      normalizedRealTrace
        (conjugate (sunMatrixGroup theory) h x)
      ≡ normalizedRealTrace x

open SUNWilsonTraceAuthority public

sunWilsonClassFunction :
  ∀ {N : Nat} {Matrix Complex Scalar : Set}
    {theory : CertifiedSUNMatrixTheory N Matrix Complex} →
  (authority : SUNWilsonTraceAuthority {Scalar = Scalar} theory) →
  ClassFunction (sunMatrixGroup theory) (normalizedRealTrace authority)
sunWilsonClassFunction authority = record
  { conjugationInvariant = traceConjugationInvariant authority }

sunWilsonLoopGaugeInvariant :
  ∀ {N : Nat} {Matrix Complex Scalar Vertex : Set}
    {theory : CertifiedSUNMatrixTheory N Matrix Complex}
    {Edge : Vertex → Vertex → Set}
    {base : Vertex} →
  (authority : SUNWilsonTraceAuthority {Scalar = Scalar} theory) →
  (gamma : GaugeTransformation Vertex (SUNMatrixElement theory)) →
  (U : GaugeField {G = SUNMatrixElement theory} Edge) →
  (path : Path Edge base base) →
  loopObservable
    (sunMatrixGroup theory)
    (normalizedRealTrace authority)
    (gaugeAction (sunMatrixGroup theory) gamma U)
    path
  ≡
  loopObservable
    (sunMatrixGroup theory)
    (normalizedRealTrace authority)
    U path
sunWilsonLoopGaugeInvariant {theory = theory} authority =
  loopObservableGaugeInvariant
    (sunMatrixGroup theory)
    (normalizedRealTrace authority)
    (sunWilsonClassFunction authority)

sunWilsonGaugeInvarianceLevel : ProofLevel
sunWilsonGaugeInvarianceLevel = machineChecked

sunTraceConjugationAuthorityLevel : ProofLevel
sunTraceConjugationAuthorityLevel = standardImported
