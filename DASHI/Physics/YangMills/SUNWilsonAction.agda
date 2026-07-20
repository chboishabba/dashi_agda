module DASHI.Physics.YangMills.SUNWilsonAction where

------------------------------------------------------------------------
-- Finite Wilson action for concrete SU(N) matrix links.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (cong; cong₂)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.CompactLieLatticeGauge
open import DASHI.Physics.YangMills.SUNMatrixCarrier
open import DASHI.Physics.YangMills.SUNWilsonClassFunction

record WilsonScalarOperations (Scalar : Set) : Set₁ where
  field
    zeroS oneS : Scalar
    addS subtractS : Scalar → Scalar → Scalar

open WilsonScalarOperations public

wilsonPlaquetteValue :
  ∀ {N : Nat} {Matrix Complex Scalar : Set}
    {theory : CertifiedSUNMatrixTheory N Matrix Complex} →
  WilsonScalarOperations Scalar →
  SUNWilsonTraceAuthority {Scalar = Scalar} theory →
  SUNMatrixElement theory → Scalar
wilsonPlaquetteValue scalarOps authority U =
  subtractS scalarOps (oneS scalarOps) (normalizedRealTrace authority U)

wilsonPlaquetteClassFunction :
  ∀ {N : Nat} {Matrix Complex Scalar : Set}
    {theory : CertifiedSUNMatrixTheory N Matrix Complex} →
  (scalarOps : WilsonScalarOperations Scalar) →
  (authority : SUNWilsonTraceAuthority {Scalar = Scalar} theory) →
  ClassFunction
    (sunMatrixGroup theory)
    (wilsonPlaquetteValue scalarOps authority)
wilsonPlaquetteClassFunction scalarOps authority = record
  { conjugationInvariant = λ h x →
      cong
        (subtractS scalarOps (oneS scalarOps))
        (traceConjugationInvariant authority h x)
  }

record SUNWilsonActionData
    {N : Nat} {Matrix Complex Scalar Vertex : Set}
    (theory : CertifiedSUNMatrixTheory N Matrix Complex)
    (Edge : Vertex → Vertex → Set) : Set₁ where
  field
    Plaquette : Set
    plaquettes : List Plaquette
    plaquetteBase : Plaquette → Vertex
    plaquetteBoundary :
      (plaquette : Plaquette) →
      Path Edge (plaquetteBase plaquette) (plaquetteBase plaquette)
    scalarOperations : WilsonScalarOperations Scalar
    traceAuthority : SUNWilsonTraceAuthority {Scalar = Scalar} theory

open SUNWilsonActionData public

sunWilsonActionFrom :
  ∀ {N : Nat} {Matrix Complex Scalar Vertex : Set}
    {theory : CertifiedSUNMatrixTheory N Matrix Complex}
    {Edge : Vertex → Vertex → Set} →
  (dataSet : SUNWilsonActionData {Scalar = Scalar} theory Edge) →
  List (Plaquette dataSet) → GaugeField {G = SUNMatrixElement theory} Edge → Scalar
sunWilsonActionFrom dataSet [] U = zeroS (scalarOperations dataSet)
sunWilsonActionFrom dataSet (plaquette ∷ rest) U =
  addS (scalarOperations dataSet)
    (loopObservable
      (sunMatrixGroup _)
      (wilsonPlaquetteValue
        (scalarOperations dataSet)
        (traceAuthority dataSet))
      U
      (plaquetteBoundary dataSet plaquette))
    (sunWilsonActionFrom dataSet rest U)

sunWilsonAction :
  ∀ {N : Nat} {Matrix Complex Scalar Vertex : Set}
    {theory : CertifiedSUNMatrixTheory N Matrix Complex}
    {Edge : Vertex → Vertex → Set} →
  (dataSet : SUNWilsonActionData {Scalar = Scalar} theory Edge) →
  GaugeField {G = SUNMatrixElement theory} Edge → Scalar
sunWilsonAction dataSet = sunWilsonActionFrom dataSet (plaquettes dataSet)

sunWilsonActionFromGaugeInvariant :
  ∀ {N : Nat} {Matrix Complex Scalar Vertex : Set}
    {theory : CertifiedSUNMatrixTheory N Matrix Complex}
    {Edge : Vertex → Vertex → Set} →
  (dataSet : SUNWilsonActionData {Scalar = Scalar} theory Edge) →
  (selected : List (Plaquette dataSet)) →
  (gamma : GaugeTransformation Vertex (SUNMatrixElement theory)) →
  (U : GaugeField {G = SUNMatrixElement theory} Edge) →
  sunWilsonActionFrom dataSet selected
    (gaugeAction (sunMatrixGroup theory) gamma U)
  ≡ sunWilsonActionFrom dataSet selected U
sunWilsonActionFromGaugeInvariant dataSet [] gamma U = refl
sunWilsonActionFromGaugeInvariant dataSet (plaquette ∷ rest) gamma U =
  cong₂
    (addS (scalarOperations dataSet))
    (loopObservableGaugeInvariant
      (sunMatrixGroup _)
      (wilsonPlaquetteValue
        (scalarOperations dataSet)
        (traceAuthority dataSet))
      (wilsonPlaquetteClassFunction
        (scalarOperations dataSet)
        (traceAuthority dataSet))
      gamma U
      (plaquetteBoundary dataSet plaquette))
    (sunWilsonActionFromGaugeInvariant dataSet rest gamma U)

sunWilsonActionGaugeInvariant :
  ∀ {N : Nat} {Matrix Complex Scalar Vertex : Set}
    {theory : CertifiedSUNMatrixTheory N Matrix Complex}
    {Edge : Vertex → Vertex → Set} →
  (dataSet : SUNWilsonActionData {Scalar = Scalar} theory Edge) →
  (gamma : GaugeTransformation Vertex (SUNMatrixElement theory)) →
  (U : GaugeField {G = SUNMatrixElement theory} Edge) →
  sunWilsonAction dataSet (gaugeAction (sunMatrixGroup theory) gamma U)
  ≡ sunWilsonAction dataSet U
sunWilsonActionGaugeInvariant dataSet =
  sunWilsonActionFromGaugeInvariant dataSet (plaquettes dataSet)

sunWilsonActionGaugeInvarianceLevel : ProofLevel
sunWilsonActionGaugeInvarianceLevel = machineChecked

sunWilsonTraceAuthorityLevel : ProofLevel
sunWilsonTraceAuthorityLevel = standardImported
