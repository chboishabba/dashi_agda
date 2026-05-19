module DASHI.Physics.Closure.FactorVecPhysicalLawProjectionTheorem where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.Sigma using (Σ; _,_)

open import MonsterOntos using (SSP; toNat)
open import Ontology.GodelLattice using (FactorVec)
open import Ontology.GodelScalarization as GS using (G; ScalarTransportStep; target)

------------------------------------------------------------------------
-- Physical laws as projections, variational constraints, and conservation
-- laws over the canonical 15SSP exponent carrier.
------------------------------------------------------------------------

data Signature31 : Set where
  sig31 : Signature31

record FactorVecProjectionStack : Set₂ where
  field
    Real Complex : Set

    -- Projection surfaces from F = Nat^15.
    Geometry Spin Gauge Matter Observable : Set
    π-geo    : FactorVec → Geometry
    π-spin   : FactorVec → Spin
    π-gauge  : FactorVec → Gauge
    π-matter : FactorVec → Matter
    π-obs    : FactorVec → Observable

    -- 1. Geometry from a quadratic projection.
    Q           : FactorVec → Real
    sig-Q       : Signature31
    M-F         : Set
    quotient    : FactorVec → M-F
    metric      : M-F → M-F → Real
    Lorentz     : Set
    actLorentz  : Lorentz → FactorVec → FactorVec
    lorentz-invariant :
      ∀ Λ v → Q (actLorentz Λ v) ≡ Q v

    -- 2. Clifford / spinor law.
    Clifford Spinor DiracOperator Mass : Set
    gamma       : Geometry → Clifford
    spinorField : FactorVec → Spinor
    dirac       : FactorVec → DiracOperator
    mass        : FactorVec → Mass
    clifford-law : Set
    dirac-law    : Set

    -- 3-4. Gauge and Yang-Mills law.
    GaugeGroup LieAlgebra Connection Curvature Current : Set
    gaugeGroup      : GaugeGroup
    gaugeLie        : GaugeGroup → LieAlgebra
    connection      : FactorVec → Connection
    curvature       : FactorVec → Curvature
    gaugeTransform  : GaugeGroup → Connection → Connection
    current         : FactorVec → Current
    gauge-invariant : Set
    yang-mills-law  : Set

    -- 5. Matter and Euler-Lagrange law.
    MatterField Potential Lagrangian : Set
    matterField          : FactorVec → MatterField
    potential            : FactorVec → Potential
    lagrangian           : FactorVec → Lagrangian
    euler-lagrange-law   : Set

    -- 6-7. Stress-energy and Einstein law.
    StressEnergy EinsteinTensor CosmologicalProjection CouplingProjection : Set
    stressEnergy          : FactorVec → StressEnergy
    einsteinTensor        : FactorVec → EinsteinTensor
    cosmologicalProjection : FactorVec → CosmologicalProjection
    couplingProjection     : FactorVec → CouplingProjection
    stress-energy-law     : Set
    einstein-law          : Set

    -- 8. Quantum law over FactorVec.
    Amplitude Hamiltonian Probability Observation : Set
    amplitude       : FactorVec → Amplitude
    hamiltonian     : Hamiltonian
    probability     : Observable → Probability
    observe         : FactorVec → Observation
    normalization-law : Set
    schrodinger-law   : Set
    born-law          : Set

    -- 9. Transport / interaction law.
    LegalTransport : SSP → SSP → FactorVec → Set
    transportStep  :
      ∀ p q v → LegalTransport p q v → ScalarTransportStep p q v
    defect         :
      ∀ p q v → LegalTransport p q v → FactorVec
    interactionEnergy :
      ∀ p q v → LegalTransport p q v → Real

    -- 10. MDL / action principle.
    L-model L-residual H-baseline PE Action : FactorVec → Nat
    action-mdl-law :
      ∀ v → Action v ≡ L-model v + L-residual v
    mdl-descent :
      FactorVec → FactorVec → Set
    stationary-action : Set

    -- 11. Post-entropy observable law.
    post-entropy-law :
      ∀ v → PE v + H-baseline v ≡ L-model v + L-residual v
    observable-promotion : FactorVec → Set
    promoted-observable-stable :
      ∀ p q v →
      (legal : LegalTransport p q v) →
      observable-promotion v →
      observable-promotion (target (transportStep p q v legal))

    -- 12. Empirical observable surface.
    DataPoint Residual Sigma ChiSquared : Set
    prediction   : Observable → DataPoint
    observedData : Observable → DataPoint
    sigma        : Observable → Sigma
    χ²-F       : ChiSquared
    empirical-observable-law : Set

open FactorVecProjectionStack public

Interact :
  (stack : FactorVecProjectionStack) →
  FactorVec → FactorVec → Set
Interact stack v w =
  Σ SSP λ p →
  Σ SSP λ q →
  Σ (LegalTransport stack p q v) λ legal →
    target (transportStep stack p q v legal) ≡ w

record FactorVecPhysicalRecovery
  (stack : FactorVecProjectionStack) : Set₁ where
  field
    geometryRecovered     : Set
    spinRecovered         : Set
    gaugeRecovered        : Set
    matterRecovered       : Set
    waveDynamicsRecovered : Set
    stressEnergyRecovered : Set
    empiricalContact      : Set

    geometryWitness     : geometryRecovered
    spinWitness         : spinRecovered
    gaugeWitness        : gaugeRecovered
    matterWitness       : matterRecovered
    waveDynamicsWitness : waveDynamicsRecovered
    stressEnergyWitness : stressEnergyRecovered
    empiricalWitness    : empiricalContact

    actionStationaryWitness :
      stationary-action stack

    observableLawWitness :
      empirical-observable-law stack

open FactorVecPhysicalRecovery public

record AdmissiblePhysicalCarrier : Set₂ where
  field
    X : Set
    toFactorVec : X → FactorVec

    Admissible Stable ReceiptBound : Set

    stack : FactorVecProjectionStack

    closureWitness :
      Admissible →
      Stable →
      ReceiptBound →
      FactorVecPhysicalRecovery stack

open AdmissiblePhysicalCarrier public

factorVecPhysicalClosure :
  (carrier : AdmissiblePhysicalCarrier) →
  Admissible carrier →
  Stable carrier →
  ReceiptBound carrier →
  Σ FactorVecProjectionStack FactorVecPhysicalRecovery
factorVecPhysicalClosure carrier admissible stable receiptBound =
  stack carrier ,
  closureWitness carrier admissible stable receiptBound

record FactorVecPhysicalLawProjectionTheorem : Set₂ where
  field
    carrier : AdmissiblePhysicalCarrier
    theorem :
      Admissible carrier →
      Stable carrier →
      ReceiptBound carrier →
      Σ FactorVecProjectionStack FactorVecPhysicalRecovery

open FactorVecPhysicalLawProjectionTheorem public

canonicalFactorVecPhysicalLawProjectionTheorem :
  (carrier : AdmissiblePhysicalCarrier) →
  FactorVecPhysicalLawProjectionTheorem
canonicalFactorVecPhysicalLawProjectionTheorem carrier =
  record
    { carrier = carrier
    ; theorem = factorVecPhysicalClosure carrier
    }
