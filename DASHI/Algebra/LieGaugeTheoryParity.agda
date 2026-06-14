module DASHI.Algebra.LieGaugeTheoryParity where

open import Agda.Primitive using (Level; Setω; lsuc; _⊔_)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

data ⊥ : Set where

------------------------------------------------------------------------
-- Lie/gauge theory parity surface.
--
-- This module is an algebra-facing fail-closed interface for the PhysLean
-- parity lane.  It records the reusable structures and proof obligations
-- needed for Lie groups/algebras, representations, principal and associated
-- bundles, connections, curvature, Yang-Mills actions, Wilson loops, BRST,
-- and gauge fixing.  It intentionally proves no analytic theorem and promotes
-- no Clay/continuum/PhysLean parity claim without explicit authority fields.

data GaugeTheoryFeature : Set where
  lieGroupFeature :
    GaugeTheoryFeature

  lieAlgebraFeature :
    GaugeTheoryFeature

  representationFeature :
    GaugeTheoryFeature

  principalBundleFeature :
    GaugeTheoryFeature

  associatedBundleFeature :
    GaugeTheoryFeature

  connectionFeature :
    GaugeTheoryFeature

  curvatureFeature :
    GaugeTheoryFeature

  covariantDerivativeFeature :
    GaugeTheoryFeature

  gaugeTransformationFeature :
    GaugeTheoryFeature

  yangMillsActionFeature :
    GaugeTheoryFeature

  wilsonLoopFeature :
    GaugeTheoryFeature

  brstFeature :
    GaugeTheoryFeature

  gaugeFixingFeature :
    GaugeTheoryFeature

  ghostSectorFeature :
    GaugeTheoryFeature

  obstructionInventoryFeature :
    GaugeTheoryFeature

canonicalGaugeTheoryFeatures : List GaugeTheoryFeature
canonicalGaugeTheoryFeatures =
  lieGroupFeature
  ∷ lieAlgebraFeature
  ∷ representationFeature
  ∷ principalBundleFeature
  ∷ associatedBundleFeature
  ∷ connectionFeature
  ∷ curvatureFeature
  ∷ covariantDerivativeFeature
  ∷ gaugeTransformationFeature
  ∷ yangMillsActionFeature
  ∷ wilsonLoopFeature
  ∷ brstFeature
  ∷ gaugeFixingFeature
  ∷ ghostSectorFeature
  ∷ obstructionInventoryFeature
  ∷ []

data ParityStatus : Set where
  interfaceRecorded :
    ParityStatus

  obligationOpen :
    ParityStatus

  authorityBacked :
    ParityStatus

  promoted :
    ParityStatus

data ParityClaim : Set where
  reusableInterfaceClaim :
    ParityClaim

  finiteCarrierClaim :
    ParityClaim

  continuumSmoothBundleClaim :
    ParityClaim

  classicalGaugeTheoryClaim :
    ParityClaim

  quantumYangMillsClaim :
    ParityClaim

  clayMassGapClaim :
    ParityClaim

data ObligationKind : Set where
  algebraicLawObligation :
    ObligationKind

  smoothStructureObligation :
    ObligationKind

  bundleLocalTrivialityObligation :
    ObligationKind

  equivarianceObligation :
    ObligationKind

  connectionNaturalityObligation :
    ObligationKind

  curvatureBianchiObligation :
    ObligationKind

  actionGaugeInvarianceObligation :
    ObligationKind

  wilsonHolonomyObligation :
    ObligationKind

  brstNilpotenceObligation :
    ObligationKind

  gaugeSliceObligation :
    ObligationKind

  analyticWellPosednessObligation :
    ObligationKind

  reflectionPositivityObligation :
    ObligationKind

  continuumLimitObligation :
    ObligationKind

  externalAuthorityObligation :
    ObligationKind

canonicalObligations : List ObligationKind
canonicalObligations =
  algebraicLawObligation
  ∷ smoothStructureObligation
  ∷ bundleLocalTrivialityObligation
  ∷ equivarianceObligation
  ∷ connectionNaturalityObligation
  ∷ curvatureBianchiObligation
  ∷ actionGaugeInvarianceObligation
  ∷ wilsonHolonomyObligation
  ∷ brstNilpotenceObligation
  ∷ gaugeSliceObligation
  ∷ analyticWellPosednessObligation
  ∷ reflectionPositivityObligation
  ∷ continuumLimitObligation
  ∷ externalAuthorityObligation
  ∷ []

record ObligationReceipt : Set where
  constructor mkObligationReceipt
  field
    obligation :
      ObligationKind

    recorded :
      Bool

    discharged :
      Bool

    authorityRequired :
      Bool

    note :
      String

open ObligationReceipt public

mkOpenObligation : ObligationKind → String → ObligationReceipt
mkOpenObligation k s =
  mkObligationReceipt k true false true s

canonicalObligationReceipts : List ObligationReceipt
canonicalObligationReceipts =
  mkOpenObligation algebraicLawObligation
    "Algebraic laws are exposed as record fields; this parity receipt does not synthesize proofs."
  ∷ mkOpenObligation smoothStructureObligation
    "Smooth manifold and differentiability structure remain authority inputs."
  ∷ mkOpenObligation bundleLocalTrivialityObligation
    "Principal and associated bundle local triviality is an explicit interface obligation."
  ∷ mkOpenObligation equivarianceObligation
    "Actions, representations, and associated-bundle quotients require explicit equivariance witnesses."
  ∷ mkOpenObligation connectionNaturalityObligation
    "Connection pullback, gauge covariance, and local form compatibility remain external obligations."
  ∷ mkOpenObligation curvatureBianchiObligation
    "Curvature definition and Bianchi identity are recorded as reusable fields, not derived here."
  ∷ mkOpenObligation actionGaugeInvarianceObligation
    "Yang-Mills action gauge invariance and positivity require supplied proofs."
  ∷ mkOpenObligation wilsonHolonomyObligation
    "Wilson loops and holonomy traces are only named interfaces until holonomy authority is supplied."
  ∷ mkOpenObligation brstNilpotenceObligation
    "BRST nilpotence, ghost grading, and physical cohomology are explicit obligations."
  ∷ mkOpenObligation gaugeSliceObligation
    "Gauge fixing records slice/Faddeev-Popov data without asserting global Gribov resolution."
  ∷ mkOpenObligation analyticWellPosednessObligation
    "Analytic existence, domains, measures, and completions are out of scope for this algebra layer."
  ∷ mkOpenObligation reflectionPositivityObligation
    "Reflection positivity is not inferred from finite algebraic interfaces."
  ∷ mkOpenObligation continuumLimitObligation
    "Continuum promotion requires separate limiting authority."
  ∷ mkOpenObligation externalAuthorityObligation
    "PhysLean parity, Clay relevance, and downstream theorem promotion require external authority."
  ∷ []

------------------------------------------------------------------------
-- Reusable algebraic structures.

record Magma {ℓ : Level} : Set (lsuc ℓ) where
  field
    Carrier :
      Set ℓ

    _∙_ :
      Carrier → Carrier → Carrier

open Magma public

record LieGroupInterface {ℓ : Level} : Set (lsuc ℓ) where
  field
    Carrier :
      Set ℓ

    identity :
      Carrier

    _∙_ :
      Carrier → Carrier → Carrier

    inverse :
      Carrier → Carrier

    leftIdentity :
      ∀ g → identity ∙ g ≡ g

    rightIdentity :
      ∀ g → g ∙ identity ≡ g

    leftInverse :
      ∀ g → inverse g ∙ g ≡ identity

    rightInverse :
      ∀ g → g ∙ inverse g ≡ identity

    associativity :
      ∀ f g h → (f ∙ g) ∙ h ≡ f ∙ (g ∙ h)

    smoothStructureAuthority :
      Bool

    smoothStructureAuthorityIsTrue :
      smoothStructureAuthority ≡ true

open LieGroupInterface public

record LieAlgebraInterface {ℓ : Level} : Set (lsuc ℓ) where
  field
    Carrier :
      Set ℓ

    zero :
      Carrier

    _+_ :
      Carrier → Carrier → Carrier

    -_ :
      Carrier → Carrier

    bracket :
      Carrier → Carrier → Carrier

    bracketAntisymmetry :
      ∀ x y → bracket x y ≡ - (bracket y x)

    bracketJacobi :
      ∀ x y z →
        _+_ (bracket x (bracket y z))
            (_+_ (bracket y (bracket z x))
                 (bracket z (bracket x y)))
        ≡ zero

    vectorSpaceAuthority :
      Bool

    vectorSpaceAuthorityIsTrue :
      vectorSpaceAuthority ≡ true

open LieAlgebraInterface public

record RepresentationInterface
  {ℓG ℓV : Level}
  (G : LieGroupInterface {ℓG}) : Set (lsuc (ℓG ⊔ ℓV)) where
  field
    Vector :
      Set ℓV

    linearMap :
      Set ℓV

    idLinear :
      linearMap

    composeLinear :
      linearMap → linearMap → linearMap

    act :
      Carrier G → linearMap

    preservesIdentity :
      act (identity G) ≡ idLinear

    preservesMultiplication :
      ∀ g h → act (_∙_ G g h) ≡ composeLinear (act g) (act h)

    linearityAuthority :
      Bool

    linearityAuthorityIsTrue :
      linearityAuthority ≡ true

open RepresentationInterface public

record InfinitesimalRepresentationInterface
  {ℓ𝔤 ℓV : Level}
  (𝔤 : LieAlgebraInterface {ℓ𝔤}) : Set (lsuc (ℓ𝔤 ⊔ ℓV)) where
  field
    Vector :
      Set ℓV

    endomorphism :
      Set ℓV

    zeroEndomorphism :
      endomorphism

    commutator :
      endomorphism → endomorphism → endomorphism

    dρ :
      Carrier 𝔤 → endomorphism

    preservesBracket :
      ∀ x y → dρ (bracket 𝔤 x y) ≡ commutator (dρ x) (dρ y)

    linearAuthority :
      Bool

    linearAuthorityIsTrue :
      linearAuthority ≡ true

open InfinitesimalRepresentationInterface public

------------------------------------------------------------------------
-- Bundle, field, and observable interfaces.

record PrincipalBundleInterface
  {ℓB ℓP ℓG : Level}
  (G : LieGroupInterface {ℓG}) : Set (lsuc (ℓB ⊔ ℓP ⊔ ℓG)) where
  field
    Base :
      Set ℓB

    Total :
      Set ℓP

    projection :
      Total → Base

    rightAction :
      Total → Carrier G → Total

    actionPreservesProjection :
      ∀ p g → projection (rightAction p g) ≡ projection p

    rightIdentityAction :
      ∀ p → rightAction p (identity G) ≡ p

    rightCompatibility :
      ∀ p g h →
        rightAction (rightAction p g) h ≡ rightAction p (_∙_ G g h)

    localTrivialityAuthority :
      Bool

    localTrivialityAuthorityIsTrue :
      localTrivialityAuthority ≡ true

open PrincipalBundleInterface public

record AssociatedBundleInterface
  {ℓB ℓP ℓG ℓV : Level}
  (G : LieGroupInterface {ℓG})
  (P : PrincipalBundleInterface {ℓB} {ℓP} G)
  (ρ : RepresentationInterface {ℓG} {ℓV} G) :
  Set (lsuc (ℓB ⊔ ℓP ⊔ ℓG ⊔ ℓV)) where
  field
    AssociatedTotal :
      Set (ℓP ⊔ ℓV)

    associatedProjection :
      AssociatedTotal → Base P

    pair :
      Total P → Vector ρ → AssociatedTotal

    quotientEquivariance :
      ∀ p g v →
        pair (rightAction P p g) v ≡ pair p v

    associatedLocalTrivialityAuthority :
      Bool

    associatedLocalTrivialityAuthorityIsTrue :
      associatedLocalTrivialityAuthority ≡ true

open AssociatedBundleInterface public

record ConnectionInterface
  {ℓB ℓP ℓG ℓ𝔤 : Level}
  (G : LieGroupInterface {ℓG})
  (𝔤 : LieAlgebraInterface {ℓ𝔤})
  (P : PrincipalBundleInterface {ℓB} {ℓP} G) :
  Set (lsuc (ℓB ⊔ ℓP ⊔ ℓG ⊔ ℓ𝔤)) where
  field
    OneForm :
      Set (ℓP ⊔ ℓ𝔤)

    connectionForm :
      OneForm

    horizontalLift :
      Base P → Set (ℓP ⊔ ℓ𝔤)

    equivarianceAuthority :
      Bool

    equivarianceAuthorityIsTrue :
      equivarianceAuthority ≡ true

    reproducesFundamentalFieldsAuthority :
      Bool

    reproducesFundamentalFieldsAuthorityIsTrue :
      reproducesFundamentalFieldsAuthority ≡ true

open ConnectionInterface public

record CurvatureInterface
  {ℓB ℓP ℓG ℓ𝔤 : Level}
  (G : LieGroupInterface {ℓG})
  (𝔤 : LieAlgebraInterface {ℓ𝔤})
  (P : PrincipalBundleInterface {ℓB} {ℓP} G)
  (A : ConnectionInterface G 𝔤 P) :
  Set (lsuc (ℓB ⊔ ℓP ⊔ ℓG ⊔ ℓ𝔤)) where
  field
    TwoForm :
      Set (ℓP ⊔ ℓ𝔤)

    curvature :
      TwoForm

    localExpressionAuthority :
      Bool

    localExpressionAuthorityIsTrue :
      localExpressionAuthority ≡ true

    bianchiIdentityAuthority :
      Bool

    bianchiIdentityAuthorityIsTrue :
      bianchiIdentityAuthority ≡ true

open CurvatureInterface public

record CovariantDerivativeInterface
  {ℓB ℓP ℓG ℓ𝔤 ℓV : Level}
  (G : LieGroupInterface {ℓG})
  (𝔤 : LieAlgebraInterface {ℓ𝔤})
  (P : PrincipalBundleInterface {ℓB} {ℓP} G)
  (ρ : RepresentationInterface {ℓG} {ℓV} G)
  (A : ConnectionInterface G 𝔤 P) :
  Set (lsuc (ℓB ⊔ ℓP ⊔ ℓG ⊔ ℓ𝔤 ⊔ ℓV)) where
  field
    Section :
      Set (ℓB ⊔ ℓV)

    OneFormValuedSection :
      Set (ℓB ⊔ ℓV)

    covariantDerivative :
      Section → OneFormValuedSection

    leibnizAuthority :
      Bool

    leibnizAuthorityIsTrue :
      leibnizAuthority ≡ true

    gaugeCovarianceAuthority :
      Bool

    gaugeCovarianceAuthorityIsTrue :
      gaugeCovarianceAuthority ≡ true

open CovariantDerivativeInterface public

record GaugeTransformationInterface
  {ℓB ℓP ℓG ℓ𝔤 : Level}
  (G : LieGroupInterface {ℓG})
  (𝔤 : LieAlgebraInterface {ℓ𝔤})
  (P : PrincipalBundleInterface {ℓB} {ℓP} G)
  (A : ConnectionInterface G 𝔤 P) :
  Set (lsuc (ℓB ⊔ ℓP ⊔ ℓG ⊔ ℓ𝔤)) where
  field
    GaugeTransformation :
      Set (ℓB ⊔ ℓG)

    transformConnection :
      GaugeTransformation → OneForm A

    preservesCurvatureClassAuthority :
      Bool

    preservesCurvatureClassAuthorityIsTrue :
      preservesCurvatureClassAuthority ≡ true

open GaugeTransformationInterface public

record YangMillsActionInterface
  {ℓB ℓP ℓG ℓ𝔤 : Level}
  (G : LieGroupInterface {ℓG})
  (𝔤 : LieAlgebraInterface {ℓ𝔤})
  (P : PrincipalBundleInterface {ℓB} {ℓP} G) :
  Set (lsuc (ℓB ⊔ ℓP ⊔ ℓG ⊔ ℓ𝔤)) where
  field
    ActionValue :
      Set (ℓB ⊔ ℓ𝔤)

    action :
      (A : ConnectionInterface G 𝔤 P) →
      CurvatureInterface G 𝔤 P A →
      ActionValue

    hodgeAuthority :
      Bool

    hodgeAuthorityIsTrue :
      hodgeAuthority ≡ true

    tracePairingAuthority :
      Bool

    tracePairingAuthorityIsTrue :
      tracePairingAuthority ≡ true

    gaugeInvariantAuthority :
      Bool

    gaugeInvariantAuthorityIsTrue :
      gaugeInvariantAuthority ≡ true

open YangMillsActionInterface public

record WilsonLoopInterface
  {ℓB ℓP ℓG ℓ𝔤 : Level}
  (G : LieGroupInterface {ℓG})
  (𝔤 : LieAlgebraInterface {ℓ𝔤})
  (P : PrincipalBundleInterface {ℓB} {ℓP} G) :
  Set (lsuc (ℓB ⊔ ℓP ⊔ ℓG ⊔ ℓ𝔤)) where
  field
    Loop :
      Set ℓB

    TraceValue :
      Set (ℓB ⊔ ℓG)

    holonomy :
      ConnectionInterface G 𝔤 P → Loop → Carrier G

    trace :
      Carrier G → TraceValue

    wilsonLoop :
      ConnectionInterface G 𝔤 P → Loop → TraceValue

    wilsonLoopDefinitionAuthority :
      Bool

    wilsonLoopDefinitionAuthorityIsTrue :
      wilsonLoopDefinitionAuthority ≡ true

open WilsonLoopInterface public

record BRSTInterface
  {ℓField ℓGhost : Level} : Set (lsuc (ℓField ⊔ ℓGhost)) where
  field
    Field :
      Set ℓField

    Ghost :
      Set ℓGhost

    GradedField :
      Set (ℓField ⊔ ℓGhost)

    brst :
      GradedField → GradedField

    ghostNumber :
      GradedField → Nat

    nilpotentAuthority :
      Bool

    nilpotentAuthorityIsTrue :
      nilpotentAuthority ≡ true

    physicalCohomologyAuthority :
      Bool

    physicalCohomologyAuthorityIsTrue :
      physicalCohomologyAuthority ≡ true

open BRSTInterface public

record GaugeFixingInterface
  {ℓField ℓSlice : Level} : Set (lsuc (ℓField ⊔ ℓSlice)) where
  field
    Field :
      Set ℓField

    Slice :
      Set ℓSlice

    gaugeCondition :
      Field → Bool

    projectToSlice :
      Field → Slice

    localSliceAuthority :
      Bool

    localSliceAuthorityIsTrue :
      localSliceAuthority ≡ true

    faddevPopovAuthority :
      Bool

    faddevPopovAuthorityIsTrue :
      faddevPopovAuthority ≡ true

    globalGribovResolved :
      Bool

    globalGribovResolvedIsFalse :
      globalGribovResolved ≡ false

open GaugeFixingInterface public

------------------------------------------------------------------------
-- Authority and promotion gates.

record LieGaugeAuthorityGate : Set where
  constructor mkLieGaugeAuthorityGate
  field
    lieGroupLawsAuthorized :
      Bool

    lieAlgebraLawsAuthorized :
      Bool

    representationLawsAuthorized :
      Bool

    principalBundleAuthorized :
      Bool

    associatedBundleAuthorized :
      Bool

    connectionAuthorized :
      Bool

    curvatureAuthorized :
      Bool

    yangMillsActionAuthorized :
      Bool

    wilsonLoopAuthorized :
      Bool

    brstAuthorized :
      Bool

    gaugeFixingAuthorized :
      Bool

    analyticAuthority :
      Bool

    continuumAuthority :
      Bool

    physLeanParityAuthority :
      Bool

    clayPromotionAuthority :
      Bool

open LieGaugeAuthorityGate public

canonicalFailClosedAuthorityGate : LieGaugeAuthorityGate
canonicalFailClosedAuthorityGate =
  mkLieGaugeAuthorityGate
    true
    true
    true
    true
    true
    true
    true
    false
    false
    false
    false
    false
    false
    false
    false

data LieGaugePromotion : Set where

lieGaugePromotionImpossibleHere :
  LieGaugePromotion → ⊥
lieGaugePromotionImpossibleHere ()

record PromotionAuthority : Set where
  field
    gate :
      LieGaugeAuthorityGate

    yangMillsActionAuthorizedIsTrue :
      yangMillsActionAuthorized gate ≡ true

    wilsonLoopAuthorizedIsTrue :
      wilsonLoopAuthorized gate ≡ true

    brstAuthorizedIsTrue :
      brstAuthorized gate ≡ true

    gaugeFixingAuthorizedIsTrue :
      gaugeFixingAuthorized gate ≡ true

    analyticAuthorityIsTrue :
      analyticAuthority gate ≡ true

    continuumAuthorityIsTrue :
      continuumAuthority gate ≡ true

    physLeanParityAuthorityIsTrue :
      physLeanParityAuthority gate ≡ true

    clayPromotionAuthorityIsTrue :
      clayPromotionAuthority gate ≡ true

open PromotionAuthority public

record ParityDecision : Set where
  constructor mkParityDecision
  field
    claim :
      ParityClaim

    status :
      ParityStatus

    accepted :
      Bool

    blocked :
      Bool

    authorityMissing :
      Bool

    explanation :
      String

open ParityDecision public

classicalInterfaceDecision : ParityDecision
classicalInterfaceDecision =
  mkParityDecision
    reusableInterfaceClaim
    interfaceRecorded
    true
    false
    false
    "Reusable Lie/gauge interfaces and obligation records are available."

continuumPromotionDecision : ParityDecision
continuumPromotionDecision =
  mkParityDecision
    continuumSmoothBundleClaim
    obligationOpen
    false
    true
    true
    "Continuum smooth-bundle parity is blocked pending smooth, analytic, and external parity authority."

quantumYangMillsDecision : ParityDecision
quantumYangMillsDecision =
  mkParityDecision
    quantumYangMillsClaim
    obligationOpen
    false
    true
    true
    "Quantum Yang-Mills promotion is blocked pending action, Wilson, BRST, gauge-fixing, analytic, and continuum authority."

clayMassGapDecision : ParityDecision
clayMassGapDecision =
  mkParityDecision
    clayMassGapClaim
    obligationOpen
    false
    true
    true
    "Clay mass-gap promotion is false here; this module is only an algebraic parity surface."

canonicalParityDecisions : List ParityDecision
canonicalParityDecisions =
  classicalInterfaceDecision
  ∷ continuumPromotionDecision
  ∷ quantumYangMillsDecision
  ∷ clayMassGapDecision
  ∷ []

------------------------------------------------------------------------
-- Canonical checked receipt.

parityScopeStatement : String
parityScopeStatement =
  "Lie/gauge theory parity surface: records reusable interfaces and open obligations for PhysLean-aligned Lie groups, algebras, representations, bundles, connections, curvature, Yang-Mills action, Wilson loops, BRST, and gauge fixing."

failClosedStatement : String
failClosedStatement =
  "Fail-closed: reusable interfaces are recorded, but continuum, quantum Yang-Mills, PhysLean parity, and Clay promotion remain false without explicit authority."

record LieGaugeTheoryParityReceipt : Setω where
  field
    features :
      List GaugeTheoryFeature

    featuresAreCanonical :
      features ≡ canonicalGaugeTheoryFeatures

    obligations :
      List ObligationKind

    obligationsAreCanonical :
      obligations ≡ canonicalObligations

    obligationReceipts :
      List ObligationReceipt

    obligationReceiptsAreCanonical :
      obligationReceipts ≡ canonicalObligationReceipts

    authorityGate :
      LieGaugeAuthorityGate

    authorityGateIsCanonical :
      authorityGate ≡ canonicalFailClosedAuthorityGate

    decisions :
      List ParityDecision

    decisionsAreCanonical :
      decisions ≡ canonicalParityDecisions

    interfaceSurfaceRecorded :
      Bool

    interfaceSurfaceRecordedIsTrue :
      interfaceSurfaceRecorded ≡ true

    lieGroupInterfaceRecorded :
      Bool

    lieGroupInterfaceRecordedIsTrue :
      lieGroupInterfaceRecorded ≡ true

    lieAlgebraInterfaceRecorded :
      Bool

    lieAlgebraInterfaceRecordedIsTrue :
      lieAlgebraInterfaceRecorded ≡ true

    representationInterfaceRecorded :
      Bool

    representationInterfaceRecordedIsTrue :
      representationInterfaceRecorded ≡ true

    principalBundleInterfaceRecorded :
      Bool

    principalBundleInterfaceRecordedIsTrue :
      principalBundleInterfaceRecorded ≡ true

    associatedBundleInterfaceRecorded :
      Bool

    associatedBundleInterfaceRecordedIsTrue :
      associatedBundleInterfaceRecorded ≡ true

    connectionInterfaceRecorded :
      Bool

    connectionInterfaceRecordedIsTrue :
      connectionInterfaceRecorded ≡ true

    curvatureInterfaceRecorded :
      Bool

    curvatureInterfaceRecordedIsTrue :
      curvatureInterfaceRecorded ≡ true

    yangMillsActionInterfaceRecorded :
      Bool

    yangMillsActionInterfaceRecordedIsTrue :
      yangMillsActionInterfaceRecorded ≡ true

    wilsonLoopInterfaceRecorded :
      Bool

    wilsonLoopInterfaceRecordedIsTrue :
      wilsonLoopInterfaceRecorded ≡ true

    brstInterfaceRecorded :
      Bool

    brstInterfaceRecordedIsTrue :
      brstInterfaceRecorded ≡ true

    gaugeFixingInterfaceRecorded :
      Bool

    gaugeFixingInterfaceRecordedIsTrue :
      gaugeFixingInterfaceRecorded ≡ true

    allObligationsDischarged :
      Bool

    allObligationsDischargedIsFalse :
      allObligationsDischarged ≡ false

    analyticAuthorityAvailable :
      Bool

    analyticAuthorityAvailableIsFalse :
      analyticAuthorityAvailable ≡ false

    continuumAuthorityAvailable :
      Bool

    continuumAuthorityAvailableIsFalse :
      continuumAuthorityAvailable ≡ false

    physLeanParityPromoted :
      Bool

    physLeanParityPromotedIsFalse :
      physLeanParityPromoted ≡ false

    quantumYangMillsPromoted :
      Bool

    quantumYangMillsPromotedIsFalse :
      quantumYangMillsPromoted ≡ false

    clayMassGapPromoted :
      Bool

    clayMassGapPromotedIsFalse :
      clayMassGapPromoted ≡ false

canonicalLieGaugeTheoryParityReceipt : LieGaugeTheoryParityReceipt
canonicalLieGaugeTheoryParityReceipt =
  record
    { features =
        canonicalGaugeTheoryFeatures
    ; featuresAreCanonical =
        refl
    ; obligations =
        canonicalObligations
    ; obligationsAreCanonical =
        refl
    ; obligationReceipts =
        canonicalObligationReceipts
    ; obligationReceiptsAreCanonical =
        refl
    ; authorityGate =
        canonicalFailClosedAuthorityGate
    ; authorityGateIsCanonical =
        refl
    ; decisions =
        canonicalParityDecisions
    ; decisionsAreCanonical =
        refl
    ; interfaceSurfaceRecorded =
        true
    ; interfaceSurfaceRecordedIsTrue =
        refl
    ; lieGroupInterfaceRecorded =
        true
    ; lieGroupInterfaceRecordedIsTrue =
        refl
    ; lieAlgebraInterfaceRecorded =
        true
    ; lieAlgebraInterfaceRecordedIsTrue =
        refl
    ; representationInterfaceRecorded =
        true
    ; representationInterfaceRecordedIsTrue =
        refl
    ; principalBundleInterfaceRecorded =
        true
    ; principalBundleInterfaceRecordedIsTrue =
        refl
    ; associatedBundleInterfaceRecorded =
        true
    ; associatedBundleInterfaceRecordedIsTrue =
        refl
    ; connectionInterfaceRecorded =
        true
    ; connectionInterfaceRecordedIsTrue =
        refl
    ; curvatureInterfaceRecorded =
        true
    ; curvatureInterfaceRecordedIsTrue =
        refl
    ; yangMillsActionInterfaceRecorded =
        true
    ; yangMillsActionInterfaceRecordedIsTrue =
        refl
    ; wilsonLoopInterfaceRecorded =
        true
    ; wilsonLoopInterfaceRecordedIsTrue =
        refl
    ; brstInterfaceRecorded =
        true
    ; brstInterfaceRecordedIsTrue =
        refl
    ; gaugeFixingInterfaceRecorded =
        true
    ; gaugeFixingInterfaceRecordedIsTrue =
        refl
    ; allObligationsDischarged =
        false
    ; allObligationsDischargedIsFalse =
        refl
    ; analyticAuthorityAvailable =
        false
    ; analyticAuthorityAvailableIsFalse =
        refl
    ; continuumAuthorityAvailable =
        false
    ; continuumAuthorityAvailableIsFalse =
        refl
    ; physLeanParityPromoted =
        false
    ; physLeanParityPromotedIsFalse =
        refl
    ; quantumYangMillsPromoted =
        false
    ; quantumYangMillsPromotedIsFalse =
        refl
    ; clayMassGapPromoted =
        false
    ; clayMassGapPromotedIsFalse =
        refl
    }

canonicalReceiptIsFailClosed :
  LieGaugeTheoryParityReceipt.clayMassGapPromoted
    canonicalLieGaugeTheoryParityReceipt
  ≡ false
canonicalReceiptIsFailClosed =
  refl

canonicalPhysLeanParityNotPromoted :
  LieGaugeTheoryParityReceipt.physLeanParityPromoted
    canonicalLieGaugeTheoryParityReceipt
  ≡ false
canonicalPhysLeanParityNotPromoted =
  refl
