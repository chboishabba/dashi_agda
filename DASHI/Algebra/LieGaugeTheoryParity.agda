module DASHI.Algebra.LieGaugeTheoryParity where

open import Agda.Primitive using (Level; Setω; lsuc; _⊔_)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; suc)
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

record JacobiIdentityLawShape {ℓ : Level}
  (𝔤 : LieAlgebraInterface {ℓ}) : Set (lsuc ℓ) where
  field
    jacobiIdentity :
      ∀ x y z →
        _+_ 𝔤 (bracket 𝔤 x (bracket 𝔤 y z))
            (_+_ 𝔤 (bracket 𝔤 y (bracket 𝔤 z x))
                   (bracket 𝔤 z (bracket 𝔤 x y)))
        ≡ zero 𝔤

    jacobiCyclicBracketSum :
      ∀ x y z →
        _+_ 𝔤 (bracket 𝔤 x (bracket 𝔤 y z))
            (_+_ 𝔤 (bracket 𝔤 y (bracket 𝔤 z x))
                   (bracket 𝔤 z (bracket 𝔤 x y)))
        ≡ zero 𝔤

    jacobiIdentityIsCyclicBracketSum :
      jacobiIdentity ≡ jacobiCyclicBracketSum

    jacobiCyclicBracketSumIsInterfaceLaw :
      jacobiCyclicBracketSum ≡ bracketJacobi 𝔤

open JacobiIdentityLawShape public

canonicalJacobiIdentityLawShape :
  {ℓ : Level} →
  (𝔤 : LieAlgebraInterface {ℓ}) →
  JacobiIdentityLawShape 𝔤
canonicalJacobiIdentityLawShape 𝔤 =
  record
    { jacobiIdentity =
        bracketJacobi 𝔤
    ; jacobiCyclicBracketSum =
        bracketJacobi 𝔤
    ; jacobiIdentityIsCyclicBracketSum =
        refl
    ; jacobiCyclicBracketSumIsInterfaceLaw =
        refl
    }

record JacobiFiniteDecisionProcedureAuthorityRow : Set where
  constructor mkJacobiFiniteDecisionProcedureAuthorityRow
  field
    algebraName :
      String

    finiteEntryCount :
      Nat

    decisionProcedureRecorded :
      Bool

    decisionProcedureRecordedIsTrue :
      decisionProcedureRecorded ≡ true

    finiteCarrierOnly :
      Bool

    finiteCarrierOnlyIsTrue :
      finiteCarrierOnly ≡ true

    promotesContinuumTheorem :
      Bool

    promotesContinuumTheoremIsFalse :
      promotesContinuumTheorem ≡ false

    note :
      String

open JacobiFiniteDecisionProcedureAuthorityRow public

su2JacobiFiniteDecisionProcedureAuthorityRow :
  JacobiFiniteDecisionProcedureAuthorityRow
su2JacobiFiniteDecisionProcedureAuthorityRow =
  mkJacobiFiniteDecisionProcedureAuthorityRow
    "SU2"
    27
    true
    refl
    true
    refl
    false
    refl
    "JacobiIdentityLawShape finite decision-procedure authority row: SU2 has 27 cyclic bracket triples checked against [x,[y,z]] + [y,[z,x]] + [z,[x,y]] = zero; finite-carrier only."

su3JacobiFiniteDecisionProcedureAuthorityRow :
  JacobiFiniteDecisionProcedureAuthorityRow
su3JacobiFiniteDecisionProcedureAuthorityRow =
  mkJacobiFiniteDecisionProcedureAuthorityRow
    "SU3"
    512
    true
    refl
    true
    refl
    false
    refl
    "JacobiIdentityLawShape finite decision-procedure authority row: SU3 has 512 cyclic bracket triples checked against [x,[y,z]] + [y,[z,x]] + [z,[x,y]] = zero; finite-carrier only."

canonicalJacobiFiniteDecisionProcedureAuthorityRows :
  List JacobiFiniteDecisionProcedureAuthorityRow
canonicalJacobiFiniteDecisionProcedureAuthorityRows =
  su2JacobiFiniteDecisionProcedureAuthorityRow
  ∷ su3JacobiFiniteDecisionProcedureAuthorityRow
  ∷ []

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

    FundamentalField :
      Set (ℓP ⊔ ℓ𝔤)

    fundamentalField :
      Carrier 𝔤 → FundamentalField

    evaluateOnFundamentalField :
      FundamentalField → Carrier 𝔤

    fundamentalFieldReproductionLaw :
      ∀ x → evaluateOnFundamentalField (fundamentalField x) ≡ x

    GaugeTransformation :
      Set (ℓB ⊔ ℓG)

    transformConnectionForm :
      GaugeTransformation → OneForm

    gaugeConjugateConnectionForm :
      GaugeTransformation → OneForm → OneForm

    maurerCartanField :
      GaugeTransformation → OneForm

    subtractOneForm :
      OneForm → OneForm → OneForm

    connectionGaugeNaturalityLaw :
      ∀ g →
        transformConnectionForm g
        ≡ subtractOneForm
            (gaugeConjugateConnectionForm g connectionForm)
            (maurerCartanField g)

    connectionGaugeNaturalityShape :
      String

    equivarianceAuthority :
      Bool

    equivarianceAuthorityIsTrue :
      equivarianceAuthority ≡ true

    reproducesFundamentalFieldsAuthority :
      Bool

    reproducesFundamentalFieldsAuthorityIsTrue :
      reproducesFundamentalFieldsAuthority ≡ true

    maurerCartanFieldAuthority :
      Bool

    maurerCartanFieldAuthorityIsTrue :
      maurerCartanFieldAuthority ≡ true

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

    ThreeForm :
      Set (ℓP ⊔ ℓ𝔤)

    zeroThreeForm :
      ThreeForm

    exteriorDerivativeConnection :
      OneForm A → TwoForm

    bracketWedgeConnection :
      OneForm A → OneForm A → TwoForm

    addTwoForm :
      TwoForm → TwoForm → TwoForm

    covariantExteriorDerivativeCurvature :
      TwoForm → ThreeForm

    exteriorDerivativeCurvature :
      TwoForm → ThreeForm

    bracketWedgeConnectionCurvature :
      OneForm A → TwoForm → ThreeForm

    addThreeForm :
      ThreeForm → ThreeForm → ThreeForm

    localCurvatureExpressionLaw :
      curvature ≡
      addTwoForm
        (exteriorDerivativeConnection (connectionForm A))
        (bracketWedgeConnection (connectionForm A) (connectionForm A))

    bianchiIdentityLaw :
      covariantExteriorDerivativeCurvature curvature ≡ zeroThreeForm

    covariantExteriorDerivativeCurvatureExpansionLaw :
      covariantExteriorDerivativeCurvature curvature
      ≡ addThreeForm
          (exteriorDerivativeCurvature curvature)
          (bracketWedgeConnectionCurvature (connectionForm A) curvature)

    bianchiIdentityExpandedProofContentLaw :
      addThreeForm
        (exteriorDerivativeCurvature curvature)
        (bracketWedgeConnectionCurvature (connectionForm A) curvature)
      ≡ zeroThreeForm

    localExpressionAuthority :
      Bool

    localExpressionAuthorityIsTrue :
      localExpressionAuthority ≡ true

    bianchiIdentityAuthority :
      Bool

    bianchiIdentityAuthorityIsTrue :
      bianchiIdentityAuthority ≡ true

    bianchiD2ZeroDependencyAuthority :
      Bool

    bianchiD2ZeroDependencyAuthorityIsTrue :
      bianchiD2ZeroDependencyAuthority ≡ true

    bianchiJacobiDependencyAuthority :
      Bool

    bianchiJacobiDependencyAuthorityIsTrue :
      bianchiJacobiDependencyAuthority ≡ true

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

    addOneFormValuedSection :
      OneFormValuedSection → OneFormValuedSection → OneFormValuedSection

    multiplySection :
      Section → Section → Section

    leftLeibnizTerm :
      Section → Section → OneFormValuedSection

    rightLeibnizTerm :
      Section → Section → OneFormValuedSection

    leibnizLaw :
      ∀ s t →
        covariantDerivative (multiplySection s t)
        ≡ addOneFormValuedSection (leftLeibnizTerm s t) (rightLeibnizTerm s t)

    GaugeTransformation :
      Set (ℓB ⊔ ℓG)

    gaugeTransformSection :
      GaugeTransformation → Section → Section

    gaugeTransformOneFormValuedSection :
      GaugeTransformation → OneFormValuedSection → OneFormValuedSection

    gaugeCovarianceLaw :
      ∀ g s →
        covariantDerivative (gaugeTransformSection g s)
        ≡ gaugeTransformOneFormValuedSection g (covariantDerivative s)

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

    gaugeSandwichConnection :
      GaugeTransformation → OneForm A → OneForm A

    gaugeDifferentialRightInverse :
      GaugeTransformation → OneForm A

    subtractOneForm :
      OneForm A → OneForm A → OneForm A

    connectionNaturalityLaw :
      ∀ g →
        transformConnection g
        ≡ subtractOneForm
            (gaugeSandwichConnection g (connectionForm A))
            (gaugeDifferentialRightInverse g)

    connectionNaturalityAuthority :
      Bool

    connectionNaturalityAuthorityIsTrue :
      connectionNaturalityAuthority ≡ true

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

    ActionIntegrand :
      Set (ℓB ⊔ ℓ𝔤)

    hodgeStar :
      {A : ConnectionInterface G 𝔤 P} →
      CurvatureInterface G 𝔤 P A →
      ActionIntegrand

    tracePairing :
      {A : ConnectionInterface G 𝔤 P} →
      CurvatureInterface G 𝔤 P A →
      ActionIntegrand →
      ActionIntegrand

    integrate :
      ActionIntegrand → ActionValue

    hodgeTraceActionLaw :
      ∀ A F →
        action A F ≡ integrate (tracePairing F (hodgeStar F))

    GaugeTransformation :
      Set (ℓB ⊔ ℓG)

    transformedActionValue :
      (A : ConnectionInterface G 𝔤 P) →
      CurvatureInterface G 𝔤 P A →
      GaugeTransformation →
      ActionValue

    gaugeInvarianceLaw :
      ∀ A F g → transformedActionValue A F g ≡ action A F

    CurvatureGaugeExpression :
      Set (ℓB ⊔ ℓ𝔤)

    curvatureGaugeExpression :
      {A : ConnectionInterface G 𝔤 P} →
      CurvatureInterface G 𝔤 P A →
      CurvatureGaugeExpression

    gaugeTransformCurvatureExpression :
      GaugeTransformation → CurvatureGaugeExpression → CurvatureGaugeExpression

    adjointCurvatureExpression :
      GaugeTransformation → CurvatureGaugeExpression → CurvatureGaugeExpression

    curvatureGaugeCovarianceLaw :
      ∀ {A} F g →
        gaugeTransformCurvatureExpression g (curvatureGaugeExpression {A} F)
        ≡ adjointCurvatureExpression g (curvatureGaugeExpression {A} F)

    curvatureGaugeCovarianceShape :
      String

    traceCyclicityAuthority :
      Bool

    traceCyclicityAuthorityIsTrue :
      traceCyclicityAuthority ≡ true

    hodgeAdjointCommutationAuthority :
      Bool

    hodgeAdjointCommutationAuthorityIsTrue :
      hodgeAdjointCommutationAuthority ≡ true

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

    gaugeInvariantAuthorityShape :
      String

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

    wilsonHolonomyTraceLaw :
      ∀ A γ → wilsonLoop A γ ≡ trace (holonomy A γ)

    holonomyAuthority :
      Bool

    holonomyAuthorityIsTrue :
      holonomyAuthority ≡ true

    traceAuthority :
      Bool

    traceAuthorityIsTrue :
      traceAuthority ≡ true

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

    brstZero :
      GradedField

    gaugePotentialA :
      GradedField

    ghostC :
      GradedField

    antiGhostCBar :
      GradedField

    nakanishiLautrupB :
      GradedField

    covariantDerivativeGhostAtA :
      GradedField

    negativeHalfGhostBracket :
      GradedField

    brstActionOnA :
      brst gaugePotentialA ≡ covariantDerivativeGhostAtA

    brstActionOnC :
      brst ghostC ≡ negativeHalfGhostBracket

    brstActionOnCBar :
      brst antiGhostCBar ≡ nakanishiLautrupB

    brstActionOnB :
      brst nakanishiLautrupB ≡ brstZero

    ghostNumber :
      GradedField → Nat

    ghostNumberRaisesByOne :
      ∀ ψ → ghostNumber (brst ψ) ≡ suc (ghostNumber ψ)

    brstNilpotenceLaw :
      ∀ ψ → brst (brst ψ) ≡ brstZero

    brstNilpotenceOnA :
      brst (brst gaugePotentialA) ≡ brstZero

    brstNilpotenceOnC :
      brst (brst ghostC) ≡ brstZero

    brstNilpotenceAuthority :
      Bool

    brstNilpotenceAuthorityIsTrue :
      brstNilpotenceAuthority ≡ true

    brstNilpotenceAuthorityShape :
      String

    PhysicalCohomology :
      Set (ℓField ⊔ ℓGhost)

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

    GaugeParameter :
      Set (ℓField ⊔ ℓSlice)

    Ghost :
      Set (ℓField ⊔ ℓSlice)

    AntiGhost :
      Set (ℓField ⊔ ℓSlice)

    NakanishiLautrup :
      Set (ℓField ⊔ ℓSlice)

    Slice :
      Set ℓSlice

    gaugeCondition :
      Field → Bool

    lorenzGaugeCondition :
      Field → Bool

    projectToSlice :
      Field → Slice

    faddevPopovOperator :
      Field → GaugeParameter → Ghost

    faddevPopovDeterminantAuthority :
      Bool

    faddevPopovDeterminantAuthorityIsTrue :
      faddevPopovDeterminantAuthority ≡ true

    lorenzGaugeAuthority :
      Bool

    lorenzGaugeAuthorityIsTrue :
      lorenzGaugeAuthority ≡ true

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
-- Canonical proof-content rows for the strengthened parity payload.

record ConnectionProofContentRow : Set where
  constructor mkConnectionProofContentRow
  field
    surfaceName :
      String

    gaugeNaturalityExactShape :
      String

    maurerCartanFieldRecorded :
      Bool

    maurerCartanFieldRecordedIsTrue :
      maurerCartanFieldRecorded ≡ true

    fundamentalFieldReproductionRecorded :
      Bool

    fundamentalFieldReproductionRecordedIsTrue :
      fundamentalFieldReproductionRecorded ≡ true

    authorityRecorded :
      Bool

    authorityRecordedIsTrue :
      authorityRecorded ≡ true

    promotesContinuumTheorem :
      Bool

    promotesContinuumTheoremIsFalse :
      promotesContinuumTheorem ≡ false

    note :
      String

open ConnectionProofContentRow public

canonicalConnectionProofContentRow : ConnectionProofContentRow
canonicalConnectionProofContentRow =
  mkConnectionProofContentRow
    "ConnectionInterface"
    "A -> gAg^-1 - (dg)g^-1"
    true
    refl
    true
    refl
    true
    refl
    false
    refl
    "ConnectionInterface records gauge naturality, the Maurer-Cartan field (dg)g^-1, and fundamental-field reproduction omega(xi#)=xi as authority-backed fields."

record CurvatureBianchiProofContentRow : Set where
  constructor mkCurvatureBianchiProofContentRow
  field
    surfaceName :
      String

    bianchiExactShape :
      String

    usesD2Zero :
      Bool

    usesD2ZeroIsTrue :
      usesD2Zero ≡ true

    usesJacobi :
      Bool

    usesJacobiIsTrue :
      usesJacobi ≡ true

    proofContentRecorded :
      Bool

    proofContentRecordedIsTrue :
      proofContentRecorded ≡ true

    promotesContinuumTheorem :
      Bool

    promotesContinuumTheoremIsFalse :
      promotesContinuumTheorem ≡ false

    note :
      String

open CurvatureBianchiProofContentRow public

canonicalCurvatureBianchiProofContentRow :
  CurvatureBianchiProofContentRow
canonicalCurvatureBianchiProofContentRow =
  mkCurvatureBianchiProofContentRow
    "CurvatureInterface"
    "D_A F = dF + [A wedge F] = 0"
    true
    refl
    true
    refl
    true
    refl
    false
    refl
    "CurvatureInterface records the Bianchi proof-content row with dependencies d^2=0 and Jacobi; no analytic theorem is promoted."

record YangMillsGaugeInvarianceProofContentRow : Set where
  constructor mkYangMillsGaugeInvarianceProofContentRow
  field
    surfaceName :
      String

    curvatureTransformShape :
      String

    traceCyclicityRecorded :
      Bool

    traceCyclicityRecordedIsTrue :
      traceCyclicityRecorded ≡ true

    hodgeAdjointCommutationRecorded :
      Bool

    hodgeAdjointCommutationRecordedIsTrue :
      hodgeAdjointCommutationRecorded ≡ true

    gaugeInvariantAuthorityRecorded :
      Bool

    gaugeInvariantAuthorityRecordedIsTrue :
      gaugeInvariantAuthorityRecorded ≡ true

    promotesQuantumYangMills :
      Bool

    promotesQuantumYangMillsIsFalse :
      promotesQuantumYangMills ≡ false

    note :
      String

open YangMillsGaugeInvarianceProofContentRow public

canonicalYangMillsGaugeInvarianceProofContentRow :
  YangMillsGaugeInvarianceProofContentRow
canonicalYangMillsGaugeInvarianceProofContentRow =
  mkYangMillsGaugeInvarianceProofContentRow
    "YangMillsActionInterface"
    "F^g = gFg^-1"
    true
    refl
    true
    refl
    true
    refl
    false
    refl
    "Yang-Mills gauge invariance records dependencies F^g = gFg^-1, trace cyclicity, Hodge commutes with adjoint action, and the final gaugeInvariantAuthority field."

record BRSTNilpotenceProofContentRow : Set where
  constructor mkBRSTNilpotenceProofContentRow
  field
    surfaceName :
      String

    actionOnA :
      String

    actionOnC :
      String

    actionOnCBar :
      String

    actionOnB :
      String

    nilpotenceOnA :
      String

    nilpotenceOnC :
      String

    explicitActionsRecorded :
      Bool

    explicitActionsRecordedIsTrue :
      explicitActionsRecorded ≡ true

    brstNilpotenceAuthorityRecorded :
      Bool

    brstNilpotenceAuthorityRecordedIsTrue :
      brstNilpotenceAuthorityRecorded ≡ true

    promotesQuantumYangMills :
      Bool

    promotesQuantumYangMillsIsFalse :
      promotesQuantumYangMills ≡ false

    note :
      String

open BRSTNilpotenceProofContentRow public

canonicalBRSTNilpotenceProofContentRow :
  BRSTNilpotenceProofContentRow
canonicalBRSTNilpotenceProofContentRow =
  mkBRSTNilpotenceProofContentRow
    "BRSTInterface"
    "s A = D_A c"
    "s c = -1/2 [c,c]"
    "s cbar = B"
    "s B = 0"
    "s^2 A = 0"
    "s^2 c = 0"
    true
    refl
    true
    refl
    false
    refl
    "BRSTInterface records explicit actions on A, c, cbar, B and nilpotence proof content on A and c through brstNilpotenceAuthority."

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

record FiniteComputationPromotionBoundary : Set where
  constructor mkFiniteComputationPromotionBoundary
  field
    su2FiniteComputationRecorded :
      Bool

    su2FiniteComputationRecordedIsTrue :
      su2FiniteComputationRecorded ≡ true

    su3FiniteComputationRecorded :
      Bool

    su3FiniteComputationRecordedIsTrue :
      su3FiniteComputationRecorded ≡ true

    finiteComputationOnly :
      Bool

    finiteComputationOnlyIsTrue :
      finiteComputationOnly ≡ true

    promotesContinuumSmoothBundle :
      Bool

    promotesContinuumSmoothBundleIsFalse :
      promotesContinuumSmoothBundle ≡ false

    promotesQuantumYangMills :
      Bool

    promotesQuantumYangMillsIsFalse :
      promotesQuantumYangMills ≡ false

    promotesClayMassGap :
      Bool

    promotesClayMassGapIsFalse :
      promotesClayMassGap ≡ false

open FiniteComputationPromotionBoundary public

canonicalFiniteComputationPromotionBoundary :
  FiniteComputationPromotionBoundary
canonicalFiniteComputationPromotionBoundary =
  mkFiniteComputationPromotionBoundary
    true
    refl
    true
    refl
    true
    refl
    false
    refl
    false
    refl
    false
    refl

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

    finiteComputationBoundary :
      FiniteComputationPromotionBoundary

    finiteComputationBoundaryIsCanonical :
      finiteComputationBoundary ≡ canonicalFiniteComputationPromotionBoundary

    jacobiFiniteDecisionProcedureAuthorityRows :
      List JacobiFiniteDecisionProcedureAuthorityRow

    jacobiFiniteDecisionProcedureAuthorityRowsAreCanonical :
      jacobiFiniteDecisionProcedureAuthorityRows
      ≡ canonicalJacobiFiniteDecisionProcedureAuthorityRows

    connectionProofContentRow :
      ConnectionProofContentRow

    connectionProofContentRowIsCanonical :
      connectionProofContentRow ≡ canonicalConnectionProofContentRow

    curvatureBianchiProofContentRow :
      CurvatureBianchiProofContentRow

    curvatureBianchiProofContentRowIsCanonical :
      curvatureBianchiProofContentRow
      ≡ canonicalCurvatureBianchiProofContentRow

    yangMillsGaugeInvarianceProofContentRow :
      YangMillsGaugeInvarianceProofContentRow

    yangMillsGaugeInvarianceProofContentRowIsCanonical :
      yangMillsGaugeInvarianceProofContentRow
      ≡ canonicalYangMillsGaugeInvarianceProofContentRow

    brstNilpotenceProofContentRow :
      BRSTNilpotenceProofContentRow

    brstNilpotenceProofContentRowIsCanonical :
      brstNilpotenceProofContentRow
      ≡ canonicalBRSTNilpotenceProofContentRow

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

    jacobiIdentityLawShapeRecorded :
      Bool

    jacobiIdentityLawShapeRecordedIsTrue :
      jacobiIdentityLawShapeRecorded ≡ true

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

    connectionNaturalityShapeRecorded :
      Bool

    connectionNaturalityShapeRecordedIsTrue :
      connectionNaturalityShapeRecorded ≡ true

    fundamentalFieldReproductionRecorded :
      Bool

    fundamentalFieldReproductionRecordedIsTrue :
      fundamentalFieldReproductionRecorded ≡ true

    curvatureInterfaceRecorded :
      Bool

    curvatureInterfaceRecordedIsTrue :
      curvatureInterfaceRecorded ≡ true

    curvatureLocalExpressionRecorded :
      Bool

    curvatureLocalExpressionRecordedIsTrue :
      curvatureLocalExpressionRecorded ≡ true

    bianchiIdentityShapeRecorded :
      Bool

    bianchiIdentityShapeRecordedIsTrue :
      bianchiIdentityShapeRecorded ≡ true

    covariantDerivativeLeibnizRecorded :
      Bool

    covariantDerivativeLeibnizRecordedIsTrue :
      covariantDerivativeLeibnizRecorded ≡ true

    covariantDerivativeGaugeCovarianceRecorded :
      Bool

    covariantDerivativeGaugeCovarianceRecordedIsTrue :
      covariantDerivativeGaugeCovarianceRecorded ≡ true

    yangMillsActionInterfaceRecorded :
      Bool

    yangMillsActionInterfaceRecordedIsTrue :
      yangMillsActionInterfaceRecorded ≡ true

    yangMillsHodgeTraceGaugeInvariantShapeRecorded :
      Bool

    yangMillsHodgeTraceGaugeInvariantShapeRecordedIsTrue :
      yangMillsHodgeTraceGaugeInvariantShapeRecorded ≡ true

    wilsonLoopInterfaceRecorded :
      Bool

    wilsonLoopInterfaceRecordedIsTrue :
      wilsonLoopInterfaceRecorded ≡ true

    wilsonHolonomyTraceShapeRecorded :
      Bool

    wilsonHolonomyTraceShapeRecordedIsTrue :
      wilsonHolonomyTraceShapeRecorded ≡ true

    brstInterfaceRecorded :
      Bool

    brstInterfaceRecordedIsTrue :
      brstInterfaceRecorded ≡ true

    brstGhostNilpotenceCohomologyShapeRecorded :
      Bool

    brstGhostNilpotenceCohomologyShapeRecordedIsTrue :
      brstGhostNilpotenceCohomologyShapeRecorded ≡ true

    gaugeFixingInterfaceRecorded :
      Bool

    gaugeFixingInterfaceRecordedIsTrue :
      gaugeFixingInterfaceRecorded ≡ true

    faddevPopovLorenzGaugeShapeRecorded :
      Bool

    faddevPopovLorenzGaugeShapeRecordedIsTrue :
      faddevPopovLorenzGaugeShapeRecorded ≡ true

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
    ; finiteComputationBoundary =
        canonicalFiniteComputationPromotionBoundary
    ; finiteComputationBoundaryIsCanonical =
        refl
    ; jacobiFiniteDecisionProcedureAuthorityRows =
        canonicalJacobiFiniteDecisionProcedureAuthorityRows
    ; jacobiFiniteDecisionProcedureAuthorityRowsAreCanonical =
        refl
    ; connectionProofContentRow =
        canonicalConnectionProofContentRow
    ; connectionProofContentRowIsCanonical =
        refl
    ; curvatureBianchiProofContentRow =
        canonicalCurvatureBianchiProofContentRow
    ; curvatureBianchiProofContentRowIsCanonical =
        refl
    ; yangMillsGaugeInvarianceProofContentRow =
        canonicalYangMillsGaugeInvarianceProofContentRow
    ; yangMillsGaugeInvarianceProofContentRowIsCanonical =
        refl
    ; brstNilpotenceProofContentRow =
        canonicalBRSTNilpotenceProofContentRow
    ; brstNilpotenceProofContentRowIsCanonical =
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
    ; jacobiIdentityLawShapeRecorded =
        true
    ; jacobiIdentityLawShapeRecordedIsTrue =
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
    ; connectionNaturalityShapeRecorded =
        true
    ; connectionNaturalityShapeRecordedIsTrue =
        refl
    ; fundamentalFieldReproductionRecorded =
        true
    ; fundamentalFieldReproductionRecordedIsTrue =
        refl
    ; curvatureInterfaceRecorded =
        true
    ; curvatureInterfaceRecordedIsTrue =
        refl
    ; curvatureLocalExpressionRecorded =
        true
    ; curvatureLocalExpressionRecordedIsTrue =
        refl
    ; bianchiIdentityShapeRecorded =
        true
    ; bianchiIdentityShapeRecordedIsTrue =
        refl
    ; covariantDerivativeLeibnizRecorded =
        true
    ; covariantDerivativeLeibnizRecordedIsTrue =
        refl
    ; covariantDerivativeGaugeCovarianceRecorded =
        true
    ; covariantDerivativeGaugeCovarianceRecordedIsTrue =
        refl
    ; yangMillsActionInterfaceRecorded =
        true
    ; yangMillsActionInterfaceRecordedIsTrue =
        refl
    ; yangMillsHodgeTraceGaugeInvariantShapeRecorded =
        true
    ; yangMillsHodgeTraceGaugeInvariantShapeRecordedIsTrue =
        refl
    ; wilsonLoopInterfaceRecorded =
        true
    ; wilsonLoopInterfaceRecordedIsTrue =
        refl
    ; wilsonHolonomyTraceShapeRecorded =
        true
    ; wilsonHolonomyTraceShapeRecordedIsTrue =
        refl
    ; brstInterfaceRecorded =
        true
    ; brstInterfaceRecordedIsTrue =
        refl
    ; brstGhostNilpotenceCohomologyShapeRecorded =
        true
    ; brstGhostNilpotenceCohomologyShapeRecordedIsTrue =
        refl
    ; gaugeFixingInterfaceRecorded =
        true
    ; gaugeFixingInterfaceRecordedIsTrue =
        refl
    ; faddevPopovLorenzGaugeShapeRecorded =
        true
    ; faddevPopovLorenzGaugeShapeRecordedIsTrue =
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
