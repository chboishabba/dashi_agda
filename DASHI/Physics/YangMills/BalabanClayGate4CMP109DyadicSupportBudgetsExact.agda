module DASHI.Physics.YangMills.BalabanClayGate4CMP109DyadicSupportBudgetsExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
  using
    ( Empty; Dec; yes; no
    ; _∈_; here; there; map; mapMembership
    ; _++_; appendMembershipLeft; appendMembershipRight
    ; cartesian; cartesianMembership
    ; pair; first; second; PositiveBond; Axis4; four
    ; elements; complete; cyclicIndexFinite
    ; periodicTorus4DecidableEquality
    )

import DASHI.Physics.YangMills.BalabanClayT2PeriodicBlockPolymerCarrierExact as Periodic
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bond
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicEndpointBlockPredicateExact as Endpoint
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicQkSupportEnumerationExact as Support
import DASHI.Physics.YangMills.BalabanClayGate4CMP109ProjectedEndpointBlocksExact as Projected
import DASHI.Physics.YangMills.BalabanClayGate4CMP109DyadicProjectionNormalizationExact as Dyadic

------------------------------------------------------------------------
-- Exact physical support envelopes for the four-dimensional dyadic step.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (2) (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- A dyadic four-dimensional site block has 16 sites and four positive bonds
-- per site.  One endpoint block therefore has 64 positive fine bonds, while
-- the union of the two endpoint blocks is covered by a 128-entry row envelope.
-- A coarse site has four outgoing and four incoming positive bonds, giving an
-- eight-entry column envelope.  The latter uses an executable certificate for
-- the repository's periodic successor/predecessor inverse laws; no unproved
-- arithmetic identity is silently promoted.
------------------------------------------------------------------------

emptyEliminate : ∀ {A : Set} → Empty → A
emptyEliminate ()

allAxes : List Axis4
allAxes = elements (cyclicIndexFinite four)

listLength : ∀ {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ values) = suc (listLength values)

allAxesLength : listLength allAxes ≡ Dyadic.fourCount
allAxesLength = refl

fibrePositiveBonds :
  ∀ {coarseN} →
  Periodic.PeriodicBlock coarseN →
  List (PositiveBond (suc (Dyadic.dyadicFineN coarseN)))
fibrePositiveBonds coarse =
  cartesian (Dyadic.dyadicFibre coarse) allAxes

fibrePositiveBondsLength :
  ∀ {coarseN} (coarse : Periodic.PeriodicBlock coarseN) →
  listLength (fibrePositiveBonds coarse) ≡ Dyadic.sixtyFour
fibrePositiveBondsLength coarse = refl

fineBondInFibrePositiveBonds :
  ∀ {coarseN}
    (coarse : Periodic.PeriodicBlock coarseN)
    (fineBond : PositiveBond (suc (Dyadic.dyadicFineN coarseN))) →
  Dyadic.projectDyadicSite (first fineBond) ≡ coarse →
  fineBond ∈ fibrePositiveBonds coarse
fineBondInFibrePositiveBonds coarse (pair fineSite axis) projectionExact =
  cartesianMembership
    (Dyadic.dyadicFibreComplete coarse fineSite projectionExact)
    (complete (cyclicIndexFinite four) axis)

dyadicRowEnvelope :
  ∀ {coarseN} →
  PositiveBond (suc coarseN) →
  List (PositiveBond (suc (Dyadic.dyadicFineN coarseN)))
dyadicRowEnvelope coarseBond =
  fibrePositiveBonds (Projected.sourceEndpoint coarseBond)
  ++ fibrePositiveBonds (Projected.targetEndpoint coarseBond)

dyadicRowEnvelopeLength :
  ∀ {coarseN} (coarseBond : PositiveBond (suc coarseN)) →
  listLength (dyadicRowEnvelope coarseBond) ≡ Dyadic.oneTwentyEight
dyadicRowEnvelopeLength coarseBond = refl

dyadicEndpointGeometry :
  ∀ coarseN →
  Endpoint.PeriodicEndpointBlockLists
    (suc (Dyadic.dyadicFineN coarseN)) (suc coarseN)
dyadicEndpointGeometry coarseN =
  Projected.projectedEndpointBlockLists
    (Dyadic.dyadicCMP109SiteProjection coarseN)

dyadicEndpointSupportInRowEnvelope :
  ∀ {coarseN}
    (coarseBond : PositiveBond (suc coarseN))
    (fineBond : PositiveBond (suc (Dyadic.dyadicFineN coarseN))) →
  Endpoint.EndpointBlockUnionSupport
    (dyadicEndpointGeometry coarseN) coarseBond fineBond →
  fineBond ∈ dyadicRowEnvelope coarseBond
dyadicEndpointSupportInRowEnvelope
    {coarseN} coarseBond fineBond
    (Endpoint.leftWitness sourceMembership) =
  appendMembershipLeft
    (fineBondInFibrePositiveBonds
      (Projected.sourceEndpoint coarseBond)
      fineBond
      (Projected.projectedFineBondBlockSound
        (Dyadic.dyadicCMP109SiteProjection coarseN)
        (Projected.sourceEndpoint coarseBond)
        fineBond
        sourceMembership))
dyadicEndpointSupportInRowEnvelope
    {coarseN} coarseBond fineBond
    (Endpoint.rightWitness targetMembership) =
  appendMembershipRight
    (fineBondInFibrePositiveBonds
      (Projected.targetEndpoint coarseBond)
      fineBond
      (Projected.projectedFineBondBlockSound
        (Dyadic.dyadicCMP109SiteProjection coarseN)
        (Projected.targetEndpoint coarseBond)
        fineBond
        targetMembership))

------------------------------------------------------------------------
-- Executable periodic step-inverse certificate.
------------------------------------------------------------------------

record Both (left right : Set) : Set where
  constructor both
  field
    firstProof : left
    secondProof : right

open Both public

data All {A : Set} (Predicate : A → Set) : List A → Set where
  allNil : All Predicate []
  allCons : ∀ {value values} →
    Predicate value → All Predicate values →
    All Predicate (value ∷ values)

allMember :
  ∀ {A : Set} {Predicate : A → Set}
    {value : A} {values : List A} →
  All Predicate values → value ∈ values → Predicate value
allMember allNil ()
allMember (allCons property rest) here = property
allMember (allCons property rest) (there membership) =
  allMember rest membership

decideAll :
  ∀ {A : Set} {Predicate : A → Set} →
  ((value : A) → Dec (Predicate value)) →
  (values : List A) → Dec (All Predicate values)
decideAll decide [] = yes allNil
decideAll decide (value ∷ values)
  with decide value | decideAll decide values
... | yes property | yes rest = yes (allCons property rest)
... | no refutation | restDecision =
  no λ where
    (allCons property rest) → refutation property
... | yes property | no restRefutation =
  no λ where
    (allCons headProperty rest) → restRefutation rest

StepInverseAt :
  ∀ {n} → PositiveBond (suc n) → Set
StepInverseAt (pair site axis) =
  Both
    (Bond.negativeStep (Bond.positiveStep site axis) axis ≡ site)
    (Bond.positiveStep (Bond.negativeStep site axis) axis ≡ site)

stepInverseAtDecidable :
  ∀ {n} (bond : PositiveBond (suc n)) → Dec (StepInverseAt bond)
stepInverseAtDecidable {n} (pair site axis)
  with periodicTorus4DecidableEquality (suc n)
      (Bond.negativeStep (Bond.positiveStep site axis) axis) site
     | periodicTorus4DecidableEquality (suc n)
      (Bond.positiveStep (Bond.negativeStep site axis) axis) site
... | yes backward | yes forward = yes (both backward forward)
... | no backwardRefutation | forwardDecision =
  no λ where
    (both backward forward) → backwardRefutation backward
... | yes backward | no forwardRefutation =
  no λ where
    (both backwardProof forward) → forwardRefutation forward

PeriodicStepInverseCertificate : Nat → Set
PeriodicStepInverseCertificate n =
  All StepInverseAt
    (elements (Support.positiveBondFinite (suc n)))

checkPeriodicStepInverse :
  ∀ n → Dec (PeriodicStepInverseCertificate n)
checkPeriodicStepInverse n =
  decideAll stepInverseAtDecidable
    (elements (Support.positiveBondFinite (suc n)))

stepInverseCertificateUniversal :
  ∀ {n} → PeriodicStepInverseCertificate n →
  ∀ site axis → StepInverseAt (pair site axis)
stepInverseCertificateUniversal certificate site axis =
  allMember certificate
    (complete (Support.positiveBondFinite _) (pair site axis))

------------------------------------------------------------------------
-- Eight-entry coarse-column envelope.
------------------------------------------------------------------------

outgoingPositiveBonds :
  ∀ {n} → Periodic.PeriodicBlock n →
  List (PositiveBond (suc n))
outgoingPositiveBonds site = map (pair site) allAxes

incomingPositiveBonds :
  ∀ {n} → Periodic.PeriodicBlock n →
  List (PositiveBond (suc n))
incomingPositiveBonds site =
  map (λ axis → pair (Bond.negativeStep site axis) axis) allAxes

incidentPositiveBonds :
  ∀ {n} → Periodic.PeriodicBlock n →
  List (PositiveBond (suc n))
incidentPositiveBonds site =
  outgoingPositiveBonds site ++ incomingPositiveBonds site

incidentPositiveBondsLength :
  ∀ {n} (site : Periodic.PeriodicBlock n) →
  listLength (incidentPositiveBonds site) ≡ Dyadic.eight
incidentPositiveBondsLength site = refl

bondInOutgoingAtSource :
  ∀ {n} (bond : PositiveBond (suc n)) →
  bond ∈ outgoingPositiveBonds (Projected.sourceEndpoint bond)
bondInOutgoingAtSource (pair site axis) =
  mapMembership (pair site) (complete (cyclicIndexFinite four) axis)

bondInIncomingAtTarget :
  ∀ {n} → PeriodicStepInverseCertificate n →
  (bond : PositiveBond (suc n)) →
  bond ∈ incomingPositiveBonds (Projected.targetEndpoint bond)
bondInIncomingAtTarget certificate (pair site axis) =
  subst
    (λ candidate →
      candidate ∈ incomingPositiveBonds (Bond.positiveStep site axis))
    (cong (λ source → pair source axis)
      (firstProof
        (stepInverseCertificateUniversal certificate site axis)))
    (mapMembership
      (λ selectedAxis →
        pair (Bond.negativeStep (Bond.positiveStep site axis) selectedAxis)
          selectedAxis)
      (complete (cyclicIndexFinite four) axis))

dyadicEndpointSupportInColumnEnvelope :
  ∀ {coarseN} →
  PeriodicStepInverseCertificate coarseN →
  (coarseBond : PositiveBond (suc coarseN))
  (fineBond : PositiveBond (suc (Dyadic.dyadicFineN coarseN))) →
  Endpoint.EndpointBlockUnionSupport
    (dyadicEndpointGeometry coarseN) coarseBond fineBond →
  coarseBond ∈ incidentPositiveBonds
    (Dyadic.projectDyadicSite (first fineBond))
dyadicEndpointSupportInColumnEnvelope
    {coarseN} certificate coarseBond fineBond
    (Endpoint.leftWitness sourceMembership) =
  appendMembershipLeft
    (subst
      (λ selectedSite →
        coarseBond ∈ outgoingPositiveBonds selectedSite)
      (sym
        (Projected.projectedFineBondBlockSound
          (Dyadic.dyadicCMP109SiteProjection coarseN)
          (Projected.sourceEndpoint coarseBond)
          fineBond sourceMembership))
      (bondInOutgoingAtSource coarseBond))
dyadicEndpointSupportInColumnEnvelope
    {coarseN} certificate coarseBond fineBond
    (Endpoint.rightWitness targetMembership) =
  appendMembershipRight
    (subst
      (λ selectedSite →
        coarseBond ∈ incomingPositiveBonds selectedSite)
      (sym
        (Projected.projectedFineBondBlockSound
          (Dyadic.dyadicCMP109SiteProjection coarseN)
          (Projected.targetEndpoint coarseBond)
          fineBond targetMembership))
      (bondInIncomingAtTarget certificate coarseBond))

cmp109DyadicRowEnvelopeLevel : ProofLevel
cmp109DyadicRowEnvelopeLevel = machineChecked

cmp109DyadicRowCardinality128Level : ProofLevel
cmp109DyadicRowCardinality128Level = computed

periodicStepInverseCertificateDecisionLevel : ProofLevel
periodicStepInverseCertificateDecisionLevel = computed

periodicStepInverseCertificateUniversalLiftLevel : ProofLevel
periodicStepInverseCertificateUniversalLiftLevel = machineChecked

cmp109DyadicColumnEnvelopeLevel : ProofLevel
cmp109DyadicColumnEnvelopeLevel = machineChecked

cmp109DyadicColumnCardinality8Level : ProofLevel
cmp109DyadicColumnCardinality8Level = computed
