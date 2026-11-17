module DASHI.Core.AxisBundlePrimeFibreReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)

------------------------------------------------------------------------
-- Axis bundle / prime-fibre receipt.
--
-- Candidate-only transcript rule:
--   - intersectional axes are represented as prime-fibre / product-fibre
--     addresses;
--   - a product fibre is not reducible to a single axis;
--   - p-adic / shared-root closeness is candidate structural affinity, not
--     identity and not causal proof;
--   - no social, legal, or clinical authority is promoted.

listCount : ∀ {A : Set} → List A → Nat
listCount [] =
  zero
listCount (_ ∷ xs) =
  suc (listCount xs)

------------------------------------------------------------------------
-- Routes.

data PrimeFibreRoute : Set where
  candidateOnlyRoute :
    PrimeFibreRoute

  singleAxisProjectionRoute :
    PrimeFibreRoute

  identityCollapseRoute :
    PrimeFibreRoute

  causalProofRoute :
    PrimeFibreRoute

  socialAuthorityRoute :
    PrimeFibreRoute

  legalAuthorityRoute :
    PrimeFibreRoute

  clinicalAuthorityRoute :
    PrimeFibreRoute

data Never : Set where

AdmissiblePrimeFibreRoute :
  PrimeFibreRoute →
  Set
AdmissiblePrimeFibreRoute candidateOnlyRoute = ⊤
AdmissiblePrimeFibreRoute singleAxisProjectionRoute = Never
AdmissiblePrimeFibreRoute identityCollapseRoute = Never
AdmissiblePrimeFibreRoute causalProofRoute = Never
AdmissiblePrimeFibreRoute socialAuthorityRoute = Never
AdmissiblePrimeFibreRoute legalAuthorityRoute = Never
AdmissiblePrimeFibreRoute clinicalAuthorityRoute = Never

singleAxisProjectionRouteRejected :
  AdmissiblePrimeFibreRoute singleAxisProjectionRoute →
  Never
singleAxisProjectionRouteRejected impossible = impossible

identityCollapseRouteRejected :
  AdmissiblePrimeFibreRoute identityCollapseRoute →
  Never
identityCollapseRouteRejected impossible = impossible

causalProofRouteRejected :
  AdmissiblePrimeFibreRoute causalProofRoute →
  Never
causalProofRouteRejected impossible = impossible

socialAuthorityRouteRejected :
  AdmissiblePrimeFibreRoute socialAuthorityRoute →
  Never
socialAuthorityRouteRejected impossible = impossible

legalAuthorityRouteRejected :
  AdmissiblePrimeFibreRoute legalAuthorityRoute →
  Never
legalAuthorityRouteRejected impossible = impossible

clinicalAuthorityRouteRejected :
  AdmissiblePrimeFibreRoute clinicalAuthorityRoute →
  Never
clinicalAuthorityRouteRejected impossible = impossible

data RouteGate : Set where
  candidateOnlyGate :
    RouteGate

  singleAxisProjectionBlockedGate :
    RouteGate

  identityCollapseBlockedGate :
    RouteGate

  causalProofBlockedGate :
    RouteGate

  socialAuthorityBlockedGate :
    RouteGate

  legalAuthorityBlockedGate :
    RouteGate

  clinicalAuthorityBlockedGate :
    RouteGate

canonicalRouteGates : List RouteGate
canonicalRouteGates =
  candidateOnlyGate
  ∷ singleAxisProjectionBlockedGate
  ∷ identityCollapseBlockedGate
  ∷ causalProofBlockedGate
  ∷ socialAuthorityBlockedGate
  ∷ legalAuthorityBlockedGate
  ∷ clinicalAuthorityBlockedGate
  ∷ []

------------------------------------------------------------------------
-- Axis and prime data.

data IntersectionalAxis : Set where
  raceAxis :
    IntersectionalAxis

  classAxis :
    IntersectionalAxis

  genderAxis :
    IntersectionalAxis

  sexualityAxis :
    IntersectionalAxis

  disabilityAxis :
    IntersectionalAxis

  neurotypeAxis :
    IntersectionalAxis

  religionAxis :
    IntersectionalAxis

  colonialityAxis :
    IntersectionalAxis

  lawAxis :
    IntersectionalAxis

  landAxis :
    IntersectionalAxis

  familyAxis :
    IntersectionalAxis

  institutionAxis :
    IntersectionalAxis

canonicalIntersectionalAxes : List IntersectionalAxis
canonicalIntersectionalAxes =
  raceAxis
  ∷ classAxis
  ∷ genderAxis
  ∷ sexualityAxis
  ∷ disabilityAxis
  ∷ neurotypeAxis
  ∷ religionAxis
  ∷ colonialityAxis
  ∷ lawAxis
  ∷ landAxis
  ∷ familyAxis
  ∷ institutionAxis
  ∷ []

data PrimeKind : Set where
  prime2 :
    PrimeKind

  prime3 :
    PrimeKind

  prime5 :
    PrimeKind

  prime7 :
    PrimeKind

  prime11 :
    PrimeKind

  prime13 :
    PrimeKind

  prime17 :
    PrimeKind

  prime19 :
    PrimeKind

canonicalPrimeKinds : List PrimeKind
canonicalPrimeKinds =
  prime2
  ∷ prime3
  ∷ prime5
  ∷ prime7
  ∷ prime11
  ∷ prime13
  ∷ prime17
  ∷ prime19
  ∷ []

data FibreKind : Set where
  primeFibreKind :
    FibreKind

  productFibreKind :
    FibreKind

  sharedRootClosenessKind :
    FibreKind

  singleAxisProjectionKind :
    FibreKind

  causalProofKind :
    FibreKind

  authorityProjectionKind :
    FibreKind

canonicalFibreKinds : List FibreKind
canonicalFibreKinds =
  primeFibreKind
  ∷ productFibreKind
  ∷ sharedRootClosenessKind
  ∷ singleAxisProjectionKind
  ∷ causalProofKind
  ∷ authorityProjectionKind
  ∷ []

data AddressKind : Set where
  axisAddressKind :
    AddressKind

  primeFibreAddressKind :
    AddressKind

  productFibreAddressKind :
    AddressKind

  sharedRootAddressKind :
    AddressKind

canonicalAddressKinds : List AddressKind
canonicalAddressKinds =
  axisAddressKind
  ∷ primeFibreAddressKind
  ∷ productFibreAddressKind
  ∷ sharedRootAddressKind
  ∷ []

------------------------------------------------------------------------
-- Product rows.

record AxisPrimeProductRow : Set where
  constructor mkAxisPrimeProductRow
  field
    rowIndex :
      Nat

    rowAxis :
      IntersectionalAxis

    rowPrime :
      PrimeKind

    rowFibreKind :
      FibreKind

    rowAddressKind :
      AddressKind

    rowLabel :
      String

    rowStatement :
      String

    rowCandidateOnly :
      Bool

    rowCandidateOnlyIsTrue :
      rowCandidateOnly ≡ true

    rowProductNotSingleAxis :
      Bool

    rowProductNotSingleAxisIsTrue :
      rowProductNotSingleAxis ≡ true

    rowSharedRootClosenessIsCandidate :
      Bool

    rowSharedRootClosenessIsCandidateIsTrue :
      rowSharedRootClosenessIsCandidate ≡ true

    rowSharedRootClosenessIsNotIdentity :
      Bool

    rowSharedRootClosenessIsNotIdentityIsTrue :
      rowSharedRootClosenessIsNotIdentity ≡ true

    rowSharedRootClosenessIsNotCausalProof :
      Bool

    rowSharedRootClosenessIsNotCausalProofIsTrue :
      rowSharedRootClosenessIsNotCausalProof ≡ true

    rowNoSocialAuthority :
      Bool

    rowNoSocialAuthorityIsTrue :
      rowNoSocialAuthority ≡ true

    rowNoLegalAuthority :
      Bool

    rowNoLegalAuthorityIsTrue :
      rowNoLegalAuthority ≡ true

    rowNoClinicalAuthority :
      Bool

    rowNoClinicalAuthorityIsTrue :
      rowNoClinicalAuthority ≡ true

    rowReading :
      String

open AxisPrimeProductRow public

record AxisPrimeProductRowCertificate (row : AxisPrimeProductRow) : Set where
  constructor mkAxisPrimeProductRowCertificate
  field
    candidateOnlyTrue :
      rowCandidateOnly row ≡ true

    productNotSingleAxisTrue :
      rowProductNotSingleAxis row ≡ true

    sharedRootClosenessCandidateTrue :
      rowSharedRootClosenessIsCandidate row ≡ true

    sharedRootClosenessNotIdentityTrue :
      rowSharedRootClosenessIsNotIdentity row ≡ true

    sharedRootClosenessNotCausalProofTrue :
      rowSharedRootClosenessIsNotCausalProof row ≡ true

    noSocialAuthorityTrue :
      rowNoSocialAuthority row ≡ true

    noLegalAuthorityTrue :
      rowNoLegalAuthority row ≡ true

    noClinicalAuthorityTrue :
      rowNoClinicalAuthority row ≡ true

open AxisPrimeProductRowCertificate public

canonicalAxisPrimeProductRowCertificate :
  (row : AxisPrimeProductRow) →
  rowCandidateOnly row ≡ true →
  rowProductNotSingleAxis row ≡ true →
  rowSharedRootClosenessIsCandidate row ≡ true →
  rowSharedRootClosenessIsNotIdentity row ≡ true →
  rowSharedRootClosenessIsNotCausalProof row ≡ true →
  rowNoSocialAuthority row ≡ true →
  rowNoLegalAuthority row ≡ true →
  rowNoClinicalAuthority row ≡ true →
  AxisPrimeProductRowCertificate row
canonicalAxisPrimeProductRowCertificate
  row
  candidateOnlyTrue
  productNotSingleAxisTrue
  sharedRootClosenessCandidateTrue
  sharedRootClosenessNotIdentityTrue
  sharedRootClosenessNotCausalProofTrue
  noSocialAuthorityTrue
  noLegalAuthorityTrue
  noClinicalAuthorityTrue =
  mkAxisPrimeProductRowCertificate
    candidateOnlyTrue
    productNotSingleAxisTrue
    sharedRootClosenessCandidateTrue
    sharedRootClosenessNotIdentityTrue
    sharedRootClosenessNotCausalProofTrue
    noSocialAuthorityTrue
    noLegalAuthorityTrue
    noClinicalAuthorityTrue

intersectionalRacePrimeRow : AxisPrimeProductRow
intersectionalRacePrimeRow =
  mkAxisPrimeProductRow
    zero
    raceAxis
    prime2
    primeFibreKind
    primeFibreAddressKind
    "race prime-fibre row"
    "Race is represented as a prime-fibre address within a product bundle, not as an isolated single-axis truth."
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    "Race prime-fibre address is candidate-only and non-authoritative."

intersectionalClassPrimeRow : AxisPrimeProductRow
intersectionalClassPrimeRow =
  mkAxisPrimeProductRow
    (suc zero)
    classAxis
    prime3
    primeFibreKind
    primeFibreAddressKind
    "class prime-fibre row"
    "Class is represented as a prime-fibre address within an intersectional bundle."
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    "Class prime-fibre address is candidate-only and non-authoritative."

intersectionalGenderProductRow : AxisPrimeProductRow
intersectionalGenderProductRow =
  mkAxisPrimeProductRow
    (suc (suc zero))
    genderAxis
    prime5
    productFibreKind
    productFibreAddressKind
    "gender product-fibre row"
    "Gender is represented as a product-fibre address with multiple axis factors, not one collapsed axis."
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    "Gender product-fibre address is candidate-only and non-authoritative."

intersectionalDisabilitySharedRootRow : AxisPrimeProductRow
intersectionalDisabilitySharedRootRow =
  mkAxisPrimeProductRow
    (suc (suc (suc zero)))
    disabilityAxis
    prime7
    sharedRootClosenessKind
    sharedRootAddressKind
    "disability shared-root row"
    "Shared-root closeness across disability and related fibres is candidate structural affinity, not identity or cause."
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    "Shared-root closeness remains candidate-only and non-authoritative."

intersectionalInstitutionAuthorityBlockedRow : AxisPrimeProductRow
intersectionalInstitutionAuthorityBlockedRow =
  mkAxisPrimeProductRow
    (suc (suc (suc (suc zero))))
    institutionAxis
    prime11
    authorityProjectionKind
    productFibreAddressKind
    "institution authority blocked row"
    "Institutional projection cannot convert a product fibre into social, legal, or clinical authority."
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    "Institutional authority is blocked at the product-fibre boundary."

canonicalAxisPrimeProductRows : List AxisPrimeProductRow
canonicalAxisPrimeProductRows =
  intersectionalRacePrimeRow
  ∷ intersectionalClassPrimeRow
  ∷ intersectionalGenderProductRow
  ∷ intersectionalDisabilitySharedRootRow
  ∷ intersectionalInstitutionAuthorityBlockedRow
  ∷ []

canonicalAxisPrimeProductRowCount : Nat
canonicalAxisPrimeProductRowCount =
  listCount canonicalAxisPrimeProductRows

canonicalAxisPrimeProductRowCertificates :
  List (AxisPrimeProductRowCertificate intersectionalRacePrimeRow)
canonicalAxisPrimeProductRowCertificates =
  canonicalAxisPrimeProductRowCertificate
    intersectionalRacePrimeRow
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
  ∷ []

------------------------------------------------------------------------
-- Projection rows and blocked projections.

data ProjectionRoute : Set where
  candidateProjectionRoute :
    ProjectionRoute

  singleAxisProjectionRoute :
    ProjectionRoute

  productCollapseRoute :
    ProjectionRoute

  identityProjectionRoute :
    ProjectionRoute

  causalProjectionRoute :
    ProjectionRoute

  socialAuthorityProjectionRoute :
    ProjectionRoute

  legalAuthorityProjectionRoute :
    ProjectionRoute

  clinicalAuthorityProjectionRoute :
    ProjectionRoute

AdmissibleProjectionRoute :
  ProjectionRoute →
  Set
AdmissibleProjectionRoute candidateProjectionRoute = ⊤
AdmissibleProjectionRoute singleAxisProjectionRoute = Never
AdmissibleProjectionRoute productCollapseRoute = Never
AdmissibleProjectionRoute identityProjectionRoute = Never
AdmissibleProjectionRoute causalProjectionRoute = Never
AdmissibleProjectionRoute socialAuthorityProjectionRoute = Never
AdmissibleProjectionRoute legalAuthorityProjectionRoute = Never
AdmissibleProjectionRoute clinicalAuthorityProjectionRoute = Never

singleAxisProjectionRouteRejected :
  AdmissibleProjectionRoute singleAxisProjectionRoute →
  Never
singleAxisProjectionRouteRejected impossible = impossible

productCollapseRouteRejected :
  AdmissibleProjectionRoute productCollapseRoute →
  Never
productCollapseRouteRejected impossible = impossible

identityProjectionRouteRejected :
  AdmissibleProjectionRoute identityProjectionRoute →
  Never
identityProjectionRouteRejected impossible = impossible

causalProjectionRouteRejected :
  AdmissibleProjectionRoute causalProjectionRoute →
  Never
causalProjectionRouteRejected impossible = impossible

socialAuthorityProjectionRouteRejected :
  AdmissibleProjectionRoute socialAuthorityProjectionRoute →
  Never
socialAuthorityProjectionRouteRejected impossible = impossible

legalAuthorityProjectionRouteRejected :
  AdmissibleProjectionRoute legalAuthorityProjectionRoute →
  Never
legalAuthorityProjectionRouteRejected impossible = impossible

clinicalAuthorityProjectionRouteRejected :
  AdmissibleProjectionRoute clinicalAuthorityProjectionRoute →
  Never
clinicalAuthorityProjectionRouteRejected impossible = impossible

data ProjectionRowKind : Set where
  singleAxisBlockedProjectionRowKind :
    ProjectionRowKind

  productFibreBlockedProjectionRowKind :
    ProjectionRowKind

  identityCollapseBlockedProjectionRowKind :
    ProjectionRowKind

  causalProofBlockedProjectionRowKind :
    ProjectionRowKind

  socialAuthorityBlockedProjectionRowKind :
    ProjectionRowKind

  legalAuthorityBlockedProjectionRowKind :
    ProjectionRowKind

  clinicalAuthorityBlockedProjectionRowKind :
    ProjectionRowKind

canonicalProjectionRowKinds : List ProjectionRowKind
canonicalProjectionRowKinds =
  singleAxisBlockedProjectionRowKind
  ∷ productFibreBlockedProjectionRowKind
  ∷ identityCollapseBlockedProjectionRowKind
  ∷ causalProofBlockedProjectionRowKind
  ∷ socialAuthorityBlockedProjectionRowKind
  ∷ legalAuthorityBlockedProjectionRowKind
  ∷ clinicalAuthorityBlockedProjectionRowKind
  ∷ []

record BlockedProjectionRow : Set where
  constructor mkBlockedProjectionRow
  field
    rowIndex :
      Nat

    rowRoute :
      ProjectionRoute

    rowKind :
      ProjectionRowKind

    rowLabel :
      String

    rowStatement :
      String

    rowCandidateOnly :
      Bool

    rowCandidateOnlyIsTrue :
      rowCandidateOnly ≡ true

    rowProjectionBlocked :
      Bool

    rowProjectionBlockedIsTrue :
      rowProjectionBlocked ≡ true

    rowSingleAxisReductionBlocked :
      Bool

    rowSingleAxisReductionBlockedIsTrue :
      rowSingleAxisReductionBlocked ≡ true

    rowIdentityCollapseBlocked :
      Bool

    rowIdentityCollapseBlockedIsTrue :
      rowIdentityCollapseBlocked ≡ true

    rowCausalProofBlocked :
      Bool

    rowCausalProofBlockedIsTrue :
      rowCausalProofBlocked ≡ true

    rowSocialAuthorityBlocked :
      Bool

    rowSocialAuthorityBlockedIsTrue :
      rowSocialAuthorityBlocked ≡ true

    rowLegalAuthorityBlocked :
      Bool

    rowLegalAuthorityBlockedIsTrue :
      rowLegalAuthorityBlocked ≡ true

    rowClinicalAuthorityBlocked :
      Bool

    rowClinicalAuthorityBlockedIsTrue :
      rowClinicalAuthorityBlocked ≡ true

    rowReading :
      String

open BlockedProjectionRow public

record BlockedProjectionRowCertificate (row : BlockedProjectionRow) : Set where
  constructor mkBlockedProjectionRowCertificate
  field
    candidateOnlyTrue :
      rowCandidateOnly row ≡ true

    projectionBlockedTrue :
      rowProjectionBlocked row ≡ true

    singleAxisReductionBlockedTrue :
      rowSingleAxisReductionBlocked row ≡ true

    identityCollapseBlockedTrue :
      rowIdentityCollapseBlocked row ≡ true

    causalProofBlockedTrue :
      rowCausalProofBlocked row ≡ true

    socialAuthorityBlockedTrue :
      rowSocialAuthorityBlocked row ≡ true

    legalAuthorityBlockedTrue :
      rowLegalAuthorityBlocked row ≡ true

    clinicalAuthorityBlockedTrue :
      rowClinicalAuthorityBlocked row ≡ true

open BlockedProjectionRowCertificate public

canonicalBlockedProjectionRowCertificate :
  (row : BlockedProjectionRow) →
  rowCandidateOnly row ≡ true →
  rowProjectionBlocked row ≡ true →
  rowSingleAxisReductionBlocked row ≡ true →
  rowIdentityCollapseBlocked row ≡ true →
  rowCausalProofBlocked row ≡ true →
  rowSocialAuthorityBlocked row ≡ true →
  rowLegalAuthorityBlocked row ≡ true →
  rowClinicalAuthorityBlocked row ≡ true →
  BlockedProjectionRowCertificate row
canonicalBlockedProjectionRowCertificate
  row
  candidateOnlyTrue
  projectionBlockedTrue
  singleAxisReductionBlockedTrue
  identityCollapseBlockedTrue
  causalProofBlockedTrue
  socialAuthorityBlockedTrue
  legalAuthorityBlockedTrue
  clinicalAuthorityBlockedTrue =
  mkBlockedProjectionRowCertificate
    candidateOnlyTrue
    projectionBlockedTrue
    singleAxisReductionBlockedTrue
    identityCollapseBlockedTrue
    causalProofBlockedTrue
    socialAuthorityBlockedTrue
    legalAuthorityBlockedTrue
    clinicalAuthorityBlockedTrue

singleAxisBlockedProjectionRow : BlockedProjectionRow
singleAxisBlockedProjectionRow =
  mkBlockedProjectionRow
    zero
    singleAxisProjectionRoute
    singleAxisBlockedProjectionRowKind
    "single-axis blocked projection row"
    "A single axis cannot reconstruct the product fibre of an intersectional bundle."
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    "Single-axis projection is blocked."

productFibreBlockedProjectionRow : BlockedProjectionRow
productFibreBlockedProjectionRow =
  mkBlockedProjectionRow
    (suc zero)
    productCollapseRoute
    productFibreBlockedProjectionRowKind
    "product-fibre blocked projection row"
    "A product fibre is not reducible to one axis or a collapsed universal axis."
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    "Product-fibre reduction is blocked."

identityCollapseBlockedProjectionRow : BlockedProjectionRow
identityCollapseBlockedProjectionRow =
  mkBlockedProjectionRow
    (suc (suc zero))
    identityProjectionRoute
    identityCollapseBlockedProjectionRowKind
    "identity-collapse blocked projection row"
    "Identity collapse is blocked; shared-root closeness is not identity."
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    "Identity collapse is blocked."

causalProofBlockedProjectionRow : BlockedProjectionRow
causalProofBlockedProjectionRow =
  mkBlockedProjectionRow
    (suc (suc (suc zero)))
    causalProjectionRoute
    causalProofBlockedProjectionRowKind
    "causal-proof blocked projection row"
    "p-adic or shared-root closeness is candidate structural affinity, not causal proof."
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    "Causal proof projection is blocked."

socialAuthorityBlockedProjectionRow : BlockedProjectionRow
socialAuthorityBlockedProjectionRow =
  mkBlockedProjectionRow
    (suc (suc (suc (suc zero))))
    socialAuthorityProjectionRoute
    socialAuthorityBlockedProjectionRowKind
    "social-authority blocked projection row"
    "Social authority does not follow from axis or fibre address."
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    "Social authority is blocked."

legalAuthorityBlockedProjectionRow : BlockedProjectionRow
legalAuthorityBlockedProjectionRow =
  mkBlockedProjectionRow
    (suc (suc (suc (suc (suc zero)))))
    legalAuthorityProjectionRoute
    legalAuthorityBlockedProjectionRowKind
    "legal-authority blocked projection row"
    "Legal authority is not promoted by a product fibre address."
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    "Legal authority is blocked."

clinicalAuthorityBlockedProjectionRow : BlockedProjectionRow
clinicalAuthorityBlockedProjectionRow =
  mkBlockedProjectionRow
    (suc (suc (suc (suc (suc (suc zero))))))
    clinicalAuthorityProjectionRoute
    clinicalAuthorityBlockedProjectionRowKind
    "clinical-authority blocked projection row"
    "Clinical authority is blocked; the receipt is not diagnostic or therapeutic."
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    "Clinical authority is blocked."

canonicalBlockedProjectionRows : List BlockedProjectionRow
canonicalBlockedProjectionRows =
  singleAxisBlockedProjectionRow
  ∷ productFibreBlockedProjectionRow
  ∷ identityCollapseBlockedProjectionRow
  ∷ causalProofBlockedProjectionRow
  ∷ socialAuthorityBlockedProjectionRow
  ∷ legalAuthorityBlockedProjectionRow
  ∷ clinicalAuthorityBlockedProjectionRow
  ∷ []

canonicalBlockedProjectionRowCount : Nat
canonicalBlockedProjectionRowCount =
  listCount canonicalBlockedProjectionRows

------------------------------------------------------------------------
-- Aggregate receipt.

record AxisBundlePrimeFibreReceipt : Set where
  constructor mkAxisBundlePrimeFibreReceipt
  field
    route :
      PrimeFibreRoute

    routeIsCandidate :
      route ≡ candidateOnlyRoute

    routeAdmissible :
      AdmissiblePrimeFibreRoute route

    routeGates :
      List RouteGate

    routeGatesAreCanonical :
      routeGates ≡ canonicalRouteGates

    intersectionalAxes :
      List IntersectionalAxis

    intersectionalAxesAreCanonical :
      intersectionalAxes ≡ canonicalIntersectionalAxes

    primeKinds :
      List PrimeKind

    primeKindsAreCanonical :
      primeKinds ≡ canonicalPrimeKinds

    fibreKinds :
      List FibreKind

    fibreKindsAreCanonical :
      fibreKinds ≡ canonicalFibreKinds

    addressKinds :
      List AddressKind

    addressKindsAreCanonical :
      addressKinds ≡ canonicalAddressKinds

    productRows :
      List AxisPrimeProductRow

    productRowsAreCanonical :
      productRows ≡ canonicalAxisPrimeProductRows

    blockedProjectionRows :
      List BlockedProjectionRow

    blockedProjectionRowsAreCanonical :
      blockedProjectionRows ≡ canonicalBlockedProjectionRows

    productRowCount :
      Nat

    productRowCountIsCanonical :
      productRowCount ≡ canonicalAxisPrimeProductRowCount

    blockedProjectionRowCount :
      Nat

    blockedProjectionRowCountIsCanonical :
      blockedProjectionRowCount ≡ canonicalBlockedProjectionRowCount

    productNotSingleAxisGate :
      Bool

    productNotSingleAxisGateIsTrue :
      productNotSingleAxisGate ≡ true

    sharedRootClosenessCandidateGate :
      Bool

    sharedRootClosenessCandidateGateIsTrue :
      sharedRootClosenessCandidateGate ≡ true

    sharedRootClosenessNotIdentityGate :
      Bool

    sharedRootClosenessNotIdentityGateIsTrue :
      sharedRootClosenessNotIdentityGate ≡ true

    sharedRootClosenessNotCausalProofGate :
      Bool

    sharedRootClosenessNotCausalProofGateIsTrue :
      sharedRootClosenessNotCausalProofGate ≡ true

    noSocialAuthorityGate :
      Bool

    noSocialAuthorityGateIsTrue :
      noSocialAuthorityGate ≡ true

    noLegalAuthorityGate :
      Bool

    noLegalAuthorityGateIsTrue :
      noLegalAuthorityGate ≡ true

    noClinicalAuthorityGate :
      Bool

    noClinicalAuthorityGateIsTrue :
      noClinicalAuthorityGate ≡ true

    receiptStatement :
      String

open AxisBundlePrimeFibreReceipt public

canonicalAxisBundlePrimeFibreReceipt :
  AxisBundlePrimeFibreReceipt
canonicalAxisBundlePrimeFibreReceipt =
  mkAxisBundlePrimeFibreReceipt
    candidateOnlyRoute
    refl
    tt
    canonicalRouteGates
    refl
    canonicalIntersectionalAxes
    refl
    canonicalPrimeKinds
    refl
    canonicalFibreKinds
    refl
    canonicalAddressKinds
    refl
    canonicalAxisPrimeProductRows
    refl
    canonicalBlockedProjectionRows
    refl
    canonicalAxisPrimeProductRowCount
    refl
    canonicalBlockedProjectionRowCount
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    "Axis bundle prime-fibre receipt: intersectional axes are preserved as prime-fibre/product-fibre addresses, product fibre is not a single axis, shared-root closeness is only candidate structural affinity, and social/legal/clinical authority are blocked."

------------------------------------------------------------------------
-- Top-level lemmas as boolean/gate receipts.

primeProductNotSingleAxisProjection :
  Bool
primeProductNotSingleAxisProjection =
  productNotSingleAxisGate canonicalAxisBundlePrimeFibreReceipt

primeProductNotSingleAxisProjectionIsTrue :
  primeProductNotSingleAxisProjection ≡ true
primeProductNotSingleAxisProjectionIsTrue =
  productNotSingleAxisGateIsTrue canonicalAxisBundlePrimeFibreReceipt

sharedRootClosenessIsCandidate :
  Bool
sharedRootClosenessIsCandidate =
  sharedRootClosenessCandidateGate canonicalAxisBundlePrimeFibreReceipt

sharedRootClosenessIsCandidateIsTrue :
  sharedRootClosenessIsCandidate ≡ true
sharedRootClosenessIsCandidateIsTrue =
  sharedRootClosenessCandidateGateIsTrue canonicalAxisBundlePrimeFibreReceipt

sharedRootClosenessIsNotIdentity :
  Bool
sharedRootClosenessIsNotIdentity =
  sharedRootClosenessNotIdentityGate canonicalAxisBundlePrimeFibreReceipt

sharedRootClosenessIsNotIdentityIsTrue :
  sharedRootClosenessIsNotIdentity ≡ true
sharedRootClosenessIsNotIdentityIsTrue =
  sharedRootClosenessNotIdentityGateIsTrue canonicalAxisBundlePrimeFibreReceipt

sharedRootClosenessIsNotCausalProof :
  Bool
sharedRootClosenessIsNotCausalProof =
  sharedRootClosenessNotCausalProofGate canonicalAxisBundlePrimeFibreReceipt

sharedRootClosenessIsNotCausalProofIsTrue :
  sharedRootClosenessIsNotCausalProof ≡ true
sharedRootClosenessIsNotCausalProofIsTrue =
  sharedRootClosenessNotCausalProofGateIsTrue canonicalAxisBundlePrimeFibreReceipt

noSocialAuthority :
  Bool
noSocialAuthority =
  noSocialAuthorityGate canonicalAxisBundlePrimeFibreReceipt

noSocialAuthorityIsTrue :
  noSocialAuthority ≡ true
noSocialAuthorityIsTrue =
  noSocialAuthorityGateIsTrue canonicalAxisBundlePrimeFibreReceipt

noLegalAuthority :
  Bool
noLegalAuthority =
  noLegalAuthorityGate canonicalAxisBundlePrimeFibreReceipt

noLegalAuthorityIsTrue :
  noLegalAuthority ≡ true
noLegalAuthorityIsTrue =
  noLegalAuthorityGateIsTrue canonicalAxisBundlePrimeFibreReceipt

noClinicalAuthority :
  Bool
noClinicalAuthority =
  noClinicalAuthorityGate canonicalAxisBundlePrimeFibreReceipt

noClinicalAuthorityIsTrue :
  noClinicalAuthority ≡ true
noClinicalAuthorityIsTrue =
  noClinicalAuthorityGateIsTrue canonicalAxisBundlePrimeFibreReceipt

