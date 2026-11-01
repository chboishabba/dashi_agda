module DASHI.Interop.ITIRActorIdentitySpine where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Canonical ITIR actor identity spine.
--
-- The canonical actor carrier remains deliberately small.  Biographical,
-- contact, address, organisation, and institution attributes live in typed
-- extension rows with their own provenance and merge rules.  A CRM may be an
-- upstream connector, but it is never the canonical identity authority.

data ActorKind : Set where
  personActor : ActorKind
  organisationActor : ActorKind
  institutionActor : ActorKind
  pseudonymActor : ActorKind
  otherActor : ActorKind

record ActorIdentity : Set where
  constructor actorIdentity
  field
    actorId : Nat
    actorKind : ActorKind
    displayName : String

open ActorIdentity public

record AddressRow : Set where
  constructor addressRow
  field
    addressId : Nat
    line1 : String
    line2 : String
    locality : String
    region : String
    postcode : String
    country : String

record PersonDetailRow : Set where
  constructor personDetailRow
  field
    personActorId : Nat
    givenName : String
    familyName : String
    birthdate : String
    pronouns : String
    genderIdentity : String
    ethnicity : String
    personAddressId : Nat

record OrganisationDetailRow : Set where
  constructor organisationDetailRow
  field
    organisationActorId : Nat
    legalName : String
    registrationNumber : String
    organisationType : String
    organisationAddressId : Nat

record InstitutionDetailRow : Set where
  constructor institutionDetailRow
  field
    institutionActorId : Nat
    jurisdiction : String
    institutionLevel : String
    division : String
    institutionAddressId : Nat

record ContactPointRow : Set where
  constructor contactPointRow
  field
    contactPointId : Nat
    contactActorId : Nat
    contactKind : String
    contactValue : String
    contactLabel : String

record ActorAliasRow : Set where
  constructor actorAliasRow
  field
    aliasId : Nat
    aliasActorId : Nat
    aliasText : String
    aliasSource : String
    aliasConfidence : Nat

record ActorMergeReceipt : Set where
  constructor actorMergeReceipt
  field
    survivingActorId : Nat
    mergedActorId : Nat
    mergeReason : String
    mergeSource : String

record CRMConnectorMapping : Set where
  constructor crmConnectorMapping
  field
    connectorName : String
    externalContactId : String
    canonicalActorId : Nat
    selectedFieldImportOnly : Bool
    selectedFieldImportOnlyIsTrue : selectedFieldImportOnly ≡ true
    crmIsCanonicalAuthority : Bool
    crmIsCanonicalAuthorityIsFalse : crmIsCanonicalAuthority ≡ false

record ActorIdentityAuthorityBits : Set where
  field
    actorSpineIsMinimal : Bool
    actorSpineIsMinimalIsTrue : actorSpineIsMinimal ≡ true
    descriptiveAttributesStayInExtensions : Bool
    descriptiveAttributesStayInExtensionsIsTrue :
      descriptiveAttributesStayInExtensions ≡ true
    mergesRequireReceipts : Bool
    mergesRequireReceiptsIsTrue : mergesRequireReceipts ≡ true
    crmConnectorOnly : Bool
    crmConnectorOnlyIsTrue : crmConnectorOnly ≡ true
    crmCanonicalAuthority : Bool
    crmCanonicalAuthorityIsFalse : crmCanonicalAuthority ≡ false
    piiInCanonicalActor : Bool
    piiInCanonicalActorIsFalse : piiInCanonicalActor ≡ false

open ActorIdentityAuthorityBits public

canonicalActorIdentityAuthorityBits : ActorIdentityAuthorityBits
canonicalActorIdentityAuthorityBits =
  record
    { actorSpineIsMinimal = true
    ; actorSpineIsMinimalIsTrue = refl
    ; descriptiveAttributesStayInExtensions = true
    ; descriptiveAttributesStayInExtensionsIsTrue = refl
    ; mergesRequireReceipts = true
    ; mergesRequireReceiptsIsTrue = refl
    ; crmConnectorOnly = true
    ; crmConnectorOnlyIsTrue = refl
    ; crmCanonicalAuthority = false
    ; crmCanonicalAuthorityIsFalse = refl
    ; piiInCanonicalActor = false
    ; piiInCanonicalActorIsFalse = refl
    }

record ITIRActorIdentitySpine : Set where
  field
    canonicalActor : ActorIdentity
    aliases : List ActorAliasRow
    personDetails : List PersonDetailRow
    organisationDetails : List OrganisationDetailRow
    institutionDetails : List InstitutionDetailRow
    addresses : List AddressRow
    contactPoints : List ContactPointRow
    mergeReceipts : List ActorMergeReceipt
    crmMappings : List CRMConnectorMapping
    authorityBits : ActorIdentityAuthorityBits
    notes : List String

open ITIRActorIdentitySpine public

canonicalITIRActorIdentitySpine : ITIRActorIdentitySpine
canonicalITIRActorIdentitySpine =
  record
    { canonicalActor = actorIdentity 0 personActor "canonical actor"
    ; aliases = []
    ; personDetails = []
    ; organisationDetails = []
    ; institutionDetails = []
    ; addresses = []
    ; contactPoints = []
    ; mergeReceipts = []
    ; crmMappings = []
    ; authorityBits = canonicalActorIdentityAuthorityBits
    ; notes =
        "Actor identity is the stable cross-source spine; attributes are not identity."
      ∷ "Person, organisation, institution, address, and contact rows retain separate provenance and merge semantics."
      ∷ "A CRM is an optional upstream adapter and never the ITIR source of truth."
      ∷ []
    }
