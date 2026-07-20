module DASHI.Physics.YangMills.SUNMatrixLieGroup where

------------------------------------------------------------------------
-- Group-parametric SU(N) adjoint action and compact-simple Lie-group assembly.
-- Global topology, matrix exponential and local logarithm are standard imported
-- authority fields. The resulting carrier and all record wiring are checked.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieGroupCore
open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.SUNMatrixCarrier
open import DASHI.Physics.YangMills.SUNMatrixLieAlgebra

rawAdjoint :
  ∀ {m c N} {Matrix : Set m} {Complex : Set c}
    {groupTheory : CertifiedSUNMatrixTheory N Matrix Complex} →
  Matrix → Matrix → Matrix
rawAdjoint {groupTheory = groupTheory} U X =
  multiplyM (operations groupTheory) U
    (multiplyM (operations groupTheory) X
      (daggerM (operations groupTheory) U))

record CertifiedSUNMatrixLieGroupAuthority
    {m c : Level} (N : Nat)
    {Matrix : Set m} {Complex : Set c}
    (groupTheory : CertifiedSUNMatrixTheory N Matrix Complex)
    (lieTheory : CertifiedSUNMatrixLieTheory N groupTheory) :
    Set (lsuc (m ⊔ c)) where
  field
    exponentialRaw : Matrix → Matrix
    logarithmRaw : Matrix → Matrix

    exponentialClosed : ∀ {X} →
      IsSUNLieElement (lieOperations lieTheory) X →
      IsSpecialUnitary (operations groupTheory) (exponentialRaw X)
    logarithmClosed : ∀ {U} →
      IsSpecialUnitary (operations groupTheory) U →
      IsSUNLieElement (lieOperations lieTheory) (logarithmRaw U)
    adjointClosed : ∀ {U X} →
      IsSpecialUnitary (operations groupTheory) U →
      IsSUNLieElement (lieOperations lieTheory) X →
      IsSUNLieElement (lieOperations lieTheory) (rawAdjoint U X)

    adjointIdentityRaw : ∀ X →
      rawAdjoint (identityM (operations groupTheory)) X ≡ X
    adjointProductRaw : ∀ U V X →
      rawAdjoint (multiplyM (operations groupTheory) U V) X ≡
      rawAdjoint U (rawAdjoint V X)
    adjointBracketRaw : ∀ U X Y →
      rawAdjoint U (commutator (lieOperations lieTheory) X Y) ≡
      commutator (lieOperations lieTheory)
        (rawAdjoint U X) (rawAdjoint U Y)

    ConjugatesExponentials : Set (m ⊔ c)
    conjugatesExponentials : ConjugatesExponentials
    Compact : Set (m ⊔ c)
    Connected : Set (m ⊔ c)
    SimpleLieAlgebra : Set (m ⊔ c)
    compact : Compact
    connected : Connected
    simpleLieAlgebra : SimpleLieAlgebra

open CertifiedSUNMatrixLieGroupAuthority public

sunExp :
  ∀ {m c N} {Matrix : Set m} {Complex : Set c}
    {groupTheory : CertifiedSUNMatrixTheory N Matrix Complex}
    {lieTheory : CertifiedSUNMatrixLieTheory N groupTheory} →
  CertifiedSUNMatrixLieGroupAuthority N groupTheory lieTheory →
  SUNMatrixLieElement lieTheory → SUNMatrixElement groupTheory
sunExp authority X =
  sunMatrix
    (exponentialRaw authority (lieMatrix X))
    (exponentialClosed authority (isSUNLie X))

sunLog :
  ∀ {m c N} {Matrix : Set m} {Complex : Set c}
    {groupTheory : CertifiedSUNMatrixTheory N Matrix Complex}
    {lieTheory : CertifiedSUNMatrixLieTheory N groupTheory} →
  CertifiedSUNMatrixLieGroupAuthority N groupTheory lieTheory →
  SUNMatrixElement groupTheory → SUNMatrixLieElement lieTheory
sunLog authority U =
  sunLieMatrix
    (logarithmRaw authority (matrix U))
    (logarithmClosed authority (specialUnitary U))

sunAd :
  ∀ {m c N} {Matrix : Set m} {Complex : Set c}
    {groupTheory : CertifiedSUNMatrixTheory N Matrix Complex}
    {lieTheory : CertifiedSUNMatrixLieTheory N groupTheory} →
  CertifiedSUNMatrixLieGroupAuthority N groupTheory lieTheory →
  SUNMatrixElement groupTheory →
  SUNMatrixLieElement lieTheory → SUNMatrixLieElement lieTheory
sunAd authority U X =
  sunLieMatrix
    (rawAdjoint (matrix U) (lieMatrix X))
    (adjointClosed authority (specialUnitary U) (isSUNLie X))

sunCompactSimpleLieGroup :
  ∀ {m c N} {Matrix : Set m} {Complex : Set c}
    {groupTheory : CertifiedSUNMatrixTheory N Matrix Complex}
    {lieTheory : CertifiedSUNMatrixLieTheory N groupTheory} →
  (authority : CertifiedSUNMatrixLieGroupAuthority N groupTheory lieTheory) →
  CompactSimpleLieGroup
    (SUNMatrixElement groupTheory)
    (SUNMatrixLieElement lieTheory)
sunCompactSimpleLieGroup {groupTheory = groupTheory} {lieTheory = lieTheory} authority = record
  { group = sunMatrixGroup groupTheory
  ; algebra = sunMatrixLieAlgebra lieTheory
  ; exp = sunExp authority
  ; log = sunLog authority
  ; Ad = sunAd authority
  ; adjointIdentity = λ X →
      sunLieMatrixExt (adjointIdentityRaw authority (lieMatrix X))
  ; adjointProduct = λ U V X →
      sunLieMatrixExt (adjointProductRaw authority (matrix U) (matrix V) (lieMatrix X))
  ; adjointBracket = λ U X Y →
      sunLieMatrixExt (adjointBracketRaw authority (matrix U) (lieMatrix X) (lieMatrix Y))
  ; ConjugatesExponentials = ConjugatesExponentials authority
  ; conjugatesExponentials = conjugatesExponentials authority
  ; Compact = Compact authority
  ; Connected = Connected authority
  ; SimpleLieAlgebra = SimpleLieAlgebra authority
  ; compact = compact authority
  ; connected = connected authority
  ; simpleLieAlgebra = simpleLieAlgebra authority
  }

sunMatrixLieGroupAssemblyLevel : ProofLevel
sunMatrixLieGroupAssemblyLevel = machineChecked

sunTopologyAndExponentialAuthorityLevel : ProofLevel
sunTopologyAndExponentialAuthorityLevel = standardImported
