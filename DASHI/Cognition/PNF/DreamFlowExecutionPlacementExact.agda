module DASHI.Cognition.PNF.DreamFlowExecutionPlacementExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

------------------------------------------------------------------------
-- Placement law for the delta-native PNF dream flow.
--
-- The semantic algebra does not dictate one physical engine.  Placement is a
-- separate implementation decision constrained by four capabilities:
--
--   local fibre compute      -- CPU-local, low-latency, ephemeral;
--   durable global authority -- database-owned persistent semantic identity;
--   indexed global relation  -- database-owned cross-fibre/corpus lookup;
--   fused publication        -- batched crossing of the process/database edge.
--
-- In particular, persistence is not a reason to execute each microscopic PNF
-- operation inside PostgreSQL, and locality is not a reason to make Python
-- object graphs semantic authority.
------------------------------------------------------------------------

data Placement : Set where
  localNative databaseAuthority : Placement

data OperationClass : Set where
  parserProjection
  fibreAddress
  localPNFSolve
  localResidualJoin
  localDeltaCompose
  deltaTransport
  globalIdentityLookup
  globalTemplateLookup
  globalCrossFibreJoin
  durableDeltaAppend
  authorityPublication
  auditRebuild : OperationClass

idealPlacement : OperationClass → Placement
idealPlacement parserProjection = localNative
idealPlacement fibreAddress = localNative
idealPlacement localPNFSolve = localNative
idealPlacement localResidualJoin = localNative
idealPlacement localDeltaCompose = localNative
idealPlacement deltaTransport = localNative
idealPlacement globalIdentityLookup = databaseAuthority
idealPlacement globalTemplateLookup = databaseAuthority
idealPlacement globalCrossFibreJoin = databaseAuthority
idealPlacement durableDeltaAppend = databaseAuthority
idealPlacement authorityPublication = databaseAuthority
idealPlacement auditRebuild = databaseAuthority

------------------------------------------------------------------------
-- Boundary batching.
------------------------------------------------------------------------

record DatabaseBoundaryBatch (Delta : Set) : Set where
  field
    batchDelta : Delta
    representedDeltaCount : Nat

open DatabaseBoundaryBatch public

record FusedDatabaseBoundary
    (Delta Database Authority : Set) : Set₁ where
  field
    appendBatch : Database → DatabaseBoundaryBatch Delta → Database
    observeAuthority : Database → Authority
    applyDelta : Authority → Delta → Authority

    batchExact :
      ∀ database batch →
      observeAuthority (appendBatch database batch)
        ≡ applyDelta (observeAuthority database) (batchDelta batch)

open FusedDatabaseBoundary public

------------------------------------------------------------------------
-- Local state is a cache/carrier, never durable authority by declaration.
------------------------------------------------------------------------

record LocalFibreCarrier (Input Fibre Delta : Set) : Set₁ where
  field
    address : Input → Fibre
    solve : Input → Fibre → Delta

open LocalFibreCarrier public

data LocalObjectGraphAsAuthorityPermission : Set where

data PerDeltaDatabaseRoundTripRequiredPermission : Set where

localObjectGraphCannotBecomeAuthorityByPlacement :
  LocalObjectGraphAsAuthorityPermission → ∀ {A : Set} → A
localObjectGraphCannotBecomeAuthorityByPlacement ()

perDeltaRoundTripIsNotSemanticallyRequired :
  PerDeltaDatabaseRoundTripRequiredPermission → ∀ {A : Set} → A
perDeltaRoundTripIsNotSemanticallyRequired ()

------------------------------------------------------------------------
-- Stable identity may be database-owned while lookup is amortized locally.
-- The local cache may answer only when it is extensionally equal to database
-- authority for the queried key.
------------------------------------------------------------------------

record AuthorityBackedCache (Key Value Cache Database : Set) : Set₁ where
  field
    databaseLookup : Database → Key → Value
    cacheLookup : Cache → Key → Value
    cacheSound :
      ∀ cache database key →
      cacheLookup cache key ≡ databaseLookup database key

open AuthorityBackedCache public

------------------------------------------------------------------------
-- Placement boundary: operations that need only one fibre and no durable/global
-- relation have no semantic reason to cross into the database. Operations whose
-- answer depends on corpus/global authority have no semantic reason to be
-- reconstructed from process-local object state.
------------------------------------------------------------------------

data LocalFibreOperationRequiresGlobalDatabaseState : Set where

data GlobalAuthorityMayBeGuessedFromLocalCarrier : Set where

localFibreOperationNeedNotReadGlobalDatabaseState :
  LocalFibreOperationRequiresGlobalDatabaseState → ∀ {A : Set} → A
localFibreOperationNeedNotReadGlobalDatabaseState ()

globalAuthorityCannotBeGuessedFromLocalCarrier :
  GlobalAuthorityMayBeGuessedFromLocalCarrier → ∀ {A : Set} → A
globalAuthorityCannotBeGuessedFromLocalCarrier ()
