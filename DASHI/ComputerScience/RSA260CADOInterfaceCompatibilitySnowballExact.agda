module DASHI.ComputerScience.RSA260CADOInterfaceCompatibilitySnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.ComputerScience.RSA260GNFSRunParameterArtifactSnowballExact as Run

------------------------------------------------------------------------
-- RSA-260 / CADO INTERFACE COMPATIBILITY SNOWBALL
--
-- Consumer: distinguish inherited parameter/interface shape from exact source
-- identity.  Stock CADO supports many of the named parameter coordinates used
-- in Lu's RSA-260 appendix (e.g. las.threads, filtering target_density,
-- purge.keep, required_excess, bwc.pl and mm_impl), but matching an interface
-- slot does not prove the downstream implementation is stock CADO.
--
-- In particular, current upstream CADO documents mm_impl as a selectable
-- matrix-multiplication backend, while the stock backend list does not include
-- `cuda`.  Lu's first-party account reports mm_impl=cuda and a new
-- GPU-optimized Block Wiedemann implementation.  This supports an interface-
-- extension relationship, not exact-source identity.
------------------------------------------------------------------------

data InterfaceRelationship : Set where
  upstreamParameterCoordinate : InterfaceRelationship
  downstreamUsesUpstreamCoordinate : InterfaceRelationship
  downstreamExtendsCoordinateValueSpace : InterfaceRelationship
  downstreamParameterUnresolvedUpstream : InterfaceRelationship

record InterfaceCompatibilityReceipt : Set where
  constructor interface-compatibility-receipt
  field
    parameterReference : String
    relationship : InterfaceRelationship
    upstreamEvidence : String
    downstreamEvidence : String
    parameterNameShared : Bool
    stockValueConfirmed : Bool
    exactCodePathSameObjectPaid : Bool
    semanticEquivalencePaid : Bool
open InterfaceCompatibilityReceipt public

lasThreadsCompatibility : InterfaceCompatibilityReceipt
lasThreadsCompatibility =
  interface-compatibility-receipt
    "tasks.sieve.las.threads / las.threads"
    downstreamUsesUpstreamCoordinate
    "CADO parameter tree and shipped parameter files document tasks.sieve.las.threads"
    "Eric Lu Appendix 3 publishes las.threads=22 for RSA-260"
    true true false false

filterTargetDensityCompatibility : InterfaceCompatibilityReceipt
filterTargetDensityCompatibility =
  interface-compatibility-receipt
    "tasks.filter.target_density / target_density"
    downstreamUsesUpstreamCoordinate
    "CADO shipped parameter files document target_density together with purge.keep and required_excess"
    "Eric Lu Appendix 3 publishes target_density=150.0 and purge.keep=160 for RSA-260"
    true true false false

bwcMMImplCompatibility : InterfaceCompatibilityReceipt
bwcMMImplCompatibility =
  interface-compatibility-receipt
    "bwc mm_impl"
    downstreamExtendsCoordinateValueSpace
    "CADO BWC sources document mm_impl as the lower-layer matrix multiplication implementation selector; stock documentation lists CPU-oriented backends such as basic/sliced/bucket/basicp/zone"
    "Eric Lu Appendix 3 publishes mm_impl=cuda and reports a new GPU-optimized Block Wiedemann implementation"
    true false false false

commImplCompatibility : InterfaceCompatibilityReceipt
commImplCompatibility =
  interface-compatibility-receipt
    "comm_impl=nccl"
    downstreamParameterUnresolvedUpstream
    "current public CADO code search in this acquisition pass did not locate a stock comm_impl parameter"
    "Eric Lu Appendix 3 publishes comm_impl=nccl for RSA-260 linear algebra"
    false false false false

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data SameParameterNameImpliesSameImplementation : Set where
data UpstreamParameterSlotImpliesStockDownstreamValue : Set where
data CompatibleRunScriptImpliesExactSourceIdentity : Set where
data UnlocatedUpstreamParameterMeansDownstreamInvented : Set where

sameNameDoesNotIdentifyImplementation : SameParameterNameImpliesSameImplementation → ⊥
sameNameDoesNotIdentifyImplementation ()

slotDoesNotMakeValueStock : UpstreamParameterSlotImpliesStockDownstreamValue → ⊥
slotDoesNotMakeValueStock ()

compatibleScriptDoesNotIdentifySource : CompatibleRunScriptImpliesExactSourceIdentity → ⊥
compatibleScriptDoesNotIdentifySource ()

searchMissDoesNotProveNovelty : UnlocatedUpstreamParameterMeansDownstreamInvented → ⊥
searchMissDoesNotProveNovelty ()

record RSA260CADOInterfaceBoundary : Set where
  constructor rsa260-cado-interface-boundary
  field
    inheritedParameterCoordinatesRetained : Bool
    cudaBackendTypedAsDownstreamExtensionCandidate : Bool
    commImplUpstreamStatusUnresolved : Bool
    exactModifiedSourceStillUnknown : Bool
    interfaceCompatibilityCreatesSourceIdentity : Bool
open RSA260CADOInterfaceBoundary public

canonicalRSA260CADOInterfaceBoundary : RSA260CADOInterfaceBoundary
canonicalRSA260CADOInterfaceBoundary =
  rsa260-cado-interface-boundary true true true true false
