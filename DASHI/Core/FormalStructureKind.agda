module DASHI.Core.FormalStructureKind where

open import DASHI.Core.Prelude
open import DASHI.Core.FormalRole

-- Mathematical structure is kept distinct from the contextual job played by a
-- term.  A Hamiltonian may play an operator, observable, invariant, or
-- optimization role; the role and the structure therefore cannot be collapsed.
data FormalStructureKind : Set where
  plainCarrierStructure
  algebraStructure
  groupStructure
  categoryStructure
  graphStructure
  topologyStructure
  geometryStructure
  metricStructure
  operatorStructure
  hamiltonianStructure
  spectralStructure
  statisticalStructure
  probabilityStructure
  dynamicalStructure
  controlStructure
  provenanceStructure
  governanceStructure
  historicalStructure
  namedStructure : FormalStructureKind

record StructuredRole (D : RoleFamily) : Set₁ where
  field
    structuredRole    : FormalRole
    structureKind     : FormalStructureKind
    structuredPayload : RoleType D structuredRole

open StructuredRole public

-- Structure relabelling requires an explicit witness.  Merely reusing the same
-- payload does not identify two mathematical structures.
record StructureBridge (from to : FormalStructureKind) : Set where
  field
    structureBridgeWitness : Set

open StructureBridge public
