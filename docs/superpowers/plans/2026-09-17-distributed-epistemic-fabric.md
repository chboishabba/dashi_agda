# Distributed Epistemic Fabric implementation plan

## Goal

Formalise the distributed epistemic architecture discussed 2026-09-17 using existing DASHI/SensibLaw machinery while preserving strict source, ownership, authority, execution and licence boundaries.

## Original tranche

1. `DistributedEpistemicFabricSourceAtlasExact.agda`
   - separate JMD/meta-introspector source observations, Johl Brown discussion-origin architecture, external technology coordinates, and DASHI synthesis;
   - record inspected JMD repository licence states without inferring rights from public visibility or missing root licences.
2. `DistributedEpistemicPlaneSeparationExact.agda`
   - artifact/history/projection/access/contract/proof/admission/settlement planes;
   - reuse canonical federated content boundary;
   - pin cross-plane authority firewalls.
3. `DistributedProofProducerABIExact.agda`
   - `Think | Look | Review` routing;
   - revision-bound proof receipts;
   - SLR recurrence when proof search exposes source debt.
4. `SituatedInformationAccessFabricExact.agda`
   - situated access coordinates;
   - public/common and premium-capability same-information fixture;
   - access/contract/settlement non-collapse firewalls.
5. `DistributedEpistemicFabricValidation.agda`
   - focused source-order RED validation and stable contract pins.

## Approved attachment-driven extension

6. `DistributedEvidenceHistoryProjectionExact.agda`
   - refine the lower braid into byte collection, content-addressed object, signed observation, authenticated history, deterministic consumer projection and query/index;
   - reuse the canonical SensibLaw federated-content and Postgres materialisation boundaries;
   - provide a positive auditable-derived-view receipt retaining source, observation, history and projection identities without promoting truth.
7. `ImmutableEvidenceSupersessionExact.agda`
   - represent revision as an explicit relation between immutable source identities rather than destructive mutation;
   - retain earlier and later identities and prevent supersession from manufacturing invalidation, authority or retroactive falsity.
8. `ReplicationCapabilityNonCollapseExact.agda`
   - separate offline-first, local-first, P2P, decentralised authority, cryptographic provenance, bulk swarming, linked-object graphs, authenticated histories, deterministic views, semantic CRDT state, discovery/query, local materialisation and server-selective sync;
   - treat BitTorrent, IPFS/IPLD/IPNS, Hypercore/Autobase, OrbitDB, Peerbit, Automerge/Yjs, SQLite/RxDB/Postgres, PowerSync/Electric and Replicache as external capability precedents rather than a ranking or deployment claim.
9. Extend the attributed source atlas with Hypercore, Autobase, Peerbit, Automerge and Yjs project coordinates.
10. Strengthen the focused validation root to pin positive derived-view/supersession receipts and the new capability/non-collapse theorem surface.

## Attribution rule

- JMD/meta-introspector retains attribution for observed repository artefacts and source-level implementation architecture actually inspected.
- Johl Brown is attributed for the 2026-09-17 discussion-origin architectural composition, situated-access framing, and evidence/history/projection refinement proposal.
- External projects retain their own technology/project claims.
- DASHI owns the typed reconstruction, finite fixtures, integration theorems and non-collapse firewalls authored in `dashi_agda`.
- Attribution does not adjudicate legal title, exclusive priority or licence compatibility.
- Licence observation does not itself create a reuse right; missing root licence observation does not determine permission.

## Verification boundary

Source-order RED is distinct from compiler RED. Source-written/interface-audited is distinct from Agda/kernel GREEN. No exact-head kernel certification is claimed until an Agda execution receipt exists for the branch head.