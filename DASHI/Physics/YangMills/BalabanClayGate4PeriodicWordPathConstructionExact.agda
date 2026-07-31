module DASHI.Physics.YangMills.BalabanClayGate4PeriodicWordPathConstructionExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanRootedPolymerWordEntropyExact
  using (SignedAxis4)

import DASHI.Physics.YangMills.BalabanClayT2PeriodicBlockPolymerCarrierExact as Periodic
import DASHI.Physics.YangMills.BalabanClayT2PeriodicAdjacencyBFSExact as Adjacency
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bond

------------------------------------------------------------------------
-- Exact construction of a proof-bearing periodic path from any signed word.
--
-- Tadeusz Bałaban,
-- "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
--
-- Every signed-axis word determines a literal periodic walk.  Because every
-- signed step is proved adjacent by the repository's finite torus carrier, the
-- same word canonically constructs a `PeriodicPath` to its computed endpoint.
-- A separately proved endpoint equality transports that path to any named
-- endpoint.  This removes a second abstract path-existence assumption from the
-- printed CMP109 contour construction.
------------------------------------------------------------------------

wordToPeriodicPath :
  ∀ {n} (start : Periodic.PeriodicBlock n)
    (directions : List SignedAxis4) →
  Adjacency.PeriodicPath start (Bond.walk start directions)
wordToPeriodicPath start [] = Adjacency.pathStop
wordToPeriodicPath start (direction ∷ directions) =
  Adjacency.pathStep
    (Adjacency.signedStepAdjacent start direction)
    (wordToPeriodicPath (Bond.walkStep start direction) directions)

wordToNamedEndpointPath :
  ∀ {n} (start finish : Periodic.PeriodicBlock n)
    (directions : List SignedAxis4) →
  Bond.walk start directions ≡ finish →
  Adjacency.PeriodicPath start finish
wordToNamedEndpointPath start finish directions endpointExact =
  subst
    (Adjacency.PeriodicPath start)
    endpointExact
    (wordToPeriodicPath start directions)

record ConstructedPeriodicContour
    {n : _}
    (start finish : Periodic.PeriodicBlock n) : Set where
  field
    directions : List SignedAxis4
    endpointExact : Bond.walk start directions ≡ finish

  path : Adjacency.PeriodicPath start finish
  path = wordToNamedEndpointPath start finish directions endpointExact

open ConstructedPeriodicContour public

periodicWordPathConstructionLevel : ProofLevel
periodicWordPathConstructionLevel = machineChecked

periodicNamedEndpointPathTransportLevel : ProofLevel
periodicNamedEndpointPathTransportLevel = machineChecked

periodicConstructedContourCarrierLevel : ProofLevel
periodicConstructedContourCarrierLevel = machineChecked
