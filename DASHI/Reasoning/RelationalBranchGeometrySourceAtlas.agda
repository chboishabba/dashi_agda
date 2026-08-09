module DASHI.Reasoning.RelationalBranchGeometrySourceAtlas where

open import DASHI.Core.Prelude

import DASHI.Core.AttributedSourceCore as Attr

------------------------------------------------------------------------
-- Bounded provenance for the finite pants/cobordism, path-phase, and
-- which-path marker analogies.  These sources motivate vocabulary and exact
-- finite carrier choices; they do not promote the relational model to a
-- physical TQFT or quantum theory.
------------------------------------------------------------------------

atiyahCobordismSource : Attr.AttributedSource
atiyahCobordismSource = Attr.mkDOISource
  "Michael F. Atiyah"
  "Topological quantum field theory"
  "Publications Mathematiques de l'IHES"
  "1988"
  "10.1007/BF02698547"
  "https://doi.org/10.1007/BF02698547"
  Attr.academicArticleSource
  "Supports the bounded language of boundaries, cobordisms, gluing and composition. The implemented carrier is finite and combinatorial; no TQFT functor, smooth manifold theorem, state-space quantisation or physical field theory is imported."
  Attr.publicAttribution

berryGeometricPhaseSource : Attr.AttributedSource
berryGeometricPhaseSource = Attr.mkDOISource
  "Michael Victor Berry"
  "Quantal phase factors accompanying adiabatic changes"
  "Proceedings of the Royal Society of London. A"
  "1984"
  "10.1098/rspa.1984.0023"
  "https://doi.org/10.1098/rspa.1984.0023"
  Attr.academicArticleSource
  "Supports the general distinction between endpoint equality and path-dependent phase under transport. No physical Berry phase, adiabatic Hamiltonian, eigenbundle or empirical psychological phase is asserted."
  Attr.publicAttribution

englertWhichWaySource : Attr.AttributedSource
englertWhichWaySource = Attr.mkDOISource
  "Berthold-Georg Englert"
  "Fringe Visibility and Which-Way Information: An Inequality"
  "Physical Review Letters"
  "1996"
  "10.1103/PhysRevLett.77.2154"
  "https://doi.org/10.1103/PhysRevLett.77.2154"
  Attr.academicArticleSource
  "Supports a bounded analogy between path distinguishability and suppression of interference. The Agda marker relation is a two-state finite accounting device, not a density matrix, laboratory visibility law, or quantum measurement claim."
  Attr.publicAttribution

canonicalBranchGeometrySources : List Attr.AttributedSource
canonicalBranchGeometrySources =
  atiyahCobordismSource
  ∷ berryGeometricPhaseSource
  ∷ englertWhichWaySource
  ∷ []

canonicalBranchGeometrySourceAtlas : Attr.AttributedSourceAtlas
canonicalBranchGeometrySourceAtlas = Attr.mkSourceAtlas
  "finite relational branch geometry sources"
  "DASHI.Reasoning.RelationalBranchGeometrySourceAtlas"
  canonicalBranchGeometrySources
  "Bounded provenance for one-to-n boundary composition, path-sensitive phase, and which-path marker suppression without promoting the finite relational carrier to physical quantum theory."

canonicalBranchGeometrySourceCount : Nat
canonicalBranchGeometrySourceCount =
  Attr.sourceCount canonicalBranchGeometrySources

canonicalBranchGeometrySourceCountIsThree :
  canonicalBranchGeometrySourceCount ≡ 3
canonicalBranchGeometrySourceCountIsThree = refl

canonicalBranchGeometryAtlasDoesNotCreateAuthority :
  Attr.atlasCreatesAuthority canonicalBranchGeometrySourceAtlas ≡ false
canonicalBranchGeometryAtlasDoesNotCreateAuthority =
  Attr.atlasCreatesAuthorityIsFalse canonicalBranchGeometrySourceAtlas
