module DASHI.Physics.Foundations.AttachedFormalismSourceAtlas where

open import DASHI.Core.Prelude

import DASHI.Physics.Foundations.Round5SourceAtlas as Sources

------------------------------------------------------------------------
-- Sources for the history/filtration, formal-receipt, MDL, cobordism, and
-- Reeb/persistence tranche.  Each record states the imported role and blocks
-- stronger identifications not proved by the finite Agda models.

pearlCausalitySource : Sources.SourceRecord
pearlCausalitySource =
  Sources.sourceRecord
    "Judea Pearl"
    "Causality: Models, Reasoning, and Inference, Second Edition"
    "Cambridge University Press"
    2009
    "10.1017/CBO9780511803161"
    "Supports separating conditioning on boundary information from interventionist causal influence and operational signalling."
    "The finite no-backward-signalling table is not promoted to a complete relativistic causal model."

coverThomasSource : Sources.SourceRecord
coverThomasSource =
  Sources.sourceRecord
    "Thomas M. Cover; Joy A. Thomas"
    "Elements of Information Theory, Second Edition"
    "Wiley-Interscience"
    2006
    "10.1002/047174882X"
    "Supports filtering, smoothing, entropy, channel contraction, and finite description-length comparisons."
    "A finite Nat-valued mass table is not identified with a calibrated probabilistic or quantum field theory."

reebSource : Sources.SourceRecord
reebSource =
  Sources.sourceRecord
    "Georges Reeb"
    "Sur les points singuliers d'une forme de Pfaff completement integrable ou d'une fonction numerique"
    "Comptes Rendus de l'Academie des Sciences de Paris 222"
    1946
    "No DOI assigned; pages 847-849"
    "Supports quotienting connected components of level sets into a graph-like transition skeleton."
    "The finite four-node graph is not promoted to the Reeb graph of an unspecified smooth manifold."

carlssonTopologyDataSource : Sources.SourceRecord
carlssonTopologyDataSource =
  Sources.sourceRecord
    "Gunnar Carlsson"
    "Topology and Data"
    "Bulletin of the American Mathematical Society"
    2009
    "10.1090/S0273-0979-09-01249-X"
    "Supports persistent and multiscale topological summaries of data and filtration-dependent structure."
    "No persistent-homology result is inferred solely from the declared finite Reeb analogue."

atiyahTQFTSource : Sources.SourceRecord
atiyahTQFTSource =
  Sources.sourceRecord
    "Michael F. Atiyah"
    "Topological Quantum Field Theories"
    "Publications Mathematiques de l'IHES"
    1988
    "10.1007/BF02698547"
    "Supports cobordisms and gluing as typed topological transition carriers."
    "A split or merge cobordism is not automatically assigned dialectical or physical dynamics."

gacsTrompVitanyiSource : Sources.SourceRecord
gacsTrompVitanyiSource =
  Sources.sourceRecord
    "Peter Gacs; John Tromp; Paul M. B. Vitanyi"
    "Algorithmic Statistics"
    "IEEE Transactions on Information Theory"
    2001
    "10.1109/18.945257"
    "Supports two-part description length and the separation of model complexity from residual data complexity."
    "The finite model table is not promoted to exact Kolmogorov complexity or a universal physical selection law."

canonicalAttachedFormalismSources : List Sources.SourceRecord
canonicalAttachedFormalismSources =
  pearlCausalitySource
  ∷ coverThomasSource
  ∷ reebSource
  ∷ carlssonTopologyDataSource
  ∷ atiyahTQFTSource
  ∷ gacsTrompVitanyiSource
  ∷ []

attachedSourceCount : List Sources.SourceRecord → Nat
attachedSourceCount [] = 0
attachedSourceCount (_ ∷ sources) = suc (attachedSourceCount sources)

canonicalAttachedFormalismSourceCount : Nat
canonicalAttachedFormalismSourceCount =
  attachedSourceCount canonicalAttachedFormalismSources

canonicalAttachedFormalismSourceCountIsSix :
  canonicalAttachedFormalismSourceCount ≡ 6
canonicalAttachedFormalismSourceCountIsSix = refl
