module DASHI.Visualisation.AttachedVisualisationSourceAtlas where

open import DASHI.Core.Prelude

import DASHI.Physics.Foundations.Round5SourceAtlas as Sources
import DASHI.Physics.Foundations.AttachedFormalismSourceAtlas as Existing

------------------------------------------------------------------------
-- Attributed sources for the cobordism, affine-slice, PCA, activation,
-- quantisation, manifold-search, and graph-layout layers.

milnorMorseSource : Sources.SourceRecord
milnorMorseSource =
  Sources.sourceRecord
    "John Milnor"
    "Morse Theory"
    "Annals of Mathematics Studies 51, Princeton University Press"
    1963
    "10.1515/9781400881802 (digital edition)"
    "Supports handle attachments, critical points, and the distinction between nondegenerate Morse events and degenerate singular presentations."
    "The finite three-saddle carrier is not promoted to a classification of a concrete smooth singularity."

atiyahCobordismSource : Sources.SourceRecord
atiyahCobordismSource = Existing.atiyahTQFTSource

edelmanAriasSmithSource : Sources.SourceRecord
edelmanAriasSmithSource =
  Sources.sourceRecord
    "Alan Edelman; Tomas A. Arias; Steven T. Smith"
    "The Geometry of Algorithms with Orthogonality Constraints"
    "SIAM Journal on Matrix Analysis and Applications"
    1998
    "10.1137/S0895479895290954"
    "Supports Stiefel and Grassmann manifolds as the natural spaces for orthonormal frames and subspaces."
    "The finite Nat-valued plane examples are not promoted to a complete continuous Grassmannian optimiser."

jolliffeCadimaSource : Sources.SourceRecord
jolliffeCadimaSource =
  Sources.sourceRecord
    "Ian T. Jolliffe; Jorge Cadima"
    "Principal Component Analysis: A Review and Recent Developments"
    "Philosophical Transactions of the Royal Society A"
    2016
    "10.1098/rsta.2015.0202"
    "Supports PCA as a variance-maximising linear dimension-reduction method."
    "PCA variance preservation is not identified with semantic colour separation, injectivity, or perceptual uniformity."

hendrycksGimpelSource : Sources.SourceRecord
hendrycksGimpelSource =
  Sources.sourceRecord
    "Dan Hendrycks; Kevin Gimpel"
    "Gaussian Error Linear Units (GELUs)"
    "arXiv"
    2016
    "No DOI assigned; arXiv:1606.08415"
    "Supports the GELU activation x Phi(x) and its signed output behaviour."
    "A raw GELU value is not promoted to a nonnegative probability, mass, ink fraction, or conservative routing weight."

jacobQuantisationSource : Sources.SourceRecord
jacobQuantisationSource =
  Sources.sourceRecord
    "Benoit Jacob; Skirmantas Kligys; Bo Chen; Menglong Zhu; Matthew Tang; Andrew Howard; Hartwig Adam; Dmitry Kalenichenko"
    "Quantization and Training of Neural Networks for Efficient Integer-Arithmetic-Only Inference"
    "2018 IEEE/CVF Conference on Computer Vision and Pattern Recognition"
    2018
    "10.1109/CVPR.2018.00286"
    "Supports explicit low-precision storage, scaling, zero points, and integer accumulation paths."
    "One visually plausible int8 winner is not promoted to ranking fidelity for a float32 search objective."

fruchtermanReingoldSource : Sources.SourceRecord
fruchtermanReingoldSource =
  Sources.sourceRecord
    "Thomas M. J. Fruchterman; Edward M. Reingold"
    "Graph Drawing by Force-Directed Placement"
    "Software: Practice and Experience"
    1991
    "10.1002/spe.4380211102"
    "Supports force-directed graph layout as an explicitly configured optimisation procedure."
    "A different reciprocal-energy objective is not labelled Fruchterman-Reingold, and graph isomorphism does not force identical local optimiser output."

mcInnesUMAPSource : Sources.SourceRecord
mcInnesUMAPSource =
  Sources.sourceRecord
    "Leland McInnes; John Healy; Nathaniel Saul; Lukas Grossberger"
    "UMAP: Uniform Manifold Approximation and Projection"
    "Journal of Open Source Software"
    2018
    "10.21105/joss.00861"
    "Supports nonlinear dimension reduction as a separately parameterised alternative visualisation map."
    "UMAP is not presumed superior to PCA or treated as a geometry-preserving inverse of the source data."

canonicalAttachedVisualisationSources : List Sources.SourceRecord
canonicalAttachedVisualisationSources =
  milnorMorseSource
  ∷ atiyahCobordismSource
  ∷ edelmanAriasSmithSource
  ∷ jolliffeCadimaSource
  ∷ hendrycksGimpelSource
  ∷ jacobQuantisationSource
  ∷ fruchtermanReingoldSource
  ∷ mcInnesUMAPSource
  ∷ []

visualisationSourceCount : List Sources.SourceRecord → Nat
visualisationSourceCount [] = 0
visualisationSourceCount (_ ∷ sources) =
  suc (visualisationSourceCount sources)

canonicalAttachedVisualisationSourceCount : Nat
canonicalAttachedVisualisationSourceCount =
  visualisationSourceCount canonicalAttachedVisualisationSources

canonicalAttachedVisualisationSourceCountIsEight :
  canonicalAttachedVisualisationSourceCount ≡ 8
canonicalAttachedVisualisationSourceCountIsEight = refl
