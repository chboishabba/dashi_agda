module DASHI.Biology.ConsciousAccessNetworkSourceAtlas where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Attributed source atlas for the conscious-access / stateful-network tranche.
--
-- A source row records provenance and the limited bridge role used here.  It
-- does not import the paper's empirical claims as Agda theorems and it does
-- not assign a DOI where none is recorded by this atlas.

data IdentifierKind : Set where
  doiIdentifier : IdentifierKind
  arxivDoiIdentifier : IdentifierKind
  noDoiRecorded : IdentifierKind

data SourceRole : Set where
  articleIntakeRole : SourceRole
  globalWorkspaceRole : SourceRole
  adversarialTheoryTestRole : SourceRole
  singleNeuronTransformRole : SourceRole
  dendriticComputationRole : SourceRole
  multilayerBrainNetworkRole : SourceRole
  psychedelicPriorReweightingRole : SourceRole
  psychedelicEntropyRole : SourceRole
  psychedelicRepertoireRole : SourceRole
  grokkingAnalogyRole : SourceRole
  travelingWaveRole : SourceRole
  spatialWaveControlRole : SourceRole
  ephapticCouplingRole : SourceRole
  analogInterferenceCandidateRole : SourceRole
  anesthesiaPhaseRole : SourceRole
  anesthesiaDynamicsRole : SourceRole

record SourceRecord : Set where
  constructor sourceRecord
  field
    authors : String
    title : String
    publication : String
    year : Nat
    identifierKind : IdentifierKind
    identifier : String
    role : SourceRole
    importedReading : String
    excludedPromotion : String

open SourceRecord public

brooksConversationSource : SourceRecord
brooksConversationSource =
  sourceRecord
    "Samantha Brooks"
    "How your conscious and unconscious mind interact"
    "The Conversation"
    2026
    noDoiRecorded
    "no DOI recorded"
    articleIntakeRole
    "Conscious and nonconscious processes are treated as interacting access regimes rather than separate substances."
    "The article does not establish a complete neural theory or a one-to-one Freud-to-brain map."

mashourWorkspaceSource : SourceRecord
mashourWorkspaceSource =
  sourceRecord
    "George A. Mashour; Pieter Roelfsema; Jean-Pierre Changeux; Stanislas Dehaene"
    "Conscious Processing and the Global Neuronal Workspace Hypothesis"
    "Neuron"
    2020
    doiIdentifier
    "10.1016/j.neuron.2020.01.026"
    globalWorkspaceRole
    "Recurrent widespread availability is used as an access-consciousness hypothesis."
    "Global workspace is not promoted as a complete account of phenomenal consciousness."

cogitateAdversarialSource : SourceRecord
cogitateAdversarialSource =
  sourceRecord
    "Cogitate Consortium; Oscar Ferrante; Urszula Gorska-Klimowska; Simon Henin; Rony Hirschhorn; Aya Khalaf; Alex Lepauvre; Ling Liu; David Richter; Yamil Vidal; and collaborators"
    "Adversarial testing of global neuronal workspace and integrated information theories of consciousness"
    "Nature"
    2025
    doiIdentifier
    "10.1038/s41586-025-08888-1"
    adversarialTheoryTestRole
    "The aggregate keeps multiple consciousness theories under empirical underdetermination."
    "No single temporal or anatomical ignition signature is promoted as settled."

beniaguevNeuronSource : SourceRecord
beniaguevNeuronSource =
  sourceRecord
    "David Beniaguev; Idan Segev; Michael London"
    "Single cortical neurons as deep artificial neural networks"
    "Neuron"
    2021
    doiIdentifier
    "10.1016/j.neuron.2021.07.002"
    singleNeuronTransformRole
    "A neuron is represented as a stateful nonlinear transform rather than a timeless scalar activation."
    "An artificial surrogate is not identified with a complete biological neuron."

londonHausserSource : SourceRecord
londonHausserSource =
  sourceRecord
    "Michael London; Michael Hausser"
    "Dendritic computation"
    "Annual Review of Neuroscience"
    2005
    doiIdentifier
    "10.1146/annurev.neuro.28.061604.135703"
    dendriticComputationRole
    "Dendritic state and location are retained as computation-bearing context."
    "No single dendritic mechanism is promoted as the sole basis of consciousness."

battistonMultilayerSource : SourceRecord
battistonMultilayerSource =
  sourceRecord
    "Federico Battiston; Vincenzo Nicosia; Mario Chavez; Vito Latora"
    "Multilayer motif analysis of brain networks"
    "Chaos"
    2017
    doiIdentifier
    "10.1063/1.4979282"
    multilayerBrainNetworkRole
    "Structural and functional connectivity are retained as interacting but non-identical network layers."
    "A multiplex graph is not promoted as a complete mechanistic explanation of cognition."

rebusSource : SourceRecord
rebusSource =
  sourceRecord
    "Robin L. Carhart-Harris; Karl J. Friston"
    "REBUS and the Anarchic Brain: Toward a Unified Model of the Brain Action of Psychedelics"
    "Pharmacological Reviews"
    2019
    doiIdentifier
    "10.1124/pr.118.017160"
    psychedelicPriorReweightingRole
    "Psychedelic perturbation is represented as candidate relaxation of high-level precision and routing constraints."
    "The model is not promoted as a treatment protocol or universal pharmacological law."

entropicBrainSource : SourceRecord
entropicBrainSource =
  sourceRecord
    "Robin L. Carhart-Harris; Robert Leech; Peter J. Hellyer; Murray Shanahan; Amanda Feilding; Enzo Tagliazucchi; Dante R. Chialvo; David Nutt"
    "The entropic brain: a theory of conscious states informed by neuroimaging research with psychedelic drugs"
    "Frontiers in Human Neuroscience"
    2014
    doiIdentifier
    "10.3389/fnhum.2014.00020"
    psychedelicEntropyRole
    "The tranche records increased repertoire and entropy as candidate dynamical readings."
    "Entropy is not treated as a settled standalone biomarker of consciousness or therapeutic outcome."

tagliazucchiRepertoireSource : SourceRecord
tagliazucchiRepertoireSource =
  sourceRecord
    "Enzo Tagliazucchi; Robin L. Carhart-Harris; Robert Leech; David Nutt; Dante R. Chialvo"
    "Enhanced repertoire of brain dynamical states during the psychedelic experience"
    "Human Brain Mapping"
    2014
    doiIdentifier
    "10.1002/hbm.22562"
    psychedelicRepertoireRole
    "The tranche records a broadened dynamical repertoire as a candidate state-space effect."
    "A broader repertoire is not identified with truth, health, treatment success, or a complete consciousness measure."

grokkingSource : SourceRecord
grokkingSource =
  sourceRecord
    "Alethea Power; Yuri Burda; Harri Edwards; Igor Babuschkin; Vedant Misra"
    "Grokking: Generalization Beyond Overfitting on Small Algorithmic Datasets"
    "arXiv"
    2022
    arxivDoiIdentifier
    "10.48550/arXiv.2201.02177"
    grokkingAnalogyRole
    "Grokking supplies an analogy for learned latent geometry becoming reusable across tasks."
    "Slow parameter-space grokking is not identified with rapid conscious access dynamics."

bhattacharyaTravelingWaveSource : SourceRecord
bhattacharyaTravelingWaveSource =
  sourceRecord
    "Sayak Bhattacharya; Scott L. Brincat; Mikael Lundqvist; Earl K. Miller"
    "Traveling waves in the prefrontal cortex during working memory"
    "PLOS Computational Biology"
    2022
    doiIdentifier
    "10.1371/journal.pcbi.1009827"
    travelingWaveRole
    "Traveling prefrontal waves motivate a spatially moving fast-control producer."
    "Traveling waves are not by themselves promoted to cognition, computation, or consciousness."

lundqvistSpatialComputingSource : SourceRecord
lundqvistSpatialComputingSource =
  sourceRecord
    "Mikael Lundqvist; Scott L. Brincat; Jonas Rose; Melissa R. Warden; Timothy J. Buschman; Earl K. Miller; Pawel Herman"
    "Working memory control dynamics follow principles of spatial computing"
    "Nature Communications"
    2023
    doiIdentifier
    "10.1038/s41467-023-36555-4"
    spatialWaveControlRole
    "Beta/gamma spatial control motivates context-dependent effective topology and item accessibility."
    "The spatial-control model is not promoted as a complete neural or consciousness theory."

pinotsisEphapticSource : SourceRecord
pinotsisEphapticSource =
  sourceRecord
    "Dimitris A. Pinotsis; Earl K. Miller"
    "Ephaptic coupling can explain variability in neural activity"
    "Cerebral Cortex"
    2026
    doiIdentifier
    "10.1093/cercor/bhag098"
    ephapticCouplingRole
    "Mesoscale field-to-neuron coupling motivates a physical route from field state to effective excitability."
    "Observed/modelled ephaptic influence is not promoted to a universal causal controller or clinical mechanism."

millerAnalogCognitionSource : SourceRecord
millerAnalogCognitionSource =
  sourceRecord
    "Earl K. Miller; Scott L. Brincat; Jefferson E. Roy"
    "Analog Cognition and Consciousness"
    "PsyArXiv / Journal of Neuroscience theory lineage"
    2026
    doiIdentifier
    "10.31234/osf.io/z48x7_v3"
    analogInterferenceCandidateRole
    "Wave superposition and traveling control motivate an explicit candidate analog-computation producer beneath access semantics."
    "The theory is not promoted to direct evidence that cortical wave interference computes cognition or establishes phenomenal consciousness."

bardonAnesthesiaPhaseSource : SourceRecord
bardonAnesthesiaPhaseSource =
  sourceRecord
    "Alexandra G. Bardon; Jesus J. Ballesteros; Scott L. Brincat; Jefferson E. Roy; Meredith K. Mahnke; Yumiko Ishizawa; Emery N. Brown; Earl K. Miller"
    "Convergent effects of different anesthetics on changes in phase alignment of cortical oscillations"
    "Cell Reports"
    2025
    doiIdentifier
    "10.1016/j.celrep.2025.115685"
    anesthesiaPhaseRole
    "Cross-drug phase-alignment changes motivate phase organization as an empirical observation axis."
    "A convergent phase signature does not identify a unique molecular cause or prove absence of all experience."

eisenAnesthesiaDynamicsSource : SourceRecord
eisenAnesthesiaDynamicsSource =
  sourceRecord
    "Adam J. Eisen; Alexandra G. Bardon; Jesus J. Ballesteros; Andre M. Bastos; Jacob A. Donoghue; Meredith K. Mahnke; Scott L. Brincat; Jefferson E. Roy; Yumiko Ishizawa; Emery N. Brown; Ila R. Fiete; Earl K. Miller"
    "Similar destabilization of neural dynamics under different general anesthetics"
    "Cell Reports"
    2026
    doiIdentifier
    "10.1016/j.celrep.2026.117048"
    anesthesiaDynamicsRole
    "Cross-drug dynamical destabilization motivates a stability/recovery observation distinct from receptor identity."
    "Dynamical convergence is not promoted to a unique cause, diagnosis, or complete theory of consciousness."

canonicalConsciousAccessSources : List SourceRecord
canonicalConsciousAccessSources =
  brooksConversationSource
  ∷ mashourWorkspaceSource
  ∷ cogitateAdversarialSource
  ∷ beniaguevNeuronSource
  ∷ londonHausserSource
  ∷ battistonMultilayerSource
  ∷ rebusSource
  ∷ entropicBrainSource
  ∷ tagliazucchiRepertoireSource
  ∷ grokkingSource
  ∷ bhattacharyaTravelingWaveSource
  ∷ lundqvistSpatialComputingSource
  ∷ pinotsisEphapticSource
  ∷ millerAnalogCognitionSource
  ∷ bardonAnesthesiaPhaseSource
  ∷ eisenAnesthesiaDynamicsSource
  ∷ []

listCount : ∀ {A : Set} → List A → Nat
listCount [] = zero
listCount (_ ∷ xs) = suc (listCount xs)

canonicalConsciousAccessSourceCount : Nat
canonicalConsciousAccessSourceCount =
  listCount canonicalConsciousAccessSources

canonicalConsciousAccessSourceCountIsSixteen :
  canonicalConsciousAccessSourceCount ≡ 16
canonicalConsciousAccessSourceCountIsSixteen = refl
