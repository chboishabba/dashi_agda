module DASHI.Biology.NeurochemicalVocabularyReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Core.AdapterCanonicalityCore as AdapterCanonicality
import DASHI.Core.AuthorityNonPromotionCore as AuthorityNonPromotionCore
import DASHI.Core.CandidateOnlyCore as CandidateOnlyCore

------------------------------------------------------------------------
-- Neurochemical vocabulary rows.

neurochemicalNamedCandidateRow :
  String → String → String → CandidateOnlyCore.CandidateOnlyRow
neurochemicalNamedCandidateRow name statement remainingGap =
  CandidateOnlyCore.mkCandidateOnlyRow
    name
    "DASHI.Biology.NeurochemicalVocabularyReceipt"
    name
    (CandidateOnlyCore.namedCandidateKind name)
    (CandidateOnlyCore.namedCandidateOnlyStatus name)
    statement
    remainingGap

neurochemicalNamedCandidateReceipt :
  (row : CandidateOnlyCore.CandidateOnlyRow) →
  CandidateOnlyCore.candidateOnly row ≡ true →
  CandidateOnlyCore.promoted row ≡ false →
  CandidateOnlyCore.carriesTruthAuthority row ≡ false →
  CandidateOnlyCore.carriesSupportAuthority row ≡ false →
  CandidateOnlyCore.carriesAdmissibilityAuthority row ≡ false →
  CandidateOnlyCore.carriesTradingAuthority row ≡ false →
  CandidateOnlyCore.carriesRuntimeAuthority row ≡ false →
  CandidateOnlyCore.carriesTheoremAuthority row ≡ false →
  CandidateOnlyCore.CandidateOnlyReceipt row
neurochemicalNamedCandidateReceipt
  row
  candidateProof
  promotedProof
  truthProof
  supportProof
  admissibilityProof
  tradingProof
  runtimeProof
  theoremProof =
  CandidateOnlyCore.mkCandidateOnlyReceipt
    row
    candidateProof
    promotedProof
    truthProof
    supportProof
    admissibilityProof
    tradingProof
    runtimeProof
    theoremProof

------------------------------------------------------------------------
-- Named neurochemical candidates.

glutamateCandidate : CandidateOnlyCore.CandidateOnlyRow
glutamateCandidate =
  neurochemicalNamedCandidateRow
    "glutamate"
    "glutamate is an excitatory transmitter candidate in this local vocabulary."
    "Candidate-only boundary: receptor composition, ionotropic/metabotropic partition, and synapse-level transport law are not yet admitted."

glutamateCandidateReceipt :
  CandidateOnlyCore.CandidateOnlyReceipt glutamateCandidate
glutamateCandidateReceipt =
  neurochemicalNamedCandidateReceipt glutamateCandidate refl refl refl refl refl refl refl refl

gabaCandidate : CandidateOnlyCore.CandidateOnlyRow
gabaCandidate =
  neurochemicalNamedCandidateRow
    "GABA"
    "GABA is represented as an inhibitory neurotransmitter candidate."
    "Folk claim blocked: GABA is not equivalent to calm. This candidate only states presence and requires receptor/target authority context."

gabaCandidateReceipt : CandidateOnlyCore.CandidateOnlyReceipt gabaCandidate
gabaCandidateReceipt =
  neurochemicalNamedCandidateReceipt gabaCandidate refl refl refl refl refl refl refl refl

dopamineCandidate : CandidateOnlyCore.CandidateOnlyRow
dopamineCandidate =
  neurochemicalNamedCandidateRow
    "dopamine"
    "dopamine is a catecholamine neurotransmitter candidate."
    "Folk claim blocked: dopamine is not the same thing as reward. Motivation claims are left to downstream authority and behavioral bridge proofs."

dopamineCandidateReceipt : CandidateOnlyCore.CandidateOnlyReceipt dopamineCandidate
dopamineCandidateReceipt =
  neurochemicalNamedCandidateReceipt dopamineCandidate refl refl refl refl refl refl refl refl

serotoninCandidate : CandidateOnlyCore.CandidateOnlyRow
serotoninCandidate =
  neurochemicalNamedCandidateRow
    "serotonin"
    "serotonin is a monoamine neurotransmitter candidate."
    "Folk claim blocked: serotonin is not identical to mood. Affinity and phenotype coupling are out-of-scope for this candidate row."

serotoninCandidateReceipt : CandidateOnlyCore.CandidateOnlyReceipt serotoninCandidate
serotoninCandidateReceipt =
  neurochemicalNamedCandidateReceipt serotoninCandidate refl refl refl refl refl refl refl refl

norepinephrineCandidate : CandidateOnlyCore.CandidateOnlyRow
norepinephrineCandidate =
  neurochemicalNamedCandidateRow
    "norepinephrine"
    "norepinephrine is an arousal-linked catecholamine candidate in this vocabulary."
    "Candidate-only surface. Adverse effect profile, receptor bias, and stress-domain validation are uncommitted."

norepinephrineCandidateReceipt : CandidateOnlyCore.CandidateOnlyReceipt norepinephrineCandidate
norepinephrineCandidateReceipt =
  neurochemicalNamedCandidateReceipt norepinephrineCandidate refl refl refl refl refl refl refl refl

acetylcholineCandidate : CandidateOnlyCore.CandidateOnlyRow
acetylcholineCandidate =
  neurochemicalNamedCandidateRow
    "acetylcholine"
    "acetylcholine is represented as a candidate neuromodulator/transmitter term."
    "Boundary-only claim: peripheral versus central source splits and receptor subtype gating are not promoted by this row."

acetylcholineCandidateReceipt : CandidateOnlyCore.CandidateOnlyReceipt acetylcholineCandidate
acetylcholineCandidateReceipt =
  neurochemicalNamedCandidateReceipt acetylcholineCandidate refl refl refl refl refl refl refl refl

histamineCandidate : CandidateOnlyCore.CandidateOnlyRow
histamineCandidate =
  neurochemicalNamedCandidateRow
    "histamine"
    "histamine is a candidate mediator with wake-circuit context."
    "Boundary-only candidate: immunological and histamine receptor context remain unbound and unpromoted."

histamineCandidateReceipt : CandidateOnlyCore.CandidateOnlyReceipt histamineCandidate
histamineCandidateReceipt =
  neurochemicalNamedCandidateReceipt histamineCandidate refl refl refl refl refl refl refl refl

glycineCandidate : CandidateOnlyCore.CandidateOnlyRow
glycineCandidate =
  neurochemicalNamedCandidateRow
    "glycine"
    "glycine is included as a candidate co-agonist/transmitter surface."
    "No transport, receptor subtype, or inhibitory balance authority is promoted without external adapters."

glycineCandidateReceipt : CandidateOnlyCore.CandidateOnlyReceipt glycineCandidate
glycineCandidateReceipt =
  neurochemicalNamedCandidateReceipt glycineCandidate refl refl refl refl refl refl refl refl

endocannabinoidCandidate : CandidateOnlyCore.CandidateOnlyRow
endocannabinoidCandidate =
  neurochemicalNamedCandidateRow
    "endocannabinoid"
    "endocannabinoid is a lipid signaling candidate class."
    "No claim is made that this entry alone identifies therapeutic, behavioral, or reward dynamics."

endocannabinoidCandidateReceipt :
  CandidateOnlyCore.CandidateOnlyReceipt endocannabinoidCandidate
endocannabinoidCandidateReceipt =
  neurochemicalNamedCandidateReceipt endocannabinoidCandidate refl refl refl refl refl refl refl refl

neuropeptideCandidate : CandidateOnlyCore.CandidateOnlyRow
neuropeptideCandidate =
  neurochemicalNamedCandidateRow
    "neuropeptide"
    "neuropeptide is tracked as a candidate peptide signaling surface."
    "Binding partner, receptor affinity profile, and secretion-context authority are outside this candidate-only surface."

neuropeptideCandidateReceipt : CandidateOnlyCore.CandidateOnlyReceipt neuropeptideCandidate
neuropeptideCandidateReceipt =
  neurochemicalNamedCandidateReceipt neuropeptideCandidate refl refl refl refl refl refl refl refl

oxytocinCandidate : CandidateOnlyCore.CandidateOnlyRow
oxytocinCandidate =
  neurochemicalNamedCandidateRow
    "oxytocin"
    "oxytocin is a candidate hormone/neuromodulator term."
    "Folk claim blocked: oxytocin is not promoted as love. This candidate requires context receipts for receptor, social attribution, and authority gates."

oxytocinCandidateReceipt : CandidateOnlyCore.CandidateOnlyReceipt oxytocinCandidate
oxytocinCandidateReceipt =
  neurochemicalNamedCandidateReceipt oxytocinCandidate refl refl refl refl refl refl refl refl

cortisolCandidate : CandidateOnlyCore.CandidateOnlyRow
cortisolCandidate =
  neurochemicalNamedCandidateRow
    "cortisol"
    "cortisol is a candidate stress-axis hormone surface."
    "Regulation, circadian phase binding, and receptor/transport context are left as outstanding obligations."

cortisolCandidateReceipt : CandidateOnlyCore.CandidateOnlyReceipt cortisolCandidate
cortisolCandidateReceipt =
  neurochemicalNamedCandidateReceipt cortisolCandidate refl refl refl refl refl refl refl refl

insulinCandidate : CandidateOnlyCore.CandidateOnlyRow
insulinCandidate =
  neurochemicalNamedCandidateRow
    "insulin"
    "insulin is represented as a candidate neurometabolic signaling term."
    "Peripheral versus central axis interpretation and transport-control claims are intentionally not promoted here."

insulinCandidateReceipt : CandidateOnlyCore.CandidateOnlyReceipt insulinCandidate
insulinCandidateReceipt =
  neurochemicalNamedCandidateReceipt insulinCandidate refl refl refl refl refl refl refl refl

------------------------------------------------------------------------
-- Receptor/transporter/enzyme-context candidates.

nmdaReceptorCandidate : CandidateOnlyCore.CandidateOnlyRow
nmdaReceptorCandidate =
  neurochemicalNamedCandidateRow
    "NMDA receptor"
    "NMDA receptor is a candidate ion-channel receptor vocabulary term."
    "No gating model, subunit composition claim, or learning claim is promoted without transport and authority adapters."

nmdaReceptorCandidateReceipt :
  CandidateOnlyCore.CandidateOnlyReceipt nmdaReceptorCandidate
nmdaReceptorCandidateReceipt =
  neurochemicalNamedCandidateReceipt nmdaReceptorCandidate refl refl refl refl refl refl refl refl

ampaReceptorCandidate : CandidateOnlyCore.CandidateOnlyRow
ampaReceptorCandidate =
  neurochemicalNamedCandidateRow
    "AMPA receptor"
    "AMPA receptor is a candidate fast synaptic receptor term."
    "No receptor occupancy, conductance class, or synaptic plasticity authority claim is promoted here."

ampaReceptorCandidateReceipt :
  CandidateOnlyCore.CandidateOnlyReceipt ampaReceptorCandidate
ampaReceptorCandidateReceipt =
  neurochemicalNamedCandidateReceipt ampaReceptorCandidate refl refl refl refl refl refl refl refl

gabaaReceptorCandidate : CandidateOnlyCore.CandidateOnlyRow
gabaaReceptorCandidate =
  neurochemicalNamedCandidateRow
    "GABA_A receptor"
    "GABA_A receptor is a candidate ligand-gated receptor vocabulary entry."
    "No sedative, anxiolytic, or calming equivalence is promoted by this row."

gabaaReceptorCandidateReceipt : CandidateOnlyCore.CandidateOnlyReceipt gabaaReceptorCandidate
gabaaReceptorCandidateReceipt =
  neurochemicalNamedCandidateReceipt gabaaReceptorCandidate refl refl refl refl refl refl refl refl

dopamineTransporterCandidate : CandidateOnlyCore.CandidateOnlyRow
dopamineTransporterCandidate =
  neurochemicalNamedCandidateRow
    "dopamine transporter"
    "dopamine transporter is a candidate clearance-context term."
    "No reuptake-rate claim is promoted; transporter kinetics and localization remain out-of-scope."

dopamineTransporterCandidateReceipt :
  CandidateOnlyCore.CandidateOnlyReceipt dopamineTransporterCandidate
dopamineTransporterCandidateReceipt =
  neurochemicalNamedCandidateReceipt dopamineTransporterCandidate refl refl refl refl refl refl refl refl

serotoninTransporterCandidate : CandidateOnlyCore.CandidateOnlyRow
serotoninTransporterCandidate =
  neurochemicalNamedCandidateRow
    "serotonin transporter"
    "serotonin transporter is a candidate context term for monoamine reuptake."
    "No mood mapping or clinical transporter-efficacy claim is promoted here."

serotoninTransporterCandidateReceipt :
  CandidateOnlyCore.CandidateOnlyReceipt serotoninTransporterCandidate
serotoninTransporterCandidateReceipt =
  neurochemicalNamedCandidateReceipt serotoninTransporterCandidate refl refl refl refl refl refl refl refl

norepinephrineTransporterCandidate : CandidateOnlyCore.CandidateOnlyRow
norepinephrineTransporterCandidate =
  neurochemicalNamedCandidateRow
    "norepinephrine transporter"
    "norepinephrine transporter is a candidate reuptake context surface."
    "No adrenergic signaling strength or stress-threshold interpretation is promoted by this row."

norepinephrineTransporterCandidateReceipt :
  CandidateOnlyCore.CandidateOnlyReceipt norepinephrineTransporterCandidate
norepinephrineTransporterCandidateReceipt =
  neurochemicalNamedCandidateReceipt norepinephrineTransporterCandidate refl refl refl refl refl refl refl refl

maoACandidate : CandidateOnlyCore.CandidateOnlyRow
maoACandidate =
  neurochemicalNamedCandidateRow
    "monoamine oxidase A"
    "monoamine oxidase A is a candidate enzymatic context term."
    "No degradation rate, inhibitor effect, or pathway-closing claim is promoted from this row."

maoACandidateReceipt : CandidateOnlyCore.CandidateOnlyReceipt maoACandidate
maoACandidateReceipt =
  neurochemicalNamedCandidateReceipt maoACandidate refl refl refl refl refl refl refl refl

maoBCandidate : CandidateOnlyCore.CandidateOnlyRow
maoBCandidate =
  neurochemicalNamedCandidateRow
    "monoamine oxidase B"
    "monoamine oxidase B is a candidate enzymatic context term."
    "No kinetic decomposition proof or subtype-specific therapeutic claim is promoted by this surface."

maoBCandidateReceipt : CandidateOnlyCore.CandidateOnlyReceipt maoBCandidate
maoBCandidateReceipt =
  neurochemicalNamedCandidateReceipt maoBCandidate refl refl refl refl refl refl refl refl

comtCandidate : CandidateOnlyCore.CandidateOnlyRow
comtCandidate =
  neurochemicalNamedCandidateRow
    "catechol O methyl transferase"
    "catechol O methyl transferase is a candidate enzyme context entry."
    "No methylation-rate promotion, genotype interpretation, or psychiatric claim is committed here."

comtCandidateReceipt : CandidateOnlyCore.CandidateOnlyReceipt comtCandidate
comtCandidateReceipt =
  neurochemicalNamedCandidateReceipt comtCandidate refl refl refl refl refl refl refl refl

achERaseCandidate : CandidateOnlyCore.CandidateOnlyRow
achERaseCandidate =
  neurochemicalNamedCandidateRow
    "acetylcholinesterase"
    "acetylcholinesterase is a candidate enzymatic context term."
    "Boundary-only candidate surface: synapse-level breakdown and inhibition claims are left unpromoted."

achERaseCandidateReceipt : CandidateOnlyCore.CandidateOnlyReceipt achERaseCandidate
achERaseCandidateReceipt =
  neurochemicalNamedCandidateReceipt achERaseCandidate refl refl refl refl refl refl refl refl

glucocorticoidReceptorCandidate : CandidateOnlyCore.CandidateOnlyRow
glucocorticoidReceptorCandidate =
  neurochemicalNamedCandidateRow
    "glucocorticoid receptor"
    "glucocorticoid receptor is a candidate receptor-context term."
    "No cortisol action, stress-cascade causation, or clinical mapping claim is promoted from this entry."

glucocorticoidReceptorCandidateReceipt :
  CandidateOnlyCore.CandidateOnlyReceipt glucocorticoidReceptorCandidate
glucocorticoidReceptorCandidateReceipt =
  neurochemicalNamedCandidateReceipt glucocorticoidReceptorCandidate refl refl refl refl refl refl refl refl

------------------------------------------------------------------------
-- Canonical list and summary proofs.

canonicalNeurochemicalVocabularyRows : List CandidateOnlyCore.CandidateOnlyRow
canonicalNeurochemicalVocabularyRows =
  glutamateCandidate
  ∷ gabaCandidate
  ∷ dopamineCandidate
  ∷ serotoninCandidate
  ∷ norepinephrineCandidate
  ∷ acetylcholineCandidate
  ∷ histamineCandidate
  ∷ glycineCandidate
  ∷ endocannabinoidCandidate
  ∷ neuropeptideCandidate
  ∷ oxytocinCandidate
  ∷ cortisolCandidate
  ∷ insulinCandidate
  ∷ nmdaReceptorCandidate
  ∷ ampaReceptorCandidate
  ∷ gabaaReceptorCandidate
  ∷ dopamineTransporterCandidate
  ∷ serotoninTransporterCandidate
  ∷ norepinephrineTransporterCandidate
  ∷ maoACandidate
  ∷ maoBCandidate
  ∷ comtCandidate
  ∷ achERaseCandidate
  ∷ glucocorticoidReceptorCandidate
  ∷ []

canonicalNeurochemicalVocabularyRowCount : Nat
canonicalNeurochemicalVocabularyRowCount =
  CandidateOnlyCore.listCount canonicalNeurochemicalVocabularyRows

canonicalNeurochemicalVocabularyRowsCandidateOnly :
  CandidateOnlyCore.AllRowsCandidateOnly canonicalNeurochemicalVocabularyRows
canonicalNeurochemicalVocabularyRowsCandidateOnly =
  CandidateOnlyCore.allRowsCandidateOnlyCons
    (CandidateOnlyCore.candidateOnlyIsTrue glutamateCandidateReceipt)
    (CandidateOnlyCore.allRowsCandidateOnlyCons
      (CandidateOnlyCore.candidateOnlyIsTrue gabaCandidateReceipt)
      (CandidateOnlyCore.allRowsCandidateOnlyCons
        (CandidateOnlyCore.candidateOnlyIsTrue dopamineCandidateReceipt)
        (CandidateOnlyCore.allRowsCandidateOnlyCons
          (CandidateOnlyCore.candidateOnlyIsTrue serotoninCandidateReceipt)
          (CandidateOnlyCore.allRowsCandidateOnlyCons
            (CandidateOnlyCore.candidateOnlyIsTrue norepinephrineCandidateReceipt)
            (CandidateOnlyCore.allRowsCandidateOnlyCons
              (CandidateOnlyCore.candidateOnlyIsTrue acetylcholineCandidateReceipt)
              (CandidateOnlyCore.allRowsCandidateOnlyCons
                (CandidateOnlyCore.candidateOnlyIsTrue histamineCandidateReceipt)
                (CandidateOnlyCore.allRowsCandidateOnlyCons
                  (CandidateOnlyCore.candidateOnlyIsTrue glycineCandidateReceipt)
                  (CandidateOnlyCore.allRowsCandidateOnlyCons
                    (CandidateOnlyCore.candidateOnlyIsTrue endocannabinoidCandidateReceipt)
                    (CandidateOnlyCore.allRowsCandidateOnlyCons
                      (CandidateOnlyCore.candidateOnlyIsTrue neuropeptideCandidateReceipt)
                      (CandidateOnlyCore.allRowsCandidateOnlyCons
                        (CandidateOnlyCore.candidateOnlyIsTrue oxytocinCandidateReceipt)
                        (CandidateOnlyCore.allRowsCandidateOnlyCons
                          (CandidateOnlyCore.candidateOnlyIsTrue cortisolCandidateReceipt)
                          (CandidateOnlyCore.allRowsCandidateOnlyCons
                            (CandidateOnlyCore.candidateOnlyIsTrue insulinCandidateReceipt)
                            (CandidateOnlyCore.allRowsCandidateOnlyCons
                              (CandidateOnlyCore.candidateOnlyIsTrue nmdaReceptorCandidateReceipt)
                              (CandidateOnlyCore.allRowsCandidateOnlyCons
                                (CandidateOnlyCore.candidateOnlyIsTrue ampaReceptorCandidateReceipt)
                                (CandidateOnlyCore.allRowsCandidateOnlyCons
                                  (CandidateOnlyCore.candidateOnlyIsTrue gabaaReceptorCandidateReceipt)
                                  (CandidateOnlyCore.allRowsCandidateOnlyCons
                                    (CandidateOnlyCore.candidateOnlyIsTrue dopamineTransporterCandidateReceipt)
                                    (CandidateOnlyCore.allRowsCandidateOnlyCons
                                      (CandidateOnlyCore.candidateOnlyIsTrue serotoninTransporterCandidateReceipt)
                                      (CandidateOnlyCore.allRowsCandidateOnlyCons
                                        (CandidateOnlyCore.candidateOnlyIsTrue norepinephrineTransporterCandidateReceipt)
                                        (CandidateOnlyCore.allRowsCandidateOnlyCons
                                          (CandidateOnlyCore.candidateOnlyIsTrue maoACandidateReceipt)
                                          (CandidateOnlyCore.allRowsCandidateOnlyCons
                                            (CandidateOnlyCore.candidateOnlyIsTrue maoBCandidateReceipt)
                                            (CandidateOnlyCore.allRowsCandidateOnlyCons
                                              (CandidateOnlyCore.candidateOnlyIsTrue comtCandidateReceipt)
                                              (CandidateOnlyCore.allRowsCandidateOnlyCons
                                                  (CandidateOnlyCore.candidateOnlyIsTrue achERaseCandidateReceipt)
                                                (CandidateOnlyCore.allRowsCandidateOnlyCons
                                                  (CandidateOnlyCore.candidateOnlyIsTrue glucocorticoidReceptorCandidateReceipt)
                                                  CandidateOnlyCore.allRowsCandidateOnlyNil)))))))))))))))))))))))

canonicalNeurochemicalVocabularyRowsPromotedFalse :
  CandidateOnlyCore.AllRowsPromotedFalse canonicalNeurochemicalVocabularyRows
canonicalNeurochemicalVocabularyRowsPromotedFalse =
  CandidateOnlyCore.allRowsPromotedFalseCons
    (CandidateOnlyCore.candidatePromotedIsFalse glutamateCandidateReceipt)
    (CandidateOnlyCore.allRowsPromotedFalseCons
      (CandidateOnlyCore.candidatePromotedIsFalse gabaCandidateReceipt)
      (CandidateOnlyCore.allRowsPromotedFalseCons
        (CandidateOnlyCore.candidatePromotedIsFalse dopamineCandidateReceipt)
        (CandidateOnlyCore.allRowsPromotedFalseCons
          (CandidateOnlyCore.candidatePromotedIsFalse serotoninCandidateReceipt)
          (CandidateOnlyCore.allRowsPromotedFalseCons
            (CandidateOnlyCore.candidatePromotedIsFalse norepinephrineCandidateReceipt)
            (CandidateOnlyCore.allRowsPromotedFalseCons
              (CandidateOnlyCore.candidatePromotedIsFalse acetylcholineCandidateReceipt)
              (CandidateOnlyCore.allRowsPromotedFalseCons
                (CandidateOnlyCore.candidatePromotedIsFalse histamineCandidateReceipt)
                (CandidateOnlyCore.allRowsPromotedFalseCons
                  (CandidateOnlyCore.candidatePromotedIsFalse glycineCandidateReceipt)
                  (CandidateOnlyCore.allRowsPromotedFalseCons
                    (CandidateOnlyCore.candidatePromotedIsFalse endocannabinoidCandidateReceipt)
                    (CandidateOnlyCore.allRowsPromotedFalseCons
                      (CandidateOnlyCore.candidatePromotedIsFalse neuropeptideCandidateReceipt)
                      (CandidateOnlyCore.allRowsPromotedFalseCons
                        (CandidateOnlyCore.candidatePromotedIsFalse oxytocinCandidateReceipt)
                        (CandidateOnlyCore.allRowsPromotedFalseCons
                          (CandidateOnlyCore.candidatePromotedIsFalse cortisolCandidateReceipt)
                          (CandidateOnlyCore.allRowsPromotedFalseCons
                            (CandidateOnlyCore.candidatePromotedIsFalse insulinCandidateReceipt)
                            (CandidateOnlyCore.allRowsPromotedFalseCons
                              (CandidateOnlyCore.candidatePromotedIsFalse nmdaReceptorCandidateReceipt)
                              (CandidateOnlyCore.allRowsPromotedFalseCons
                                (CandidateOnlyCore.candidatePromotedIsFalse ampaReceptorCandidateReceipt)
                                (CandidateOnlyCore.allRowsPromotedFalseCons
                                  (CandidateOnlyCore.candidatePromotedIsFalse gabaaReceptorCandidateReceipt)
                                  (CandidateOnlyCore.allRowsPromotedFalseCons
                                    (CandidateOnlyCore.candidatePromotedIsFalse dopamineTransporterCandidateReceipt)
                                    (CandidateOnlyCore.allRowsPromotedFalseCons
                                      (CandidateOnlyCore.candidatePromotedIsFalse serotoninTransporterCandidateReceipt)
                                      (CandidateOnlyCore.allRowsPromotedFalseCons
                                        (CandidateOnlyCore.candidatePromotedIsFalse norepinephrineTransporterCandidateReceipt)
                                        (CandidateOnlyCore.allRowsPromotedFalseCons
                                          (CandidateOnlyCore.candidatePromotedIsFalse maoACandidateReceipt)
                                          (CandidateOnlyCore.allRowsPromotedFalseCons
                                            (CandidateOnlyCore.candidatePromotedIsFalse maoBCandidateReceipt)
                                            (CandidateOnlyCore.allRowsPromotedFalseCons
                                              (CandidateOnlyCore.candidatePromotedIsFalse comtCandidateReceipt)
                                              (CandidateOnlyCore.allRowsPromotedFalseCons
                                                  (CandidateOnlyCore.candidatePromotedIsFalse achERaseCandidateReceipt)
                                                (CandidateOnlyCore.allRowsPromotedFalseCons
                                                  (CandidateOnlyCore.candidatePromotedIsFalse glucocorticoidReceptorCandidateReceipt)
                                                  CandidateOnlyCore.allRowsPromotedFalseNil)))))))))))))))))))))))

------------------------------------------------------------------------
-- Authority non-promotion bundle and adapter evidence.

neurochemicalAuthorityBundle :
  AuthorityNonPromotionCore.AuthorityNonPromotionBundle
neurochemicalAuthorityBundle =
  AuthorityNonPromotionCore.mkClosedAuthorityNonPromotionBundle
    "neurochemical vocabulary authority non-promotion bundle"

neurochemicalAuthorityBundleKindsFalse :
  AuthorityNonPromotionCore.AllAuthorityKindsFalse
    neurochemicalAuthorityBundle
    AuthorityNonPromotionCore.canonicalAuthorityKinds
neurochemicalAuthorityBundleKindsFalse =
  AuthorityNonPromotionCore.proveAllAuthorityKindsFalse
    neurochemicalAuthorityBundle
    AuthorityNonPromotionCore.canonicalAuthorityKinds

neurochemicalAuthorityBundlePromotesAnyAuthorityFalse :
  AuthorityNonPromotionCore.promotesAnyAuthority
    neurochemicalAuthorityBundle
  ≡
  false
neurochemicalAuthorityBundlePromotesAnyAuthorityFalse =
  AuthorityNonPromotionCore.bundlePromotesAnyAuthorityIsFalse neurochemicalAuthorityBundle

neurochemicalCandidateAdapter :
  AdapterCanonicality.AdapterCanonicalityReceipt
    CandidateOnlyCore.CandidateOnlyRow
    glutamateCandidate
neurochemicalCandidateAdapter =
  AdapterCanonicality.mkCanonicalAdapterReceipt
    "neurochemical candidate adapter"
    "DASHI.Biology.NeurochemicalVocabularyReceipt"
    "glutamateCandidate"
    (AdapterCanonicality.namedAdapterKind "neurochemical vocabulary candidate")
    glutamateCandidate

neurochemicalCandidateAdapterCanonical :
  AdapterCanonicality.adapter neurochemicalCandidateAdapter ≡ glutamateCandidate
neurochemicalCandidateAdapterCanonical =
  AdapterCanonicality.adapterCanonical neurochemicalCandidateAdapter

neurochemicalCandidateAdapterNoAuthorityPromotion :
  AdapterCanonicality.adapterPromotesAuthority neurochemicalCandidateAdapter ≡ false
neurochemicalCandidateAdapterNoAuthorityPromotion =
  AdapterCanonicality.adapterAuthorityPromotionFalse neurochemicalCandidateAdapter

neurochemicalAuthorityBundleAdapter :
  AdapterCanonicality.AdapterCanonicalityReceipt
    AuthorityNonPromotionCore.AuthorityNonPromotionBundle
    neurochemicalAuthorityBundle
neurochemicalAuthorityBundleAdapter =
  AdapterCanonicality.mkCanonicalAdapterReceipt
    "neurochemical authority non-promotion bundle adapter"
    "DASHI.Biology.NeurochemicalVocabularyReceipt"
    "neurochemicalAuthorityBundle"
    (AdapterCanonicality.namedAdapterKind "neurochemical authority non-promotion")
    neurochemicalAuthorityBundle

neurochemicalAuthorityBundleAdapterCanonical :
  AdapterCanonicality.adapter neurochemicalAuthorityBundleAdapter ≡ neurochemicalAuthorityBundle
neurochemicalAuthorityBundleAdapterCanonical =
  AdapterCanonicality.adapterCanonical neurochemicalAuthorityBundleAdapter

neurochemicalAuthorityBundleAdapterNoAuthorityPromotion :
  AdapterCanonicality.adapterPromotesAuthority neurochemicalAuthorityBundleAdapter ≡ false
neurochemicalAuthorityBundleAdapterNoAuthorityPromotion =
  AdapterCanonicality.adapterAuthorityPromotionFalse neurochemicalAuthorityBundleAdapter
