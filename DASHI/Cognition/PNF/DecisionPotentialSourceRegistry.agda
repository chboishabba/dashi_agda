module DASHI.Cognition.PNF.DecisionPotentialSourceRegistry where

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Decision / potential / order-effect source registry.
--
-- These sources calibrate distinct mathematical/empirical producers.  They
-- are not proof authority for the finite DASHI theorems and are not promoted
-- to one universal theory of decision or cognition.
------------------------------------------------------------------------

record DecisionSource : Set where
  constructor decisionSource
  field
    authors : String
    title : String
    year : Nat
    doi : String
    role : String

open DecisionSource public

busemeyerTownsend1993 : DecisionSource
busemeyerTownsend1993 = decisionSource
  "Jerome R. Busemeyer; James T. Townsend"
  "Decision Field Theory: A Dynamic-Cognitive Approach to Decision Making in an Uncertain Environment"
  1993
  "10.1037/0033-295X.100.3.432"
  "dynamic preference/evidence trajectory rather than static utility readout"

roeBusemeyerTownsend2001 : DecisionSource
roeBusemeyerTownsend2001 = decisionSource
  "Robert M. Roe; Jerome R. Busemeyer; James T. Townsend"
  "Multialternative decision field theory: a dynamic connectionist model of decision making"
  2001
  "10.1037/0033-295X.108.2.370"
  "multialternative lateral competition between simultaneously live candidates"

krajbichArmelRangel2010 : DecisionSource
krajbichArmelRangel2010 = decisionSource
  "Ian Krajbich; Carrie Armel; Antonio Rangel"
  "Visual fixations and the computation and comparison of value in simple choice"
  2010
  "10.1038/nn.2635"
  "attention-gated evidence accumulation"

krajbichRangel2011 : DecisionSource
krajbichRangel2011 = decisionSource
  "Ian Krajbich; Antonio Rangel"
  "Multialternative drift-diffusion model predicts the relationship between visual fixations and choice in value-based decisions"
  2011
  "10.1073/pnas.1101328108"
  "attention-gated accumulation generalized to three competing alternatives"

wang2002 : DecisionSource
wang2002 = decisionSource
  "Xiao-Jing Wang"
  "Probabilistic Decision Making by Slow Reverberation in Cortical Circuits"
  2002
  "10.1016/S0896-6273(02)01092-9"
  "recurrent attractor competition and accumulation-to-commitment dynamics"

wongWang2006 : DecisionSource
wongWang2006 = decisionSource
  "Kong-Fatt Wong; Xiao-Jing Wang"
  "A Recurrent Network Mechanism of Time Integration in Perceptual Decisions"
  2006
  "10.1523/JNEUROSCI.3733-05.2006"
  "low-dimensional recurrent decision dynamics"

wang2008 : DecisionSource
wang2008 = decisionSource
  "Xiao-Jing Wang"
  "Decision Making in Recurrent Neuronal Circuits"
  2008
  "10.1016/j.neuron.2008.09.034"
  "categorical attractor commitment separated from accumulation transients"

manteEtAl2013 : DecisionSource
manteEtAl2013 = decisionSource
  "Valerio Mante; David Sussillo; Krishna V. Shenoy; William T. Newsome"
  "Context-dependent computation by recurrent dynamics in prefrontal cortex"
  2013
  "10.1038/nature12742"
  "context-dependent population geometry without deleting represented inputs"

goldShadlen2007 : DecisionSource
goldShadlen2007 = decisionSource
  "Joshua I. Gold; Michael N. Shadlen"
  "The Neural Basis of Decision Making"
  2007
  "10.1146/annurev.neuro.29.051605.113038"
  "bounded evidence accumulation with deliberation/commitment separation"

hazyFrankOReilly2007 : DecisionSource
hazyFrankOReilly2007 = decisionSource
  "Thomas E. Hazy; Michael J. Frank; Randall C. O'Reilly"
  "Towards an executive without a homunculus: computational models of the prefrontal cortex/basal ganglia system"
  2007
  "10.1098/rstb.2007.2055"
  "downstream Go/NoGo gating of represented actions"

maiaFrank2011 : DecisionSource
maiaFrank2011 = decisionSource
  "Tiago V. Maia; Michael J. Frank"
  "From reinforcement learning models to psychiatric and neurological disorders"
  2011
  "10.1038/nn.2723"
  "dopamine-trained cortico-basal-ganglia action gating and computational-neurology boundary"

bastenEtAl2010 : DecisionSource
bastenEtAl2010 = decisionSource
  "Ulrike Basten; Guido Biele; Hauke R. Heekeren; Christian J. Fiebach"
  "How the brain integrates costs and benefits during decision making"
  2010
  "10.1073/pnas.0908104107"
  "cost-benefit difference representation followed by accumulation"

rolls2019 : DecisionSource
rolls2019 = decisionSource
  "Edmund T. Rolls"
  "Orbitofrontal cortex output pathways: cingulate cortex, basal ganglia, and dopamine"
  2019
  "10.1093/oso/9780198845997.003.0005"
  "value-related OFC output distinguished from downstream action-outcome and striatal pathways"

schultzDayanMontague1997 : DecisionSource
schultzDayanMontague1997 = decisionSource
  "Wolfram Schultz; Peter Dayan; P. Read Montague"
  "A Neural Substrate of Prediction and Reward"
  1997
  "10.1126/science.275.5306.1593"
  "prediction-error learning signal distinguished from current value representation"

pisauroEtAl2017 : DecisionSource
pisauroEtAl2017 = decisionSource
  "M. Andrea Pisauro; Elsa Fouragnan; Chris Retzler; Marios G. Philiastides"
  "Neural correlates of evidence accumulation during value-based decisions revealed via simultaneous EEG-fMRI"
  2017
  "10.1038/ncomms15808"
  "value-based evidence-accumulation signal linked across EEG and fMRI"

dacremontFornariBossaerts2013 : DecisionSource
dacremontFornariBossaerts2013 = decisionSource
  "Mathieu d'Acremont; Eleonora Fornari; Peter Bossaerts"
  "Activity in inferior parietal and medial prefrontal cortex signals the accumulation of evidence in a probability learning task"
  2013
  "10.1371/journal.pcbi.1002895"
  "probability-evidence accumulation empirically separated from value-related activity"

moritoMurata2022 : DecisionSource
moritoMurata2022 = decisionSource
  "Yusuke Morito; Tsutomu Murata"
  "Accumulation System: Distributed Neural Substrates of Perceptual Decision Making Revealed by fMRI Deconvolution"
  2022
  "10.1523/JNEUROSCI.1062-21.2022"
  "distributed accumulation activity with decision-time specialization"

siRoweZhang2021 : DecisionSource
siRoweZhang2021 = decisionSource
  "Ruoguang Si; James B. Rowe; Jiaxiang Zhang"
  "Functional localization and categorization of intentional decisions in humans: A meta-analysis of brain imaging studies"
  2021
  "10.1016/j.neuroimage.2021.118468"
  "intentional choice recruits distributed components with distinct computational roles"

truebloodBusemeyer2011 : DecisionSource
truebloodBusemeyer2011 = decisionSource
  "Jennifer S. Trueblood; Jerome R. Busemeyer"
  "A Quantum Probability Account of Order Effects in Inference"
  2011
  "10.1111/j.1551-6709.2011.01197.x"
  "noncommuting sequential evidence updates"

yearsleyBusemeyer2016 : DecisionSource
yearsleyBusemeyer2016 = decisionSource
  "James M. Yearsley; Jerome R. Busemeyer"
  "Quantum cognition and decision theories: A tutorial"
  2016
  "10.1016/j.jmp.2015.11.005"
  "QQ-equality and quantum-like order-effect model diagnostics"

fuyamaKhrennikovOzawa2025 : DecisionSource
fuyamaKhrennikovOzawa2025 = decisionSource
  "M. Fuyama; A. Khrennikov; M. Ozawa"
  "Quantum-like cognition and decision making in the light of quantum measurement theory"
  2025
  "10.48550/arXiv.2503.05859"
  "separation of observable-noncommutativity from state-update noncommutativity"

friston2010 : DecisionSource
friston2010 = decisionSource
  "Karl Friston"
  "The free-energy principle: a unified brain theory?"
  2010
  "10.1038/nrn2787"
  "single-functional free-energy comparison model; not adopted as DASHI semantics"

pezzuloParrFriston2024 : DecisionSource
pezzuloParrFriston2024 = decisionSource
  "Giovanni Pezzulo; Thomas Parr; Karl Friston"
  "Active inference as a theory of sentient behavior"
  2024
  "10.1016/j.biopsycho.2023.108741"
  "modern active-inference synthesis of prediction, policy optimization and action"

hauserWernerfelt1990 : DecisionSource
hauserWernerfelt1990 = decisionSource
  "John R. Hauser; Birger Wernerfelt"
  "An Evaluation Cost Model of Consideration Sets"
  1990
  "10.1086/209225"
  "cost-bounded live consideration sets"

tverskyKahneman1974 : DecisionSource
tverskyKahneman1974 = decisionSource
  "Amos Tversky; Daniel Kahneman"
  "Judgment under Uncertainty: Heuristics and Biases"
  1974
  "10.1126/science.185.4157.1124"
  "availability/representativeness/anchoring as pre-selection distortions"

mackenzie2014 : DecisionSource
mackenzie2014 = decisionSource
  "Catriona Mackenzie"
  "Three Dimensions of Autonomy: A Relational Analysis"
  2014
  "book DOI 10.1093/acprof:oso/9780199969104.001.0001; no separate chapter DOI asserted"
  "self-governance, self-determination and self-authorization as distinct autonomy dimensions"

canonicalDecisionSourceCount : Nat
canonicalDecisionSourceCount = 26
