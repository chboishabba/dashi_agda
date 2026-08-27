module DASHI.Biology.EmbodiedInteroceptionSourceRegistry where

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- EMBODIED INTEROCEPTION / ALLOSTASIS SOURCE REGISTRY
--
-- These sources calibrate the biological neighbourhood for the exact finite
-- body-state/interoception/access constructions in DASHI.  They are not proof
-- authority for a live person's physiology, diagnosis, emotion, or treatment.
------------------------------------------------------------------------

record EmbodiedSource : Set where
  constructor embodiedSource
  field
    authors : String
    title : String
    year : Nat
    doi : String
    role : String

open EmbodiedSource public

craig2009 : EmbodiedSource
craig2009 = embodiedSource
  "A. D. (Bud) Craig"
  "How do you feel -- now? The anterior insula and human awareness"
  2009
  "10.1038/nrn2555"
  "ascending interoceptive representation and anterior-insula re-representation"

seth2013 : EmbodiedSource
seth2013 = embodiedSource
  "Anil K. Seth"
  "Interoceptive inference, emotion, and the embodied self"
  2013
  "10.1016/j.tics.2013.09.007"
  "felt state as inference on causes of interoceptive afference rather than a raw body readout"

sethTsakiris2018 : EmbodiedSource
sethTsakiris2018 = embodiedSource
  "Anil K. Seth; Manos Tsakiris"
  "Being a Beast Machine: The Somatic Basis of Selfhood"
  2018
  "10.1016/j.tics.2018.08.008"
  "control-oriented predictive regulation/allostasis as a basis for embodied selfhood"

mcewen1998 : EmbodiedSource
mcewen1998 = embodiedSource
  "Bruce S. McEwen"
  "Stress, Adaptation, and Disease: Allostasis and Allostatic Load"
  1998
  "10.1111/j.1749-6632.1998.tb09546.x"
  "multisystem allostasis/allostatic load; stress physiology is not one scalar mediator"

mcewen2017 : EmbodiedSource
mcewen2017 = embodiedSource
  "Bruce S. McEwen"
  "Neurobiological and Systemic Effects of Chronic Stress"
  2017
  "10.1177/2470547017692328"
  "brain-mediated neuroendocrine/autonomic/immune/metabolic adaptation with nonlinear and time-dependent effects"

ganzelMorrisWethington2010 : EmbodiedSource
ganzelMorrisWethington2010 = embodiedSource
  "Barbara L. Ganzel; Pamela A. Morris; Elaine Wethington"
  "Allostasis and the human brain: Integrating models of stress from the social and life sciences"
  2010
  "10.1037/a0017773"
  "brain as dynamically adapting interface between environmental context and biological self"

xiaMaheuKaneScott2026 : EmbodiedSource
xiaMaheuKaneScott2026 = embodiedSource
  "Hongjie Xia; Maxime Maheu; Gary A. Kane; Benjamin B. Scott"
  "Regulation of the decision threshold by the locus coeruleus"
  2026
  "10.1038/s41386-026-02399-x"
  "cell-type-specific LC-NE manipulation as an empirical controller of decision threshold, not a universal stress law"

astonJonesCohen2005 : EmbodiedSource
astonJonesCohen2005 = embodiedSource
  "Gary Aston-Jones; Jonathan D. Cohen"
  "An Integrative Theory of Locus Coeruleus-Norepinephrine Function: Adaptive Gain and Optimal Performance"
  2005
  "10.1146/annurev.neuro.28.061604.135709"
  "LC-NE adaptive-gain calibration and separation of neuromodulatory state from represented evidence"

kianiShadlen2009 : EmbodiedSource
kianiShadlen2009 = embodiedSource
  "Roozbeh Kiani; Michael N. Shadlen"
  "Representation of Confidence Associated with a Decision by Neurons in the Parietal Cortex"
  2009
  "10.1126/science.1169405"
  "decision confidence/certainty as an additional readout rather than commitment identity"

canonicalEmbodiedSourceCount : Nat
canonicalEmbodiedSourceCount = 9
