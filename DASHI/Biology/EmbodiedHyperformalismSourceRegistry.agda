module DASHI.Biology.EmbodiedHyperformalismSourceRegistry where

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

record HyperformalismSource : Set where
  constructor hyperformalismSource
  field
    authors : String
    title : String
    year : Nat
    doi : String
    role : String

open HyperformalismSource public

abl1964 : HyperformalismSource
abl1964 = hyperformalismSource
  "Yakir Aharonov; Peter G. Bergmann; Joel L. Lebowitz"
  "Time Symmetry in the Quantum Process of Measurement"
  1964
  "10.1103/PhysRev.134.B1410"
  "two-boundary pre/post-selection precedent; not retrocausal neuroscience"

multitime2009 : HyperformalismSource
multitime2009 = hyperformalismSource
  "Yakir Aharonov; Sandu Popescu; Jeff Tollaksen; Lev Vaidman"
  "Multiple-time states and multiple-time measurements in quantum mechanics"
  2009
  "10.1103/PhysRevA.79.052110"
  "multi-time boundary-constraint precedent"

everett1957 : HyperformalismSource
everett1957 = hyperformalismSource
  "Hugh Everett III"
  "\"Relative State\" Formulation of Quantum Mechanics"
  1957
  "10.1103/RevModPhys.29.454"
  "branching/relative-state interpretive precedent only; no many-worlds biology claim"

gellMannHartle1993 : HyperformalismSource
gellMannHartle1993 = hyperformalismSource
  "Murray Gell-Mann; James B. Hartle"
  "Classical Equations for Quantum Systems"
  1993
  "10.1103/PhysRevD.47.3345"
  "alternative coarse-grained histories/decoherence precedent; not neural quantum dynamics"

arnsten2015 : HyperformalismSource
arnsten2015 = hyperformalismSource
  "Amy F. T. Arnsten"
  "Stress weakens prefrontal networks: molecular insults to higher cognition"
  2015
  "10.1038/nn.4087"
  "stress/catecholamine modulation of prefrontal versus reflexive-control circuitry"

dickersonKemeny2004 : HyperformalismSource
dickersonKemeny2004 = hyperformalismSource
  "Sally S. Dickerson; Margaret E. Kemeny"
  "Acute stressors and cortisol responses: a theoretical integration and synthesis of laboratory research"
  2004
  "10.1037/0033-2909.130.3.355"
  "uncontrollability/social-evaluative threat as HPA-response moderators, rejecting scalar stress assumptions"

canonicalHyperformalismSourceCount : Nat
canonicalHyperformalismSourceCount = 6
