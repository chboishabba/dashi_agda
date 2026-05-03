module DASHI.CurrentBlockageBreakBundle where

open import Agda.Primitive using (Setω)

import DASHI.Physics.Closure.ChemistryRightLimitsBlockageBroken as Chemistry
import DASHI.Physics.Closure.CanonicalToNoncanonicalMdlBranchResolved as MDL
import Ontology.BrainDNA.BrainDNACrossoverBridgePressureResolved as BrainDNA
import Ontology.Brain.BrainSideLocalTheoremLane as Brain
import Ontology.DNA.DNAFirstLocalProgramBundle as DNA

------------------------------------------------------------------------
-- Current blockage break bundle.
--
-- This is the drop-in owner that gathers the non-fancy resolutions:
--   * chemistry blocker discharged by new quotient observable + coupling;
--   * MDL blocker resolved by branch classification + no-global theorem;
--   * Brain-DNA crossover turned into storage/channel bridge pressure;
--   * brain-side lane localized as a theorem-thin local lane;
--   * DNA-first lane localized as a real adjacent formal program.

record CurrentBlockageBreakBundle : Setω where
  field
    chemistry : Chemistry.ChemistryRightLimitsBlockageBroken
    mdl : MDL.CanonicalToNoncanonicalMdlBranchResolved
    brainDNA : BrainDNA.BrainDNACrossoverBridgePressureResolved
    brain : Brain.BrainSideLocalTheoremLane
    dna : DNA.DNAFirstLocalProgramBundle

currentBlockageBreakBundle : CurrentBlockageBreakBundle
currentBlockageBreakBundle = record
  { chemistry = Chemistry.canonicalChemistryRightLimitsBlockageBroken
  ; mdl = MDL.canonicalToNoncanonicalMdlBranchResolved
  ; brainDNA = BrainDNA.brainDNACrossoverBridgePressureResolved
  ; brain = Brain.brainSideLocalTheoremLane
  ; dna = DNA.DNAFirstLocalProgram
  }
