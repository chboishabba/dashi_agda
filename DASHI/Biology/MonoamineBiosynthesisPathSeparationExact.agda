module DASHI.Biology.MonoamineBiosynthesisPathSeparationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Biology.ChegenWalshUndermethylationSourceAtlasExact as Sources

------------------------------------------------------------------------
-- SEROTONIN / DOPAMINE BIOSYNTHESIS VERSUS METHYLTRANSFERASE METABOLISM
------------------------------------------------------------------------

data MonoamineMolecule : Set where
  tryptophan : MonoamineMolecule
  fiveHTP : MonoamineMolecule
  serotonin : MonoamineMolecule
  tyrosine : MonoamineMolecule
  lDOPA : MonoamineMolecule
  dopamine : MonoamineMolecule
  methylatedCatecholProduct : MonoamineMolecule

data MonoamineEnzyme : Set where
  tph : MonoamineEnzyme
  tyrosineHydroxylase : MonoamineEnzyme
  aadc : MonoamineEnzyme
  comt : MonoamineEnzyme

data MonoamineProcessClass : Set where
  serotoninBiosynthesis : MonoamineProcessClass
  dopamineBiosynthesis : MonoamineProcessClass
  catecholMethylationMetabolism : MonoamineProcessClass

record MonoamineEdge : Set where
  constructor monoamineEdge
  field
    substrate : MonoamineMolecule
    product : MonoamineMolecule
    enzyme : MonoamineEnzyme
    process : MonoamineProcessClass
    source : Source.AttributedSource
    reading : String

open MonoamineEdge public

tryptophanTo5HTP : MonoamineEdge
tryptophanTo5HTP =
  monoamineEdge tryptophan fiveHTP tph serotoninBiosynthesis
    Sources.goncalvesEtAl2022
    "Tryptophan hydroxylase converts tryptophan to 5-HTP in animal serotonin biosynthesis."

fiveHTPToSerotonin : MonoamineEdge
fiveHTPToSerotonin =
  monoamineEdge fiveHTP serotonin aadc serotoninBiosynthesis
    Sources.goncalvesEtAl2022
    "Aromatic amino acid decarboxylase converts 5-HTP to serotonin."

tyrosineToLDOPA : MonoamineEdge
tyrosineToLDOPA =
  monoamineEdge tyrosine lDOPA tyrosineHydroxylase dopamineBiosynthesis
    Sources.daubnerLeWang2011
    "Tyrosine hydroxylase converts tyrosine to L-DOPA and is rate-limiting for catecholamine synthesis."

lDOPAToDopamine : MonoamineEdge
lDOPAToDopamine =
  monoamineEdge lDOPA dopamine aadc dopamineBiosynthesis
    Sources.daubnerLeWang2011
    "Aromatic amino acid decarboxylase converts L-DOPA to dopamine."

canonicalMonoamineBiosynthesisEdges : List MonoamineEdge
canonicalMonoamineBiosynthesisEdges =
  tryptophanTo5HTP
  ∷ fiveHTPToSerotonin
  ∷ tyrosineToLDOPA
  ∷ lDOPAToDopamine
  ∷ []

data COMTIsSerotoninBiosynthesis : Set where
data COMTIsDopamineBiosynthesis : Set where
data SAMEqualsMonoamineBiosyntheticSubstrate : Set where
data MethyltransferaseFluxDeterminesMonoamineSynthesisRate : Set where

comtNotSerotoninBiosynthesis :
  COMTIsSerotoninBiosynthesis → ⊥
comtNotSerotoninBiosynthesis ()

comtNotDopamineBiosynthesis :
  COMTIsDopamineBiosynthesis → ⊥
comtNotDopamineBiosynthesis ()

samNotDefinitionallyBiosyntheticSubstrate :
  SAMEqualsMonoamineBiosyntheticSubstrate → ⊥
samNotDefinitionallyBiosyntheticSubstrate ()

methyltransferaseFluxDoesNotDefinitionallyDetermineSynthesisRate :
  MethyltransferaseFluxDeterminesMonoamineSynthesisRate → ⊥
methyltransferaseFluxDoesNotDefinitionallyDetermineSynthesisRate ()
