module DASHI.Wikimedia.ScientificCitationQidBindingsExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.ScientificReferenceEntityAtlasExact as Atlas

data CitationDomain : Set where
  yangMills navierStokes riemannHypothesis shared : CitationDomain

record CitationEntityBinding : Set where
  constructor citation-entity-binding
  field
    citationKey : String
    sourceIdentifier : String
    domain : CitationDomain
    relatedEntities : List Atlas.ScientificReferenceEntity
    bindingNote : String
open CitationEntityBinding public

-- Yang-Mills / constructive QFT citation surface.
os1973 : CitationEntityBinding
os1973 = citation-entity-binding "OS1973" "publication identity retained by bibliography; QIDs bind authors only" yangMills
  (Atlas.konradOsterwalder ∷ Atlas.robertSchrader ∷ [])
  "Osterwalder verified; Schrader unresolved; author alignment does not identify either OS paper"

os1975 : CitationEntityBinding
os1975 = citation-entity-binding "OS1975" "publication identity retained by bibliography; QIDs bind authors only" yangMills
  (Atlas.konradOsterwalder ∷ Atlas.robertSchrader ∷ [])
  "same author identities as OS1973; distinct publication remains distinct"

grossWilczek1973 : CitationEntityBinding
grossWilczek1973 = citation-entity-binding "GrossWilczek1973" "published 1973 asymptotic-freedom source" yangMills
  (Atlas.davidGross ∷ Atlas.frankWilczek ∷ [])
  "background source; author QIDs do not pay the finite-gap theorem route"

politzer1973 : CitationEntityBinding
politzer1973 = citation-entity-binding "Politzer1973" "published 1973 asymptotic-freedom source" yangMills
  (Atlas.hughPolitzer ∷ [])
  "background source only"

seiler1982 : CitationEntityBinding
seiler1982 = citation-entity-binding "Seiler1982" "1982 continuum gauge-theory source" yangMills
  (Atlas.erhardSeiler ∷ [])
  "authority-boundary source, not automatic continuum promotion"

balaban1987 : CitationEntityBinding
balaban1987 = citation-entity-binding "Balaban1987" "Bałaban block-spin constructive lattice-gauge source; DOI/bibliography remains primary" yangMills
  (Atlas.tadeuszBalaban ∷ [])
  "person QID deliberately unresolved"

balaban1988 : CitationEntityBinding
balaban1988 = citation-entity-binding "Balaban1988" "Bałaban cluster-expansion source; DOI/bibliography remains primary" yangMills
  (Atlas.tadeuszBalaban ∷ [])
  "person QID deliberately unresolved"

faddeevPopov1967 : CitationEntityBinding
faddeevPopov1967 = citation-entity-binding "FaddeevPopov1967" "doi:10.1016/0370-2693(67)90067-6" yangMills
  (Atlas.ludvigFaddeev ∷ Atlas.victorPopov ∷ Atlas.gaugeFixing ∷ [])
  "DOI is publication identity; people/concept QIDs are related metadata"

federbush1988PhaseCellIV : CitationEntityBinding
federbush1988PhaseCellIV = citation-entity-binding "FederbushPhaseCellIV" "doi:10.1007/BF01225039" yangMills
  (Atlas.paulFederbush ∷ [])
  "publication DOI remains primary"

jaffeWittenClayYM : CitationEntityBinding
jaffeWittenClayYM = citation-entity-binding "JaffeWittenClayYM" "Clay Mathematics Institute Yang-Mills existence and mass gap problem description" yangMills
  (Atlas.arthurJaffe ∷ Atlas.edwardWitten ∷ Atlas.millenniumPrizeProblems ∷ [])
  "author/concept identity only; no QID substitutes for the official Clay problem statement"

-- Navier-Stokes citation surface.
coifmanMeyer : CitationEntityBinding
coifmanMeyer = citation-entity-binding "CoifmanMeyer" "Coifman-Meyer paraproduct theory" navierStokes
  (Atlas.ronaldCoifman ∷ Atlas.yvesMeyer ∷ [])
  "theory-family label; exact paper identity remains citation-specific"

lerayHopf : CitationEntityBinding
lerayHopf = citation-entity-binding "LerayHopf" "Leray-Hopf weak-solution/existence theory" navierStokes
  (Atlas.jeanLeray ∷ Atlas.eberhardHopf ∷ Atlas.navierStokesEquations ∷ [])
  "person/concept metadata only"

bkm : CitationEntityBinding
bkm = citation-entity-binding "BKM" "Beale-Kato-Majda continuation criterion" navierStokes
  (Atlas.jamesBeale ∷ Atlas.tosioKato ∷ Atlas.andrewMajda ∷ [])
  "Kato/Majda verified; Beale remains unresolved"

ckn : CitationEntityBinding
ckn = citation-entity-binding "CKN" "doi:10.1002/cpa.3160350604" navierStokes
  (Atlas.luisCaffarelli ∷ Atlas.robertKohn ∷ Atlas.louisNirenberg ∷ Atlas.navierStokesEquations ∷ [])
  "DOI is the paper identity; Kohn remains unresolved"

leiRenTian2025 : CitationEntityBinding
leiRenTian2025 = citation-entity-binding "LeiRenTian2025" "2025 geometric-obstruction source retained by bibliography" navierStokes
  (Atlas.zhenLei ∷ Atlas.xiaoRen ∷ Atlas.gangTian ∷ Atlas.navierStokesEquations ∷ [])
  "Tian verified; Lei/Ren unresolved"

ess2003 : CitationEntityBinding
ess2003 = citation-entity-binding "ESS2003" "Escauriaza-Seregin-Sverak endpoint regularity source" navierStokes
  (Atlas.luisEscauriaza ∷ Atlas.gregorySeregin ∷ Atlas.vladimirSverak ∷ Atlas.navierStokesEquations ∷ [])
  "Sverak verified; Escauriaza/Seregin unresolved"

-- Riemann / de Bruijn-Newman citation surface.
polymath2019 : CitationEntityBinding
polymath2019 = citation-entity-binding "Polymath2019" "doi:10.1007/s40687-019-0193-1; arXiv:1904.12438" riemannHypothesis
  (Atlas.polymathProject ∷ Atlas.riemannHypothesis ∷ Atlas.bernhardRiemann ∷ Atlas.nicolaasDeBruijn ∷ Atlas.charlesNewman ∷ [])
  "publication identifiers remain primary; project/concepts/persons are related identities"

plattTrudgian2021 : CitationEntityBinding
plattTrudgian2021 = citation-entity-binding "PlattTrudgian2021" "doi:10.1112/blms.12460" riemannHypothesis
  (Atlas.davePlatt ∷ Atlas.timothyTrudgian ∷ Atlas.riemannHypothesis ∷ [])
  "Trudgian verified; Dave Platt deliberately unresolved"

gomila2026Candidate : CitationEntityBinding
gomila2026Candidate = citation-entity-binding "Gomila2026Candidate" "github:judegomila/dbn-lambda-01787854-candidate-audit" riemannHypothesis
  (Atlas.judeGomila ∷ Atlas.riemannHypothesis ∷ Atlas.nicolaasDeBruijn ∷ Atlas.charlesNewman ∷ [])
  "candidate provenance remains non-peer-reviewed; QID alignment creates no publication authority"

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data CitationBindingIsSourceAuthority : Set where
data AuthorIdentityDeterminesPublication : Set where
data SharedPersonQidMakesCitationsSameSource : Set where
data UnresolvedEntityMayBeGuessedFromName : Set where

citationBindingDoesNotCreateSourceAuthority : CitationBindingIsSourceAuthority → ⊥
citationBindingDoesNotCreateSourceAuthority ()
authorIdentityDoesNotDeterminePublication : AuthorIdentityDeterminesPublication → ⊥
authorIdentityDoesNotDeterminePublication ()
sharedAuthorDoesNotCollapseCitations : SharedPersonQidMakesCitationsSameSource → ⊥
sharedAuthorDoesNotCollapseCitations ()
unresolvedEntityCannotBeGuessedFromName : UnresolvedEntityMayBeGuessedFromName → ⊥
unresolvedEntityCannotBeGuessedFromName ()
