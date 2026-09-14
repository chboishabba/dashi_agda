module DASHI.Law.SensibLawMaboDenaturalisationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.InstitutionalNormProductionExact as Norm

------------------------------------------------------------------------
-- MABO / DENATURALISATION FIXTURE
--
-- This fixture does not define Indigenous law, sovereignty, historical truth,
-- native-title doctrine as a whole, or moral legitimacy.  It source-binds a
-- narrow High Court proposition useful for the generic naturalisation model:
-- judicial recognition is not the same thing as creation of the underlying
-- rights/interests being recognised.
------------------------------------------------------------------------

maboNo2SourceIdentity : Source.AttributedSource
maboNo2SourceIdentity = Source.mkNoDOISource
  "High Court of Australia"
  "Mabo v Queensland [No 2] [1992] HCA 23; (1992) 175 CLR 1"
  "High Court of Australia / Commonwealth Law Reports"
  "1992"
  "https://www.austlii.edu.au/cgi-bin/viewdoc/au/cases/cth/HCA/1992/23.html"
  (Source.namedSourceKind "court judgment")
  "Identity and primary-authority coordinate for Mabo [No 2]. This atlas entry does not reproduce the whole judgment or promote a secondary paraphrase into the holding."
  Source.publicAttribution

yortaYortaSource : Source.AttributedSource
yortaYortaSource = Source.mkNoDOISource
  "High Court of Australia"
  "Members of the Yorta Yorta Aboriginal Community v Victoria [2002] HCA 58"
  "High Court of Australia"
  "2002"
  "https://www.hcourt.gov.au/sites/default/files/eresources/2002/HCA/58.pdf"
  (Source.namedSourceKind "court judgment")
  "Primary later High Court source stating that native title is not a creature of the common law and that Mabo [No 2] decided that certain rights and interests rooted in traditional law and custom survived the Crown's acquisition of sovereignty and radical title. Used only for that bounded doctrinal proposition."
  Source.publicAttribution

maboDenaturalisationSources : List Source.AttributedSource
maboDenaturalisationSources = maboNo2SourceIdentity ∷ yortaYortaSource ∷ []

maboDenaturalisationSourceAtlas : Source.AttributedSourceAtlas
maboDenaturalisationSourceAtlas = Source.mkSourceAtlas
  "Mabo denaturalisation source atlas"
  "DASHI.Law.SensibLawMaboDenaturalisationExact"
  maboDenaturalisationSources
  "Primary-judgment identity plus later High Court doctrinal statement distinguishing survival/recognition of underlying rights from creation by the common law. No sovereignty, genocide, extinguishment, compensation or historical-equivalence conclusion is promoted."

parentInstitutionalNormProductionBoundary : Norm.InstitutionalNormProductionBoundary
parentInstitutionalNormProductionBoundary = Norm.canonicalInstitutionalNormProductionBoundary

record MaboDenaturalisationBoundary : Set where
  constructor maboDenaturalisationBoundary
  field
    parentInstitutionalNormProductionReused : Bool
    maboNo2IdentityRetained : Bool
    laterHighCourtRecognitionSurvivalStatementPaid : Bool
    judicialRecognitionAutomaticallyCreatesUnderlyingRights : Bool
    priorLegalNonRecognitionAutomaticallyEstablishesUnderlyingNonExistence : Bool
    maboRecognitionAutomaticallyResolvesSovereigntyQuestion : Bool
    maboRecognitionAutomaticallyResolvesExtinguishmentQuestion : Bool
    structuralDenaturalisationAutomaticallyEstablishesCrossHistoricalEquivalence : Bool
    courtCitationAutomaticallyCreatesHistoricalTruthAuthority : Bool

open MaboDenaturalisationBoundary public

canonicalMaboDenaturalisationBoundary : MaboDenaturalisationBoundary
canonicalMaboDenaturalisationBoundary =
  maboDenaturalisationBoundary
    true
    true
    true
    false
    false
    false
    false
    false
    false

------------------------------------------------------------------------
-- Reusable bad-promotion propositions.
------------------------------------------------------------------------

data JudicialRecognitionCreatesUnderlyingRights : Set where
data PriorNonRecognitionEstablishesUnderlyingNonExistence : Set where
data MaboRecognitionResolvesSovereignty : Set where

judicialRecognitionDoesNotCreateUnderlyingRights :
  JudicialRecognitionCreatesUnderlyingRights → ⊥
judicialRecognitionDoesNotCreateUnderlyingRights ()

priorNonRecognitionDoesNotEstablishUnderlyingNonExistence :
  PriorNonRecognitionEstablishesUnderlyingNonExistence → ⊥
priorNonRecognitionDoesNotEstablishUnderlyingNonExistence ()

maboRecognitionDoesNotResolveSovereignty :
  MaboRecognitionResolvesSovereignty → ⊥
maboRecognitionDoesNotResolveSovereignty ()
