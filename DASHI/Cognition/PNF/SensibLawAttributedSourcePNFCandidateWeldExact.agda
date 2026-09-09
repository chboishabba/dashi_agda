module DASHI.Cognition.PNF.SensibLawAttributedSourcePNFCandidateWeldExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Interop.SensibLawResidualLattice as Residual
import DASHI.Cognition.PNF.SensibLawSpacyCompositionOnlySemanticConstitutionExact as Constitution
import DASHI.Cognition.PNF.SensibLawLegalSemanticAdmissionFrontierExact as Admission

------------------------------------------------------------------------
-- ATTRIBUTED SOURCE <-> PNF EMISSION <-> SEMANTIC CANDIDATE WELD
--
-- SemanticCommitmentState stores a SemanticCandidateFibre, while source
-- attribution and PNF emission provenance live on separate carriers.  This
-- receipt explicitly welds them before a source-specific legal state may be
-- assembled.
--
-- The weld is review-authorised because the existing carriers do not carry a
-- definitional equality connecting a parser candidate to a bibliographic source.
-- It therefore records the exact source object, the exact PNF emission, the
-- exact source-span equality and the candidate fibre under one review receipt.
------------------------------------------------------------------------

record AttributedPNFCandidateWeld : Set₁ where
  constructor attributed-pnf-candidate-weld
  field
    attributedSource : Source.AttributedSource
    emission : Residual.PNFEmissionReceipt
    candidateFibre : Constitution.SemanticCandidateFibre
    sourceLocator : String
    emissionSpanMatchesLocator :
      Residual.PNFEmissionReceipt.sourceSpan emission ≡ sourceLocator
    reviewAuthority : Admission.ResolutionAuthority
    reviewReference : String
    candidateSourceRelationship : String
    citationStillDoesNotCreateAuthority :
      Source.citationCreatesAuthority attributedSource ≡ false

open AttributedPNFCandidateWeld public

------------------------------------------------------------------------
-- Boundaries.
------------------------------------------------------------------------

data MatchingSpanCreatesLegalAuthority : Set where
data PNFEmissionAloneIdentifiesAttributedSource : Set where
data CandidateFibreAloneIdentifiesDocument : Set where
data ReviewedWeldProvesSourcePropositionTrue : Set where

data UnrelatedCandidateMayPopulateSourceSpecificState : Set where

matchingSpanDoesNotCreateAuthority : MatchingSpanCreatesLegalAuthority → ⊥
matchingSpanDoesNotCreateAuthority ()

emissionDoesNotIdentifyAttributedSource :
  PNFEmissionAloneIdentifiesAttributedSource → ⊥
emissionDoesNotIdentifyAttributedSource ()

candidateDoesNotIdentifyDocument : CandidateFibreAloneIdentifiesDocument → ⊥
candidateDoesNotIdentifyDocument ()

reviewedWeldDoesNotProveTruth : ReviewedWeldProvesSourcePropositionTrue → ⊥
reviewedWeldDoesNotProveTruth ()

unrelatedCandidateCannotPopulateSourceState :
  UnrelatedCandidateMayPopulateSourceSpecificState → ⊥
unrelatedCandidateCannotPopulateSourceState ()

attributedPNFCandidateWeldReading : String
attributedPNFCandidateWeldReading =
  "A source-specific semantic state must retain an exact AttributedSource, PNF emission/source span and SemanticCandidateFibre under one reviewed weld. Span identity and review preserve provenance but do not create legal authority or world truth."
