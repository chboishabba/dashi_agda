{-# OPTIONS --safe #-}
module DASHI.Physics.ExoticGravity.LiTorrTheorySourceAcquisitionExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using ([]; _∷_)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Physics.ExoticGravity.LiTorrTheorySourceDiligenceProofSearchExact as Diligence

------------------------------------------------------------------------
-- ACQUIRED THEORY-SOURCE LAYER
--
-- Acquired 2026-10-14.
--
-- Attribution discipline:
--   * APS DOI/abstract pages are the primary publication-authority surfaces;
--   * the 1992 page-image carrier inspected for equations (33)-(35) is a
--     reproduction of the published article, not an authority substitute;
--   * Kowitt 1994 is an independent published critique, not a rewrite of the
--     Li/Torr source and not a theorem that every algebraic equation is false;
--   * citation and carrier inspection do not import scientific proof.
------------------------------------------------------------------------

liTorrPRD1991PrimaryAPS : Source.AttributedSource
liTorrPRD1991PrimaryAPS =
  Source.mkDOISource
    "N. Li; D. G. Torr"
    "Effects of a gravitomagnetic field on pure superconductors"
    "Physical Review D 43, 457"
    "1991"
    "10.1103/PhysRevD.43.457"
    "https://journals.aps.org/prd/abstract/10.1103/PhysRevD.43.457"
    Source.academicArticleSource
    "primary APS source; bounded use here is bibliographic identity plus the abstract-level combined-field attenuation claim"
    Source.publicAttribution

liTorrPRB1992PrimaryAPS : Source.AttributedSource
liTorrPRB1992PrimaryAPS =
  Source.mkDOISource
    "Ning Li; D. G. Torr"
    "Gravitational effects on the magnetic attenuation of superconductors"
    "Physical Review B 46, 5489"
    "1992"
    "10.1103/PhysRevB.46.5489"
    "https://journals.aps.org/prb/abstract/10.1103/PhysRevB.46.5489"
    Source.academicArticleSource
    "primary APS publication identity and abstract-level sigma-mu model claim; exact equation entitlement below additionally requires the inspected published-page reproduction"
    Source.publicAttribution

liTorrPRB1992InspectedReproduction : Source.AttributedSource
liTorrPRB1992InspectedReproduction =
  Source.mkNoDOISource
    "Ning Li; D. G. Torr"
    "Gravitational effects on the magnetic attenuation of superconductors — inspected reproduction"
    "reproduction of Physical Review B 46, 5489-5495"
    "1992"
    "https://unpublished.ca/sites/default/files/letter/263060/Ning%20Li%20Paper1.pdf"
    Source.archivalSource
    "carrier-inspection copy used only to verify printed journal page 5492 and equations (33)-(35); publication identity/authority remains the APS source"
    Source.publicAttribution

kowitt1994PrimaryAPS : Source.AttributedSource
kowitt1994PrimaryAPS =
  Source.mkDOISource
    "Mark Kowitt"
    "Gravitomagnetism and magnetic permeability in superconductors"
    "Physical Review B 49, 704"
    "1994"
    "10.1103/PhysRevB.49.704"
    "https://journals.aps.org/prb/abstract/10.1103/PhysRevB.49.704"
    Source.academicArticleSource
    "independent primary published critique of Li/Torr's permeability interpretation and magnitude estimate; retained as counter-source context, not merged into Li/Torr authorship"
    Source.publicAttribution

liTorrAcquiredTheorySourceAtlas : Source.AttributedSourceAtlas
liTorrAcquiredTheorySourceAtlas =
  Source.mkSourceAtlas
    "Li/Torr acquired theory-source and critique atlas"
    "DASHI.Physics.ExoticGravity.LiTorrTheorySourceAcquisitionExact"
    ( liTorrPRD1991PrimaryAPS
    ∷ liTorrPRB1992PrimaryAPS
    ∷ liTorrPRB1992InspectedReproduction
    ∷ kowitt1994PrimaryAPS
    ∷ [] )
    "bounded source provenance for the 1991 attenuation claim, 1992 equations (33)-(35), and the 1994 Kowitt critique"

reproductionCreatesPublicationAuthority : Bool
reproductionCreatesPublicationAuthority = false

citationImportsScientificProof : Bool
citationImportsScientificProof = false

------------------------------------------------------------------------
-- BOUNDED SOURCE-ENTITLED CLAIM RECEIPTS
------------------------------------------------------------------------

record BoundedSourceClaim : Set where
  constructor bounded-source-claim
  field
    primarySource : Source.AttributedSource
    inspectedCarrier : Source.AttributedSource
    exactLocator : String
    sourceEntitledClaim : String
    claimIsHistoricalPublishedClaim : Bool
    claimIsEstablishedPhysics : Bool

open BoundedSourceClaim public

prd1991AttenuationAcquired : BoundedSourceClaim
prd1991AttenuationAcquired =
  bounded-source-claim
    liTorrPRD1991PrimaryAPS
    liTorrPRD1991PrimaryAPS
    "APS abstract, final attenuation/result sentences"
    "The paper reports that the combined magnetic/gravitomagnetic field coordinate falls exponentially toward zero over a characteristic distance lambda."
    true
    false

prb1992CoupledResponseAcquired : BoundedSourceClaim
prb1992CoupledResponseAcquired =
  bounded-source-claim
    liTorrPRB1992PrimaryAPS
    liTorrPRB1992InspectedReproduction
    "Phys. Rev. B 46, 5492, Eqs. (33)-(35)"
    "Equation (33) uses the combined potential A(k,omega) + (m/q) A_g(k,omega) in the supercurrent; Eqs. (34)-(35) feed that same combined coordinate into the magnetic and gravitomagnetic response equations."
    true
    false

------------------------------------------------------------------------
-- DILIGENCE OVERLAY
--
-- We do not mutate the master candidates.  Instead these exact bounded receipts
-- pay only the source uses actually inspected.  The 1993 microscopic narrative
-- remains open until a full carrier and locator are acquired.
------------------------------------------------------------------------

prd1991CarrierInspectedForAttenuationClaim : Bool
prd1991CarrierInspectedForAttenuationClaim = true

prd1991ExactLocatorKnownForAttenuationClaim : Bool
prd1991ExactLocatorKnownForAttenuationClaim = true

prb1992CarrierInspectedForEquations33To35 : Bool
prb1992CarrierInspectedForEquations33To35 = true

prb1992ExactLocatorKnownForEquations33To35 : Bool
prb1992ExactLocatorKnownForEquations33To35 = true

fopl1993MicroscopicCarrierStillOpen : Bool
fopl1993MicroscopicCarrierStillOpen = true

kowittCritiqueDoesNotRewriteLiTorrSource : Bool
kowittCritiqueDoesNotRewriteLiTorrSource = true

historicalEquationShapeEstablishedPhysics : Bool
historicalEquationShapeEstablishedPhysics = false

record LiTorrAcquiredDiligenceFrontier : Set where
  constructor li-torr-acquired-diligence-frontier
  field
    prd1991AttenuationCarrierOpen : Bool
    prd1991AttenuationLocatorOpen : Bool
    prb1992Eq3335CarrierOpen : Bool
    prb1992Eq3335LocatorOpen : Bool
    fopl1993MicroscopicCarrierOpen : Bool
    critiqueKeptRoleDistinct : Bool
    publishedClaimPromotedToEstablishedPhysics : Bool

canonicalLiTorrAcquiredDiligenceFrontier : LiTorrAcquiredDiligenceFrontier
canonicalLiTorrAcquiredDiligenceFrontier =
  li-torr-acquired-diligence-frontier
    false false false false true true false

-- Cross-check against the old generic residual classifier: this tranche pays
-- bounded source uses, not every possible claim that could be extracted from
-- either paper.
oldPRD1991CandidateStillExists : Diligence.LiTorrTheorySourceCandidate
oldPRD1991CandidateStillExists = Diligence.prd1991Candidate

oldPRB1992CandidateStillExists : Diligence.LiTorrTheorySourceCandidate
oldPRB1992CandidateStillExists = Diligence.prb1992Candidate
