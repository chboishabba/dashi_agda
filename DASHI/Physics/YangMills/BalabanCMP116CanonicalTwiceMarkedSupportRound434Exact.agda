{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116CanonicalTwiceMarkedSupportRound434Exact where

------------------------------------------------------------------------
-- B / ROUND434: MAKE TWICE-MARKED SUPPORT STRUCTURAL
--
-- A selected differentiated term is represented together with the two literal
-- source-link membership witnesses.  Survival is fibre membership.  Therefore
-- membership -> survival -> both marks is compiler-owned.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (refl)
open import Data.List.Base using (List)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (Σ; _×_; _,_)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.Closure.YMEffectiveActionSupportInterface as Support
import DASHI.Physics.YangMills.YMSupportGraphDistance as Graph
import DASHI.Physics.YangMills.BalabanCMP116SelectedSupportGraphRound416Exact as R416

record TwiceMarkedTerm
    (RawTerm : Set)
    (CarriesLink : RawTerm → Support.Link → Set)
    (left right : Support.Link) : Set where
  constructor twice-marked
  field
    rawTerm : RawTerm
    carriesLeft : CarriesLink rawTerm left
    carriesRight : CarriesLink rawTerm right

open TwiceMarkedTerm public

record CanonicalTwiceMarkedSupport
    (Domain RawTerm : Set)
    (CarriesLink : RawTerm → Support.Link → Set) : Set₁ where
  field
    leftMark rightMark : Support.Link
    termsWithCommonY :
      Domain → List (TwiceMarkedTerm RawTerm CarriesLink leftMark rightMark)

open CanonicalTwiceMarkedSupport public

containsLink :
  ∀ {Domain RawTerm CarriesLink}
    (source : CanonicalTwiceMarkedSupport Domain RawTerm CarriesLink) →
  Domain → Support.Link → Set
containsLink {RawTerm = RawTerm} {CarriesLink = CarriesLink}
    source domain link =
  Σ (TwiceMarkedTerm RawTerm CarriesLink
      (leftMark source) (rightMark source))
    (λ term →
      term ∈ termsWithCommonY source domain
      × CarriesLink (rawTerm term) link)

supportGraph :
  ∀ {Domain RawTerm CarriesLink}
    (source : CanonicalTwiceMarkedSupport Domain RawTerm CarriesLink) →
  R416.SelectedTwoMarkSupportGraph
    Domain
    (TwiceMarkedTerm RawTerm CarriesLink
      (leftMark source) (rightMark source))
supportGraph source = record
  { R416.SelectedTwoMarkSupportGraph.leftMark =
      leftMark source
  ; R416.SelectedTwoMarkSupportGraph.rightMark =
      rightMark source
  ; R416.SelectedTwoMarkSupportGraph.selectedConnectingDistance =
      Graph.ymGraphDist (leftMark source) (rightMark source)
  ; R416.SelectedTwoMarkSupportGraph.selectedDistanceIsSupportGraphDistance =
      refl
  ; R416.SelectedTwoMarkSupportGraph.domainTreeDistance =
      λ _ → Graph.ymTreeEdgeCount
  ; R416.SelectedTwoMarkSupportGraph.domainTreeDistanceIsSupportTreeEdgeCount =
      λ _ → refl
  ; R416.SelectedTwoMarkSupportGraph.containsSelectedLink =
      containsLink source
  ; R416.SelectedTwoMarkSupportGraph.selectedDifferentiatedTermSurvives =
      λ domain term → term ∈ termsWithCommonY source domain
  ; R416.SelectedTwoMarkSupportGraph.survivingTermContainsLeftMark =
      λ domain term membership →
        term , (membership , carriesLeft term)
  ; R416.SelectedTwoMarkSupportGraph.survivingTermContainsRightMark =
      λ domain term membership →
        term , (membership , carriesRight term)
  }

selectedMembershipIsSurvival :
  ∀ {Domain RawTerm CarriesLink}
    (source : CanonicalTwiceMarkedSupport Domain RawTerm CarriesLink)
    domain term →
  term ∈ termsWithCommonY source domain →
  R416.selectedDifferentiatedTermSurvives
    (supportGraph source) domain term
selectedMembershipIsSurvival source domain term membership = membership

round434MembershipSurvivalCompilerLevel : ProofLevel
round434MembershipSurvivalCompilerLevel = machineChecked

round434BothMarksCompilerLevel : ProofLevel
round434BothMarksCompilerLevel = machineChecked

round434SupportMetricCompilerLevel : ProofLevel
round434SupportMetricCompilerLevel = machineChecked

-- Remaining B2 source work on this preferred carrier is only to construct the
-- actual selected term values with their two source-link witnesses and show
-- each retained common-Y fibre is nonempty.
literalRound434TwiceMarkedTermConstructionLevel : ProofLevel
literalRound434TwiceMarkedTermConstructionLevel = conditional
