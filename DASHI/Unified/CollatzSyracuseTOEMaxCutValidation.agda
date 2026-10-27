module DASHI.Unified.CollatzSyracuseTOEMaxCutValidation where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.EverythingTOESymmetryResolved369 as TOE
import DASHI.Unifier as Unifier
import DASHI.Unified.Everything as Unified
import DASHI.Unified.CollatzSyracuseTOEMaxCutExact as Owner
import DASHI.Analysis.CollatzSyracuseSameObjectMaxCutExact as MaxCut
import DASHI.Analysis.CollatzSyracuseTerminalParityMaxCutExact as Terminal

toeReceiptMatchesOwner :
  TOE.toeCollatzSyracuseMaxCutReceipt
  ≡ Owner.canonicalCollatzSyracuseTOEMaxCutReceipt
toeReceiptMatchesOwner = refl

unifierReceiptMatchesOwner :
  Unifier.unifierCollatzSyracuseMaxCutReceipt
  ≡ Owner.canonicalCollatzSyracuseTOEMaxCutReceipt
unifierReceiptMatchesOwner = refl

unifiedReceiptMatchesOwner :
  Unified.unifiedCollatzSyracuseMaxCutReceipt
  ≡ Owner.canonicalCollatzSyracuseTOEMaxCutReceipt
unifiedReceiptMatchesOwner = refl

toeCylinderForwardPaid :
  MaxCut.cutStatus MaxCut.C3-residueCylinderForward ≡ MaxCut.proved
toeCylinderForwardPaid =
  TOE.toeCollatzCylinderForwardPaid

unifierAffineIteratePaid :
  MaxCut.cutStatus MaxCut.C6-affineIterate ≡ MaxCut.proved
unifierAffineIteratePaid =
  Unifier.unifierCollatzAffineIteratePaid

toeDirectBernoulliPaid :
  MaxCut.cutStatus MaxCut.C12a-directParityBernoulliLaw ≡ MaxCut.proved
toeDirectBernoulliPaid =
  TOE.toeCollatzDirectBernoulliLawPaid

toeTerminalWallStillOpen :
  MaxCut.cutStatus MaxCut.C13d-allStartsStrictDescentProducer
  ≡ MaxCut.sourceSpecificOpen
toeTerminalWallStillOpen =
  TOE.toeCollatzStrictDescentTerminalWallOpen

unifierTerminalWallStillOpen :
  MaxCut.cutStatus MaxCut.C13d-allStartsStrictDescentProducer
  ≡ MaxCut.sourceSpecificOpen
unifierTerminalWallStillOpen =
  Unifier.unifierCollatzStrictDescentTerminalWallOpen

toeFiniteBarrierProducerStillOpen :
  Terminal.TerminalParityMaxCutBoundary.allStartsFiniteBarrierProducerPaid
    Terminal.canonicalTerminalParityMaxCutBoundary
  ≡ 0
toeFiniteBarrierProducerStillOpen =
  TOE.toeCollatzAllStartsFiniteBarrierProducerStillOpen

unifierFiniteSearchDoesNotPromote :
  Terminal.TerminalParityMaxCutBoundary.finiteSearchPromotesUniversalStopping
    Terminal.canonicalTerminalParityMaxCutBoundary
  ≡ 0
unifierFiniteSearchDoesNotPromote =
  Unifier.unifierCollatzFiniteSearchDoesNotPromoteUniversalStopping
