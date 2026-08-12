module DASHI.Physics.Closure.NSTriadKNKernelLiteralizationAuditRound51Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean-Michel Bony.
-- Title: "Calcul symbolique et propagation des singularites pour les
-- equations aux derivees partielles non lineaires".
-- DOI: 10.24033/asens.1404.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- DASHI CONTRIBUTION
--
-- The signed constituent tree currently contains `kernelSource` only as an
-- abstract source atom with owner compatibility `Tax.kernel`.  No literal
-- periodic Navier--Stokes expression is attached to that atom there.  Round 51
-- therefore makes the order of proof obligations explicit:
--
--   literal PDE expression
--     -> exact ownership / duplicate check
--     -> amplitude-frequency-time audit
--     -> zero / Young-soft / hard pre-absorption classification.
--
-- In particular no multidegree or viscosity floor may be assigned before the
-- literal expression exists.  Once it exists there are exactly three legitimate
-- ownership outcomes: independent kernel constituent, exact zero/cancellation,
-- or exact duplication of an already-owned physical term.  The third outcome
-- requires an ownership correction rather than double taxation.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ)

import DASHI.Physics.Closure.NSTriadKNSignedConstituentTreeRound28Exact as Signed
import DASHI.Physics.Closure.NSTriadKNLuoDuplicateFreeTaxOwnershipRound26Exact as Tax

data LiteralKernelOwnershipOutcome : Set where
  independentKernel exactZero duplicateExistingOwner : LiteralKernelOwnershipOutcome

record PhysicalKernelConstituentInstantiation : Set where
  field
    literalKernelContribution : ℚ
    signedKernelConstituent : Signed.SignedConstituent

    sourceIsKernelSource :
      Signed.source signedKernelConstituent ≡ Signed.kernelSource
    ownerIsKernel :
      Signed.assignedOwner signedKernelConstituent ≡ Tax.kernel
    signedContributionIsLiteralKernel :
      Signed.signedContribution signedKernelConstituent
      ≡ literalKernelContribution

    ownershipOutcome : LiteralKernelOwnershipOutcome

open PhysicalKernelConstituentInstantiation public

kernelLiteralizationMustPrecedeTaxClassification : Bool
kernelLiteralizationMustPrecedeTaxClassification = true

physicalKernelConstituentInstantiated : Bool
physicalKernelConstituentInstantiated = false

kernelLiteralizationMustPrecedeTaxClassificationIsTrue :
  kernelLiteralizationMustPrecedeTaxClassification ≡ true
kernelLiteralizationMustPrecedeTaxClassificationIsTrue = refl

physicalKernelConstituentInstantiatedIsFalse :
  physicalKernelConstituentInstantiated ≡ false
physicalKernelConstituentInstantiatedIsFalse = refl
