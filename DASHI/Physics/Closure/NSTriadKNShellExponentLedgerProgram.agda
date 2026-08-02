module DASHI.Physics.Closure.NSTriadKNShellExponentLedgerProgram where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- Venue/year: Grundlehren der mathematischen Wissenschaften 343,
-- Springer, 2011.
-- DOI: 10.1007/978-3-642-16830-7.
-- Uses: Littlewood--Paley support, Bernstein inequalities, paraproducts,
-- remainders, and Fourier multipliers.
-- Relationship: supports the standard shell estimates and finite-overlap
-- mechanisms, not the repository's orbit-specific constants.
--
-- Author: Terence Tao.
-- Title: "Lecture Notes 6 for 247B: Paradifferential calculus,
-- fractional chain and Leibnitz rules".
-- Venue/year: UCLA Math 247B lecture notes, Winter 2007.
-- DOI: none; these are course lecture notes.
-- Uses: the high-high/high-low/low-high trichotomy and transpose viewpoint.
-- Relationship: supports the shared three-class frequency combinatorics.
--
-- Author: Jean-Michel Bony.
-- Title: "Calcul symbolique et propagation des singularites pour les
-- equations aux derivees partielles non lineaires".
-- Venue/year: Annales scientifiques de l'Ecole Normale Superieure,
-- Serie 4, 14 (1981), no. 2, 209--246.
-- DOI: 10.24033/asens.1404.
-- Uses: the original paradifferential decomposition principle.
-- Relationship: supports the decomposition principle only.
--
-- Author: Pierre Germain.
-- Title: "Multipliers, paramultipliers, and weak-strong uniqueness for the
-- Navier-Stokes equations".
-- Venue/year: Journal of Differential Equations 226 (2006), 373--428.
-- DOI: 10.1016/j.jde.2005.10.007.
-- Uses: equation (9), the three-term Pi + R + tilde-Pi decomposition;
-- Theorem 3.9, the Sobolev-indexed multiplier/paramultiplier characterization.
-- Relationship: supports the paramultiplier proof strategy and exponent-index
-- bookkeeping.  It does not supply the repository's eight near/far/transition
-- classes or an orbit-transfer Schur theorem.
--
-- Authors: DASHI repository contributors.
-- Title: "Three frozen-leg shell exponent ledgers".
-- Venue/year: DASHI formal development, 2026.
-- DOI: not applicable; near/far/transition/residual subdivisions and their
-- orbit-shell transport are repository-original obligations.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Closure.NSTriadKNTaoFrozenLegParaproductProgram as Tao
import DASHI.Physics.Closure.NSTriadKNFrozenLegDerivativeLerayLedger as Derivative

data SourceAttribution : Set where
  standardLittlewoodPaley
  taoTrichotomy
  bonyParadifferential
  germainParamultiplierLedger
  repositoryOriginalSubdivision : SourceAttribution

data ShellClass : Set where
  lowHigh highLow highHighToLow nearDiagonal
  farLow farHigh transition residual : ShellClass

classAttribution : ShellClass → SourceAttribution
classAttribution lowHigh = taoTrichotomy
classAttribution highLow = taoTrichotomy
classAttribution highHighToLow = taoTrichotomy
classAttribution nearDiagonal = repositoryOriginalSubdivision
classAttribution farLow = repositoryOriginalSubdivision
classAttribution farHigh = repositoryOriginalSubdivision
classAttribution transition = repositoryOriginalSubdivision
classAttribution residual = repositoryOriginalSubdivision

record AttributionReceipt : Set where
  constructor receipt
  field
    lowHighIsTaoTrichotomy : classAttribution lowHigh ≡ taoTrichotomy
    highLowIsTaoTrichotomy : classAttribution highLow ≡ taoTrichotomy
    highHighIsTaoTrichotomy : classAttribution highHighToLow ≡ taoTrichotomy
    nearIsRepositoryOriginal :
      classAttribution nearDiagonal ≡ repositoryOriginalSubdivision
    farLowIsRepositoryOriginal :
      classAttribution farLow ≡ repositoryOriginalSubdivision
    farHighIsRepositoryOriginal :
      classAttribution farHigh ≡ repositoryOriginalSubdivision
    transitionIsRepositoryOriginal :
      classAttribution transition ≡ repositoryOriginalSubdivision
    residualIsRepositoryOriginal :
      classAttribution residual ≡ repositoryOriginalSubdivision

open AttributionReceipt public

attributionReceipt : AttributionReceipt
attributionReceipt = receipt refl refl refl refl refl refl refl refl

record RationalPower : Set where
  constructor power
  field
    negative : Bool
    numerator denominator : Nat

open RationalPower public

zeroPower : RationalPower
zeroPower = power false 0 1

record ShellExponentEntry : Set₁ where
  field
    frozenLeg : Tao.FrozenLeg
    shellClass : ShellClass
    derivativeDescription : Derivative.DerivativeDescription

    leftShellPower rightShellPower outputShellPower : RationalPower
    bernsteinPower cancellationPower orbitMultiplicityPower
      helicityLiftPower : RationalPower

    holderTarget : Derivative.SobolevTarget
    geometricSeriesExponent : RationalPower

    supportOrderingIdentified : Set
    holderAllocationIdentified : Set
    exponentIdentityChecked : Set
    geometricSeriesStrictlyConvergent : Set
    constantIndependentOfCutoff : Set

open ShellExponentEntry public

record FrozenLegShellLedger : Set₁ where
  field
    frozenLeg : Tao.FrozenLeg
    entry : ShellClass → ShellExponentEntry

    lowHighEntryMatchesLeg : Set
    highLowEntryMatchesLeg : Set
    highHighToLowEntryMatchesLeg : Set
    nearEntryMatchesLeg : Set
    farLowEntryMatchesLeg : Set
    farHighEntryMatchesLeg : Set
    transitionEntryMatchesLeg : Set
    residualEntryMatchesLeg : Set

    exactEightClassPartition : Set
    finiteNearOverlap : Set
    transitionAbsorbedWithFixedConstant : Set
    residualAbsorbedWithFixedConstant : Set
    allClassSeriesConverge : Set
    ledgerUniformInCutoff : Set

open FrozenLegShellLedger public

record ThreeFrozenLegExponentPackage : Set₁ where
  field
    outputLedger firstAdjointLedger secondAdjointLedger : FrozenLegShellLedger

    sharedIncidenceClassification : Set
    sharedNearFarTransitionPartition : Set

    outputDerivativeLedgerConsumed : Set
    firstAdjointDerivativeLedgerConsumed : Set
    secondAdjointDerivativeLedgerConsumed : Set

    outputHolderAndHolderConjugateClosed : Set
    firstHolderAndHolderConjugateClosed : Set
    secondHolderAndHolderConjugateClosed : Set

    outputAffineConstraintExtracted : Set
    firstAdjointAffineConstraintExtracted : Set
    secondAdjointAffineConstraintExtracted : Set

    allThreeLedgersCutoffUniform : Set

open ThreeFrozenLegExponentPackage public

shellExponentLedgerSurfaceRepresented : Bool
shellExponentLedgerSurfaceRepresented = true

shellExponentLedgerSurfaceRepresentedIsTrue :
  shellExponentLedgerSurfaceRepresented ≡ true
shellExponentLedgerSurfaceRepresentedIsTrue = refl

germainSuppliesEightClassOrbitGeometry : Bool
germainSuppliesEightClassOrbitGeometry = false

germainSuppliesEightClassOrbitGeometryIsFalse :
  germainSuppliesEightClassOrbitGeometry ≡ false
germainSuppliesEightClassOrbitGeometryIsFalse = refl

allThreeNumericExponentLedgersClosed : Bool
allThreeNumericExponentLedgersClosed = false

allThreeNumericExponentLedgersClosedIsFalse :
  allThreeNumericExponentLedgersClosed ≡ false
allThreeNumericExponentLedgersClosedIsFalse = refl
