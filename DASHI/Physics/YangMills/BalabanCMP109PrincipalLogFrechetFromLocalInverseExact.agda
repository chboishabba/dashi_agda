module DASHI.Physics.YangMills.BalabanCMP109PrincipalLogFrechetFromLocalInverseExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer, 2015.
-- DOI: 10.1007/978-3-319-13467-3.
--
-- Jean-Luc Guermond,
-- "Banach and Hilbert Spaces: Linear Mappings", Chapter 7 lecture notes,
-- Texas A&M University, 2017. No DOI recorded.
--
-- DASHI CONTRIBUTION
--
-- Remove the principal-log derivative IDENTIFICATION as a physical input.
-- On a chart where log(exp X)=X exactly, the chain rule and uniqueness of the
-- Frechet derivative force
--
--        D log_{exp Y} o D exp_Y = I.
--
-- If J is any right inverse of D exp_Y, then
--
--        D log_{exp Y} = J
--
-- pointwise.  The proof below uses the repository's actual Frechet derivative,
-- chain-rule and derivative-uniqueness carriers; it does not assume the desired
-- Dlog=inverse-dexp equality.  Thus the remaining CMP109 source work is only
-- (a) instantiate exp/log as the literal SU(2) chart, (b) supply the standard
-- finite-dimensional differentiability witnesses, and (c) identify the printed
-- trivialization/product path.  The inverse-dexp identity itself is a theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Analysis.MarxHigherCalculus as Frechet

record PrincipalLogLocalInverseFrechetData
    {A : Frechet.MarxAlgebra}
    {V : Frechet.Module A}
    (R : Frechet.VectorLittleOStructure A V V) : Set₁ where
  field
    expMap logMap : Frechet.Vector V → Frechet.Vector V
    point : Frechet.Vector V

    expDerivative :
      Frechet.FrechetDerivativeAt R expMap point

    logDerivative :
      Frechet.FrechetDerivativeAt R logMap (expMap point)

    chainRuleData :
      Frechet.FrechetChainRuleData R R R logDerivative expDerivative

    derivativeUniqueness : Frechet.FrechetDerivativeUniqueness R

    -- Exact chart inverse on the selected principal-log domain.
    logAfterExpExact : ∀ value → logMap (expMap value) ≡ value

open PrincipalLogLocalInverseFrechetData public

compositeIdentityDerivative :
  ∀ {A : Frechet.MarxAlgebra}
    {V : Frechet.Module A}
    {R : Frechet.VectorLittleOStructure A V V} →
  (dataSet : PrincipalLogLocalInverseFrechetData R) →
  Frechet.FrechetDerivativeAt R
    (λ value → logMap dataSet (expMap dataSet value))
    (point dataSet)
compositeIdentityDerivative {V = V} {R = R} dataSet = record
  { Frechet.FrechetDerivativeAt.derivative = Frechet.linearIdentity V
  ; Frechet.FrechetDerivativeAt.remainder = λ _ → Frechet.zeroV V
  ; Frechet.FrechetDerivativeAt.expansion = λ increment →
      let
        pointValue = point dataSet
        lhsToIdentity :
          logMap dataSet
            (expMap dataSet (Frechet._+V_ V pointValue increment))
          ≡ Frechet._+V_ V pointValue increment
        lhsToIdentity =
          logAfterExpExact dataSet (Frechet._+V_ V pointValue increment)

        rhsToIdentity :
          Frechet._+V_ V
            (logMap dataSet (expMap dataSet pointValue))
            (Frechet._+V_ V increment (Frechet.zeroV V))
          ≡ Frechet._+V_ V pointValue increment
        rhsToIdentity =
          trans
            (cong
              (λ base →
                Frechet._+V_ V base
                  (Frechet._+V_ V increment (Frechet.zeroV V)))
              (logAfterExpExact dataSet pointValue))
            (cong
              (Frechet._+V_ V pointValue)
              (Frechet.addZeroRightV V increment))
      in
      trans lhsToIdentity (sym rhsToIdentity)
  ; Frechet.FrechetDerivativeAt.remainderLittleO =
      Frechet.zeroLittleO R
  }

chainDerivativeWitness :
  ∀ {A : Frechet.MarxAlgebra}
    {V : Frechet.Module A}
    {R : Frechet.VectorLittleOStructure A V V} →
  (dataSet : PrincipalLogLocalInverseFrechetData R) →
  Frechet.FrechetDerivativeAt R
    (λ value → logMap dataSet (expMap dataSet value))
    (point dataSet)
chainDerivativeWitness dataSet =
  Frechet.frechetChainRule
    (logDerivative dataSet)
    (expDerivative dataSet)
    (chainRuleData dataSet)

logDerivativeAfterExpDerivativeIsIdentity :
  ∀ {A : Frechet.MarxAlgebra}
    {V : Frechet.Module A}
    {R : Frechet.VectorLittleOStructure A V V} →
  (dataSet : PrincipalLogLocalInverseFrechetData R) →
  ∀ direction →
  Frechet.apply
    (Frechet.derivative (logDerivative dataSet))
    (Frechet.apply
      (Frechet.derivative (expDerivative dataSet)) direction)
  ≡ direction
logDerivativeAfterExpDerivativeIsIdentity dataSet direction =
  let
    derivativeEquality :
      Frechet.derivative (chainDerivativeWitness dataSet)
      ≡ Frechet.derivative (compositeIdentityDerivative dataSet)
    derivativeEquality =
      Frechet.frechetDerivativeUnique
        (derivativeUniqueness dataSet)
        (chainDerivativeWitness dataSet)
        (compositeIdentityDerivative dataSet)
  in
  cong (λ linear → Frechet.apply linear direction) derivativeEquality

record SelectedRightInverseDexp
    {A : Frechet.MarxAlgebra}
    {V : Frechet.Module A}
    {R : Frechet.VectorLittleOStructure A V V}
    (dataSet : PrincipalLogLocalInverseFrechetData R) : Set₁ where
  field
    inverseDexp : Frechet.LinearMap A V V

    dexpAfterInverseDexp : ∀ direction →
      Frechet.apply (Frechet.derivative (expDerivative dataSet))
        (Frechet.apply inverseDexp direction)
      ≡ direction

open SelectedRightInverseDexp public

principalLogFrechetEqualsSelectedInverseDexp :
  ∀ {A : Frechet.MarxAlgebra}
    {V : Frechet.Module A}
    {R : Frechet.VectorLittleOStructure A V V}
    (dataSet : PrincipalLogLocalInverseFrechetData R)
    (selected : SelectedRightInverseDexp dataSet) →
  ∀ direction →
  Frechet.apply (Frechet.derivative (logDerivative dataSet)) direction
  ≡ Frechet.apply (inverseDexp selected) direction
principalLogFrechetEqualsSelectedInverseDexp dataSet selected direction =
  trans
    (cong
      (Frechet.apply (Frechet.derivative (logDerivative dataSet)))
      (sym (dexpAfterInverseDexp selected direction)))
    (logDerivativeAfterExpDerivativeIsIdentity dataSet
      (Frechet.apply (inverseDexp selected) direction))

cmp109PrincipalLogCompositeIdentityDerivativeLevel : ProofLevel
cmp109PrincipalLogCompositeIdentityDerivativeLevel = machineChecked

cmp109PrincipalLogFrechetInverseDexpIdentificationLevel : ProofLevel
cmp109PrincipalLogFrechetInverseDexpIdentificationLevel = machineChecked

-- These are standard finite-dimensional chart facts rather than a CMP109
-- physics estimate.  They remain source instantiations until the literal
-- SUNMatrixGeometry/Bishop chart is connected to this Marx calculus carrier.
cmp109LiteralSU2ChartDifferentiabilityInstantiationLevel : ProofLevel
cmp109LiteralSU2ChartDifferentiabilityInstantiationLevel = standardImported

cmp109PrintedTrivializationProductPathInstantiationLevel : ProofLevel
cmp109PrintedTrivializationProductPathInstantiationLevel = conditional
