module DASHI.Physics.Closure.NSTriadKNLuoPhysicalFiveClassSupportRound25Exact where

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
-- Author: Xiaoyutao Luo.
-- Title: "A Beale-Kato-Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- DASHI CONTRIBUTION
--
-- This file closes the discrete support part of L4 on the repository's literal
-- Z^3 cutoff carrier.  Every actual resonant physical triad is assigned
-- exactly one of LH, HL, HH or CC by the executable shell classifier.  The
-- differentiated commutator is retained as the fifth class Com.  There is no
-- generic remainder constructor.
--
-- A new shell-triangle theorem proves that two inputs cannot both lie three
-- shells below their resonant output.  The proof uses the exact max-norm
-- triangle inequality and the already checked ceil-log shell estimate:
--
--   j_p + 3 <= j_k and j_q + 3 <= j_k
--   contradict j_k <= max(j_p,j_q)+1.
--
-- Low-high, high-low and high-high-to-low certificates also carry the sharper
-- distance-one consequences proved in the literal dyadic geometry module.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Empty using (⊥)
open import Data.Nat.Base using (_≤_; z≤n; s≤s; ∣_-_∣)
import Data.Nat.Properties as Nat
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSPeriodicNearTriadClassification as Near
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNOfficialInfinityNormTriangle as Infinity
import DASHI.Physics.Closure.NSTriadKNLiteralDyadicShellConstants as Shell
import DASHI.Physics.Closure.NSTriadKNLiteralDyadicConsequencesClosed as Dyadic
import DASHI.Physics.Closure.NSTriadKNPhysicalScaleTrichotomy as Scale
import DASHI.Physics.Closure.NSTriadKNLuoFiniteParaproductRangePartitionExact as Range

open Cube using (_∈_)

------------------------------------------------------------------------
-- Boolean strict-order evidence to propositional natural-number order.
------------------------------------------------------------------------

natLessTrueToSuccessorLe :
  ∀ {m n} → Near.natLess m n ≡ true → suc m ≤ n
natLessTrueToSuccessorLe {zero} {zero} ()
natLessTrueToSuccessorLe {zero} {suc n} proof = s≤s z≤n
natLessTrueToSuccessorLe {suc m} {zero} ()
natLessTrueToSuccessorLe {suc m} {suc n} proof =
  s≤s (natLessTrueToSuccessorLe proof)

successorLeImpliesLe :
  ∀ {m n} → suc m ≤ n → m ≤ n
successorLeImpliesLe {zero} proof = z≤n
successorLeImpliesLe {suc m} {zero} ()
successorLeImpliesLe {suc m} {suc n} (s≤s proof) =
  s≤s (successorLeImpliesLe proof)

natLessTrueToLe :
  ∀ {m n} → Near.natLess m n ≡ true → m ≤ n
natLessTrueToLe proof =
  successorLeImpliesLe (natLessTrueToSuccessorLe proof)

------------------------------------------------------------------------
-- New literal shell theorem: low-low cannot generate a far higher output.
------------------------------------------------------------------------

noTwoInputsThreeShellsBelowOutput :
  (τ : Physical.PhysicalTriadIncidence) →
  Shell.shellIndex (Physical.p τ) + Shell.Csep
    ≤ Shell.shellIndex (Physical.k τ) →
  Shell.shellIndex (Physical.q τ) + Shell.Csep
    ≤ Shell.shellIndex (Physical.k τ) →
  ⊥
noTwoInputsThreeShellsBelowOutput τ pGap qGap
  with Nat.≤-total
    (Shell.shellIndex (Physical.p τ))
    (Shell.shellIndex (Physical.q τ))
... | inj₁ pShell≤qShell =
  Dyadic.gapThreeContradictsUpperSuccessor qGap
    (Dyadic.shellOfNormSumUpperRight
      (Infinity.outputTriangle consequences)
      pShell≤qShell)
  where
  consequences : Infinity.OfficialResonantNormConsequences τ
  consequences = Infinity.officialResonantNormConsequences τ
... | inj₂ qShell≤pShell =
  Dyadic.gapThreeContradictsUpperSuccessor pGap
    (Dyadic.shellOfNormSumUpperRight
      (Infinity.outputTriangle consequences)
      qShell≤pShell)
  where
  consequences : Infinity.OfficialResonantNormConsequences τ
  consequences = Infinity.officialResonantNormConsequences τ

------------------------------------------------------------------------
-- Exact four-way classification of literal physical triads.
------------------------------------------------------------------------

data TriadicSourceClass : Set where
  LH HL HH CC : TriadicSourceClass

regimeForClass : TriadicSourceClass → Scale.ScaleRegime
regimeForClass LH = Scale.lowHigh
regimeForClass HL = Scale.highLow
regimeForClass HH = Scale.highHigh
regimeForClass CC = Scale.comparable

classForRegime : Scale.ScaleRegime → TriadicSourceClass
classForRegime Scale.lowHigh = LH
classForRegime Scale.highLow = HL
classForRegime Scale.highHigh = HH
classForRegime Scale.comparable = CC

literalShellPolicy : Scale.PhysicalShellPolicy
literalShellPolicy = Shell.literalDyadicShellPolicy

triadicSourceClass :
  Physical.PhysicalTriadIncidence → TriadicSourceClass
triadicSourceClass τ =
  classForRegime (Scale.classifyScale literalShellPolicy τ)

TriadicClassMeaning :
  Physical.PhysicalTriadIncidence → TriadicSourceClass → Set
TriadicClassMeaning τ source =
  Scale.ScaleCondition literalShellPolicy τ (regimeForClass source)

record TriadicClassCertificate
    (τ : Physical.PhysicalTriadIncidence)
    (source : TriadicSourceClass) : Set where
  constructor triadic-class-certificate
  field
    computedClass : triadicSourceClass τ ≡ source
    classMeaning : TriadicClassMeaning τ source

open TriadicClassCertificate public

classifyPhysicalTriad :
  (τ : Physical.PhysicalTriadIncidence) →
  Σ TriadicSourceClass (λ source → TriadicClassCertificate τ source)
classifyPhysicalTriad τ
  with Scale.classifyScale literalShellPolicy τ
     | Scale.scaleClassificationSound literalShellPolicy τ
... | Scale.lowHigh | evidence =
      LH , triadic-class-certificate refl evidence
... | Scale.highLow | evidence =
      HL , triadic-class-certificate refl evidence
... | Scale.highHigh | evidence =
      HH , triadic-class-certificate refl evidence
... | Scale.comparable | evidence =
      CC , triadic-class-certificate refl evidence

triadicClassificationUnique :
  ∀ {τ first second} →
  TriadicClassCertificate τ first →
  TriadicClassCertificate τ second →
  first ≡ second
triadicClassificationUnique firstCertificate secondCertificate =
  trans
    (sym (computedClass firstCertificate))
    (computedClass secondCertificate)

------------------------------------------------------------------------
-- Quantitative meanings of the three separated classes.
------------------------------------------------------------------------

lowHighWeakGap :
  ∀ {τ} →
  Scale.ScaleCondition literalShellPolicy τ Scale.lowHigh →
  Shell.shellIndex (Physical.p τ) + Shell.Csep
    ≤ Shell.shellIndex (Physical.q τ)
lowHighWeakGap (Scale.lowHighCondition strictGap) =
  natLessTrueToLe strictGap

highLowWeakGap :
  ∀ {τ} →
  Scale.ScaleCondition literalShellPolicy τ Scale.highLow →
  Shell.shellIndex (Physical.q τ) + Shell.Csep
    ≤ Shell.shellIndex (Physical.p τ)
highLowWeakGap (Scale.highLowCondition notLowHigh strictGap) =
  natLessTrueToLe strictGap

highHighWeakGaps :
  ∀ {τ} →
  Scale.ScaleCondition literalShellPolicy τ Scale.highHigh →
  (Shell.shellIndex (Physical.k τ) + Shell.Csep
      ≤ Shell.shellIndex (Physical.p τ))
  ×
  (Shell.shellIndex (Physical.k τ) + Shell.Csep
      ≤ Shell.shellIndex (Physical.q τ))
highHighWeakGaps
  (Scale.highHighCondition notLowHigh notHighLow outputBelowP outputBelowQ) =
  natLessTrueToLe outputBelowP , natLessTrueToLe outputBelowQ

lowHighOutputTracksHighOne :
  ∀ {τ} →
  TriadicClassCertificate τ LH →
  ∣ Shell.shellIndex (Physical.k τ)
    - Shell.shellIndex (Physical.q τ) ∣ ≤ 1
lowHighOutputTracksHighOne certificate =
  Dyadic.lowHighOutputTracksHighOne _
    (lowHighWeakGap (classMeaning certificate))

highLowOutputTracksHighOne :
  ∀ {τ} →
  TriadicClassCertificate τ HL →
  ∣ Shell.shellIndex (Physical.k τ)
    - Shell.shellIndex (Physical.p τ) ∣ ≤ 1
highLowOutputTracksHighOne certificate =
  Dyadic.highLowOutputTracksHighOne _
    (highLowWeakGap (classMeaning certificate))

highHighInputsComparableOne :
  ∀ {τ} →
  TriadicClassCertificate τ HH →
  ∣ Shell.shellIndex (Physical.p τ)
    - Shell.shellIndex (Physical.q τ) ∣ ≤ 1
highHighInputsComparableOne certificate =
  Dyadic.highHighToLowInputsComparableOne _
    (proj₁ gaps)
    (proj₂ gaps)
  where
  gaps = highHighWeakGaps (classMeaning certificate)

------------------------------------------------------------------------
-- Enumeration-wide classification and exact erasure.
------------------------------------------------------------------------

record ClassifiedPhysicalTriad : Set where
  constructor classified-physical-triad
  field
    incidence : Physical.PhysicalTriadIncidence
    sourceClass : TriadicSourceClass
    certificate : TriadicClassCertificate incidence sourceClass

open ClassifiedPhysicalTriad public

classifyOnePhysicalTriad :
  Physical.PhysicalTriadIncidence → ClassifiedPhysicalTriad
classifyOnePhysicalTriad τ with classifyPhysicalTriad τ
... | source , proof = classified-physical-triad τ source proof

classifyPhysicalTriads :
  List Physical.PhysicalTriadIncidence →
  List ClassifiedPhysicalTriad
classifyPhysicalTriads [] = []
classifyPhysicalTriads (τ ∷ rest) =
  classifyOnePhysicalTriad τ ∷ classifyPhysicalTriads rest

eraseClassifiedPhysicalTriad :
  ClassifiedPhysicalTriad → Physical.PhysicalTriadIncidence
eraseClassifiedPhysicalTriad = incidence

eraseClassifiedPhysicalTriads :
  List ClassifiedPhysicalTriad →
  List Physical.PhysicalTriadIncidence
eraseClassifiedPhysicalTriads [] = []
eraseClassifiedPhysicalTriads (τ ∷ rest) =
  incidence τ ∷ eraseClassifiedPhysicalTriads rest

eraseClassifiedPhysicalTriadsExact :
  (triads : List Physical.PhysicalTriadIncidence) →
  eraseClassifiedPhysicalTriads (classifyPhysicalTriads triads)
  ≡ triads
eraseClassifiedPhysicalTriadsExact [] = refl
eraseClassifiedPhysicalTriadsExact (τ ∷ rest)
  rewrite eraseClassifiedPhysicalTriadsExact rest = refl

classifiedPhysicalOutputFiber :
  Nat → Z3.FourierMode → List ClassifiedPhysicalTriad
classifiedPhysicalOutputFiber cutoff output =
  classifyPhysicalTriads (Output.physicalOutputFiber cutoff output)

classifiedPhysicalOutputFiberErasesExactly :
  (cutoff : Nat) →
  (output : Z3.FourierMode) →
  eraseClassifiedPhysicalTriads
    (classifiedPhysicalOutputFiber cutoff output)
  ≡ Output.physicalOutputFiber cutoff output
classifiedPhysicalOutputFiberErasesExactly cutoff output =
  eraseClassifiedPhysicalTriadsExact
    (Output.physicalOutputFiber cutoff output)

------------------------------------------------------------------------
-- Fifth class: differentiated commutator.  No residual constructor exists.
------------------------------------------------------------------------

data FiveSourceCell : Set where
  triadicSource : ClassifiedPhysicalTriad → FiveSourceCell
  differentiatedCommutator : Z3.FourierMode → FiveSourceCell

triadicToFiveClass : TriadicSourceClass → Range.FiveInteractionClass
triadicToFiveClass LH = Range.LH
triadicToFiveClass HL = Range.HL
triadicToFiveClass HH = Range.HH
triadicToFiveClass CC = Range.CC

fiveSourceClass : FiveSourceCell → Range.FiveInteractionClass
fiveSourceClass (triadicSource τ) = triadicToFiveClass (sourceClass τ)
fiveSourceClass (differentiatedCommutator output) = Range.Com

mapTriadicSources : List ClassifiedPhysicalTriad → List FiveSourceCell
mapTriadicSources [] = []
mapTriadicSources (τ ∷ rest) =
  triadicSource τ ∷ mapTriadicSources rest

appendFiveSources :
  List FiveSourceCell → List FiveSourceCell → List FiveSourceCell
appendFiveSources [] right = right
appendFiveSources (left ∷ rest) right =
  left ∷ appendFiveSources rest right

fiveSourceOutputFiber :
  Nat → Z3.FourierMode → List FiveSourceCell
fiveSourceOutputFiber cutoff output =
  appendFiveSources
    (mapTriadicSources (classifiedPhysicalOutputFiber cutoff output))
    (differentiatedCommutator output ∷ [])

fiveSourceClassificationTotal :
  (cell : FiveSourceCell) →
  Σ Range.FiveInteractionClass
    (λ source → fiveSourceClass cell ≡ source)
fiveSourceClassificationTotal cell = fiveSourceClass cell , refl

------------------------------------------------------------------------
-- Fixed collar constants and fail-closed analytic boundary.
------------------------------------------------------------------------

separationCollarIsThree : Shell.Csep ≡ 3
separationCollarIsThree = refl

outputTrackingCollarIsTwo : Shell.Cout ≡ 2
outputTrackingCollarIsTwo = refl

inputComparabilityCollarIsTwo : Shell.Cin ≡ 2
inputComparabilityCollarIsTwo = refl

record PhysicalFiveClassRound25Status : Set where
  constructor physical-five-class-round25-status
  field
    actualPhysicalTriadsClassified : Bool
    classificationTotalAndUnique : Bool
    lowLowToFarHighExcluded : Bool
    outputFibresRecomposeExactly : Bool
    fifthCommutatorClassSeparated : Bool
    genericRemainderAbsent : Bool
    cutoffsEnterClassifierConstants : Bool
    classwiseAnalyticBoundsProduced : Bool

open PhysicalFiveClassRound25Status public

canonicalPhysicalFiveClassRound25Status : PhysicalFiveClassRound25Status
canonicalPhysicalFiveClassRound25Status =
  physical-five-class-round25-status
    true true true true true true false false
