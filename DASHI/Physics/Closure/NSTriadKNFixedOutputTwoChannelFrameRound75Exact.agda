module DASHI.Physics.Closure.NSTriadKNFixedOutputTwoChannelFrameRound75Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- DOI: 10.1007/BF02547354.
--
-- Authors: Augustin-Louis Cauchy; Hermann Amandus Schwarz.
-- Classical finite-dimensional Cauchy--Schwarz inequality; DOI not applicable.
--
-- Author: Ole Christensen.
-- Title: "An Introduction to Frames and Riesz Bases".
-- DOI: 10.1007/978-3-319-25613-9.
--
-- ROUND75 / FIXED-OUTPUT RESPONSE FRAME WITHOUT CARDINALITY LOSS
--
-- Round75 reduced the canonical right-factor mass to
--
--   W_tau <= ||u_k||^2 ||u_q||^2.
--
-- On one exact output fibre k, q is an injective coordinate: if two resonant
-- incidences have the same q and the same output, then p=k-q is the same, and
-- Round35's proof-relevant incidence extensionality identifies the incidences.
-- Every q lies in the literal cutoff cube.  Therefore the q-energy appearing in
-- the output fibre is a UNIQUE restriction of the full cutoff energy, not an
-- atom-count multiple of that energy.
--
-- The resulting exact finite estimate is
--
--   W_k <= ||u_k||^2 * sum_{q in cutoff} ||u_q||^2.
--
-- This is the source-native frame theorem for the response coordinate at one
-- output.  No cardinality, square root, phase choice or post-hoc frame
-- certificate appears.  Remaining theorem-4 work is the Q/charge budget and
-- transport to the selected time-dependent trajectory.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Integer.Base using (ℤ; _+_; _-_)
import Data.Integer.Properties as Int
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; subst; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNOfficialInfinityNormTriangle as Infinity
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiberPermutationRound35Exact as Permutation
import DASHI.Physics.Closure.NSTriadKNFixedOutputFiberThreeDOFRound72Exact as Fixed
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as RationalL2
import DASHI.Physics.Closure.NSTriadKNRationalComplex3Separation as Separation
import DASHI.Physics.Closure.NSTriadKNRationalComplex3LerayPythagoras as Leray
import DASHI.Physics.Closure.NSTriadKNLuoPhysicalFiveClassSupportRound25Exact as Support
import DASHI.Physics.Closure.NSTriadKNStaticPairingEmitsStructuredTriadicAtomsRound72Exact as Fine
import DASHI.Physics.Closure.NSTriadKNFactorizedEffectiveComplexityCauchyRound72Exact as Effective
import DASHI.Physics.Closure.NSTriadKNTwoChannelStructuredCauchyOverlayRound74Exact as Overlay
import DASHI.Physics.Closure.NSTriadKNCanonicalTwoChannelPhysicalMassBoundsRound75Exact as Bounds
import DASHI.Physics.Closure.NSTriadKNStaticRationalTwoChannelOverlayRound75Exact as Static
import DASHI.Physics.Closure.NSTriadKNTwoChannelOutputFibreMassSumRound75Exact as Sum

F : C3.RealField _
F = RationalL2.rationalRealField

------------------------------------------------------------------------
-- q is an injective coordinate on one fixed output fibre.
------------------------------------------------------------------------

pCoordinateFromQK :
  (τ : Physical.PhysicalTriadIncidence) →
  (coordinate : Z3.FourierMode → ℤ) →
  coordinate (Physical.p τ)
  ≡ coordinate (Physical.k τ) - coordinate (Physical.q τ)
pCoordinateFromQK τ coordinate =
  trans
    (sym (Infinity.sumMinusLeft
      (coordinate (Physical.q τ))
      (coordinate (Physical.p τ))))
    (cong
      (λ total → total - coordinate (Physical.q τ))
      (trans
        (Int.+-comm
          (coordinate (Physical.q τ))
          (coordinate (Physical.p τ)))
        (cong coordinate (Physical.resonance τ))))

pDeterminedByQAndOutput :
  (left right : Physical.PhysicalTriadIncidence) →
  Physical.q left ≡ Physical.q right →
  Physical.k left ≡ Physical.k right →
  Physical.p left ≡ Physical.p right
pDeterminedByQAndOutput left right qExact kExact =
  Output.modeExt
    (trans
      (pCoordinateFromQK left Z3.kx)
      (trans
        (cong₂ _-_
          (cong Z3.kx kExact)
          (cong Z3.kx qExact))
        (sym (pCoordinateFromQK right Z3.kx))))
    (trans
      (pCoordinateFromQK left Z3.ky)
      (trans
        (cong₂ _-_
          (cong Z3.ky kExact)
          (cong Z3.ky qExact))
        (sym (pCoordinateFromQK right Z3.ky))))
    (trans
      (pCoordinateFromQK left Z3.kz)
      (trans
        (cong₂ _-_
          (cong Z3.kz kExact)
          (cong Z3.kz qExact))
        (sym (pCoordinateFromQK right Z3.kz))))

fixedOutputQInjective :
  ∀ {cutoff output left right} →
  left Cube.∈ Output.physicalOutputFiber cutoff output →
  right Cube.∈ Output.physicalOutputFiber cutoff output →
  Physical.q left ≡ Physical.q right →
  left ≡ right
fixedOutputQInjective leftMember rightMember qExact =
  let
    kExact = trans
      (Output.physicalOutputFiberSound leftMember)
      (sym (Output.physicalOutputFiberSound rightMember))
    pExact = pDeterminedByQAndOutput _ _ qExact kExact
  in
  Permutation.physicalIncidenceExtPQ _ _ pExact qExact

qModes : List Physical.PhysicalTriadIncidence → List Z3.FourierMode
qModes [] = []
qModes (τ ∷ rest) = Physical.q τ ∷ qModes rest

qModePreimage :
  ∀ {mode triads} →
  mode Cube.∈ qModes triads →
  Σ Physical.PhysicalTriadIncidence
    (λ τ → (τ Cube.∈ triads) × (mode ≡ Physical.q τ))
qModePreimage {triads = []} ()
qModePreimage {triads = head ∷ tail} (Cube.here equality) =
  head , (Cube.here refl , equality)
qModePreimage {triads = head ∷ tail} (Cube.there member)
  with qModePreimage member
... | τ , (τMember , equality) =
  τ , (Cube.there τMember , equality)

fixedOutputQModesNoDuplicatesGeneral :
  ∀ {cutoff output triads} →
  Cube.NoDuplicates triads →
  (∀ τ → τ Cube.∈ triads → Physical.k τ ≡ output) →
  Cube.NoDuplicates (qModes triads)
fixedOutputQModesNoDuplicatesGeneral Cube.unique[] allOutput = Cube.unique[]
fixedOutputQModesNoDuplicatesGeneral
    {cutoff} {output} {triads = head ∷ tail}
    (Cube.unique∷ fresh restUnique) allOutput =
  Cube.unique∷ headQFresh tailUnique
  where
  tailAllOutput : ∀ τ → τ Cube.∈ tail → Physical.k τ ≡ output
  tailAllOutput τ member = allOutput τ (Cube.there member)

  tailUnique : Cube.NoDuplicates (qModes tail)
  tailUnique =
    fixedOutputQModesNoDuplicatesGeneral restUnique tailAllOutput

  headQFresh : Physical.q head Cube.∉ qModes tail
  headQFresh qMember with qModePreimage qMember
  ... | τ , (τMember , qEqual) =
    let
      headK = allOutput head (Cube.here refl)
      tailK = tailAllOutput τ τMember
      kEqual = trans headK (sym tailK)
      pEqual = pDeterminedByQAndOutput head τ qEqual kEqual
      triadEqual = Permutation.physicalIncidenceExtPQ head τ pEqual qEqual
      headInTail : head Cube.∈ tail
      headInTail = subst (_Cube.∈ tail) (sym triadEqual) τMember
    in fresh headInTail

fixedOutputQModesNoDuplicates :
  (cutoff : Agda.Builtin.Nat.Nat) (output : Z3.FourierMode) →
  Cube.NoDuplicates (qModes (Output.physicalOutputFiber cutoff output))
fixedOutputQModesNoDuplicates cutoff output =
  fixedOutputQModesNoDuplicatesGeneral
    (Permutation.filterOutputNoDuplicates
      output
      (Physical.physicalTriadEnumeration cutoff)
      (Physical.physicalTriadEnumerationNoDuplicates cutoff))
    (λ τ member → Output.physicalOutputFiberSound member)

fixedOutputQModesInCutoff :
  ∀ {cutoff output mode} →
  mode Cube.∈ qModes (Output.physicalOutputFiber cutoff output) →
  mode Cube.∈ Cube.cutoffModes cutoff
fixedOutputQModesInCutoff {cutoff} {output} {mode} member
  with qModePreimage member
... | τ , (τMember , modeEqualsQ) =
  subst
    (_Cube.∈ Cube.cutoffModes cutoff)
    (sym modeEqualsQ)
    (proj₂ (Fixed.fixedOutputInputCutoff τMember))

------------------------------------------------------------------------
-- Generic finite restriction theorem for a nonnegative rational mass.
------------------------------------------------------------------------

sumMass : ∀ {A : Set} → (A → ℚ) → List A → ℚ
sumMass mass [] = 0ℚ
sumMass mass (x ∷ xs) = mass x + sumMass mass xs

removeAt : ∀ {A : Set} {x : A} {xs : List A} → x Cube.∈ xs → List A
removeAt {xs = _ ∷ xs} (Cube.here refl) = xs
removeAt {xs = y ∷ ys} (Cube.there member) = y ∷ removeAt member

sumMassRemoveAtExact :
  ∀ {A : Set} (mass : A → ℚ) {x xs}
    (member : x Cube.∈ xs) →
  sumMass mass xs ≡ mass x + sumMass mass (removeAt member)
sumMassRemoveAtExact mass (Cube.here refl) = refl
sumMassRemoveAtExact mass {x = x} {xs = y ∷ ys} (Cube.there member) =
  trans
    (cong (mass y +_) (sumMassRemoveAtExact mass member))
    (solve
      ( mass y
      ∷ mass x
      ∷ sumMass mass (removeAt member)
      ∷ []))

otherMemberSurvivesRemoval :
  ∀ {A : Set} {x z : A} {xs : List A}
    (selected : x Cube.∈ xs) →
  z Cube.∈ xs →
  (z ≡ x → Data.Empty.⊥) →
  z Cube.∈ removeAt selected
otherMemberSurvivesRemoval (Cube.here refl) (Cube.here equality) different =
  Data.Empty.⊥-elim (different equality)
otherMemberSurvivesRemoval (Cube.here refl) (Cube.there member) different = member
otherMemberSurvivesRemoval (Cube.there selected) (Cube.here equality) different =
  Cube.here equality
otherMemberSurvivesRemoval
    (Cube.there selected) (Cube.there member) different =
  Cube.there (otherMemberSurvivesRemoval selected member different)

uniqueRestrictionMassBound :
  ∀ {A : Set}
    (mass : A → ℚ) →
  (∀ x → 0ℚ ≤ mass x) →
  ∀ {selected full} →
  Cube.NoDuplicates selected →
  (∀ x → x Cube.∈ selected → x Cube.∈ full) →
  sumMass mass selected ≤ sumMass mass full
uniqueRestrictionMassBound mass massNN Cube.unique[] subset =
  let
    fullNN : ∀ xs → 0ℚ ≤ sumMass mass xs
    fullNN [] = ℚP.≤-refl
    fullNN (x ∷ xs) = ℚP.+-mono-≤ (massNN x) (fullNN xs)
  in fullNN _
uniqueRestrictionMassBound mass massNN
    {selected = x ∷ xs} {full}
    (Cube.unique∷ fresh restUnique) subset =
  let
    xMember : x Cube.∈ full
    xMember = subset x (Cube.here refl)

    tailSubsetRemoved : ∀ z → z Cube.∈ xs → z Cube.∈ removeAt xMember
    tailSubsetRemoved z zMember =
      otherMemberSurvivesRemoval
        xMember
        (subset z (Cube.there zMember))
        (λ zEqualsX →
          fresh (subst (_Cube.∈ xs) zEqualsX zMember))

    tailBound :
      sumMass mass xs ≤ sumMass mass (removeAt xMember)
    tailBound =
      uniqueRestrictionMassBound
        mass massNN restUnique tailSubsetRemoved

    addHead :
      mass x + sumMass mass xs
      ≤ mass x + sumMass mass (removeAt xMember)
    addHead = ℚP.+-mono-≤ ℚP.≤-refl tailBound
  in
  subst
    ((mass x + sumMass mass xs) ≤_)
    (sym (sumMassRemoveAtExact mass xMember))
    addHead

------------------------------------------------------------------------
-- Apply the restriction theorem to the q-energy of one output fibre.
------------------------------------------------------------------------

modeEnergy :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Audit.FiniteComplex3GalerkinSystem F E I →
  Z3.FourierMode → ℚ
modeEnergy system mode =
  L2.complex3NormSquared (Audit.velocityAt system mode)

modeEnergyNonnegative :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    mode →
  0ℚ ≤ modeEnergy system mode
modeEnergyNonnegative system mode =
  Separation.complex3NormSquaredNonnegative (Audit.velocityAt system mode)

cutoffEnergy :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Audit.FiniteComplex3GalerkinSystem F E I → ℚ
cutoffEnergy system =
  sumMass (modeEnergy system) (Cube.cutoffModes (Audit.cutoff system))

fixedOutputQEnergy :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Audit.FiniteComplex3GalerkinSystem F E I →
  Z3.FourierMode → ℚ
fixedOutputQEnergy system output =
  sumMass
    (modeEnergy system)
    (qModes (Output.physicalOutputFiber (Audit.cutoff system) output))

fixedOutputQEnergyBelowCutoffEnergy :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (output : Z3.FourierMode) →
  fixedOutputQEnergy system output ≤ cutoffEnergy system
fixedOutputQEnergyBelowCutoffEnergy system output =
  uniqueRestrictionMassBound
    (modeEnergy system)
    (modeEnergyNonnegative system)
    (fixedOutputQModesNoDuplicates (Audit.cutoff system) output)
    (λ mode member → fixedOutputQModesInCutoff member)

------------------------------------------------------------------------
-- Fixed-output W bound on the exact classified fibre.
------------------------------------------------------------------------

rawCanonicalWSum :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Audit.FiniteComplex3GalerkinSystem F E I →
  List Physical.PhysicalTriadIncidence → ℚ
rawCanonicalWSum system triads =
  Sum.canonicalWSum system (Support.classifyPhysicalTriads triads)

rawQEnergy :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Audit.FiniteComplex3GalerkinSystem F E I →
  List Physical.PhysicalTriadIncidence → ℚ
rawQEnergy system triads = sumMass (modeEnergy system) (qModes triads)

rawCanonicalWSumFixedOutputBound :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (O : Leray.RationalInverseNormOrder E I)
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (output : Z3.FourierMode)
    (outputNonzero : Z3.NonZeroMode output)
    (triads : List Physical.PhysicalTriadIncidence) →
  (∀ τ → τ Cube.∈ triads → Physical.k τ ≡ output) →
  rawCanonicalWSum system triads
  ≤ modeEnergy system output * rawQEnergy system triads
rawCanonicalWSumFixedOutputBound O system output outputNonzero [] allOutput =
  ℚP.≤-refl
rawCanonicalWSumFixedOutputBound
    O system output outputNonzero (head ∷ tail) allOutput =
  let
    headK = allOutput head (Cube.here refl)
    headNonzero : Z3.NonZeroMode (Physical.k head)
    headNonzero = subst Z3.NonZeroMode (sym headK) outputNonzero

    local = Bounds.orderedInteractionCanonicalWBound
      O system head headNonzero (Static.outputVelocityTest system head)

    kMassExact :
      modeEnergy system (Physical.k head) ≡ modeEnergy system output
    kMassExact = cong (modeEnergy system) headK

    localFixed :
      Sum.canonicalWSum system (Support.classifyOnePhysicalTriad head ∷ [])
      ≤ modeEnergy system output * modeEnergy system (Physical.q head)
    localFixed =
      subst
        (λ kMass →
          Sum.canonicalWSum system (Support.classifyOnePhysicalTriad head ∷ [])
          ≤ kMass * modeEnergy system (Physical.q head))
        kMassExact
        local

    tailOutput : ∀ τ → τ Cube.∈ tail → Physical.k τ ≡ output
    tailOutput τ member = allOutput τ (Cube.there member)

    tailBound =
      rawCanonicalWSumFixedOutputBound
        O system output outputNonzero tail tailOutput

    combined = ℚP.+-mono-≤ localFixed tailBound
  in
  subst
    (λ upper → rawCanonicalWSum system (head ∷ tail) ≤ upper)
    (solve
      ( modeEnergy system output
      ∷ modeEnergy system (Physical.q head)
      ∷ rawQEnergy system tail
      ∷ []))
    combined

fixedOutputCanonicalWSumFrameBound :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (O : Leray.RationalInverseNormOrder E I)
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (output : Z3.FourierMode) →
  Z3.NonZeroMode output →
  Sum.canonicalWSum system
    (Support.classifiedPhysicalOutputFiber (Audit.cutoff system) output)
  ≤ modeEnergy system output * cutoffEnergy system
fixedOutputCanonicalWSumFrameBound O system output outputNonzero =
  let
    fibre = Output.physicalOutputFiber (Audit.cutoff system) output
    first :
      rawCanonicalWSum system fibre
      ≤ modeEnergy system output * rawQEnergy system fibre
    first = rawCanonicalWSumFixedOutputBound
      O system output outputNonzero fibre
      (λ τ member → Output.physicalOutputFiberSound member)

    restriction = fixedOutputQEnergyBelowCutoffEnergy system output
    outputNN = modeEnergyNonnegative system output
    qNN : 0ℚ ≤ fixedOutputQEnergy system output
    qNN =
      let
        sumNN : ∀ modes → 0ℚ ≤ sumMass (modeEnergy system) modes
        sumNN [] = ℚP.≤-refl
        sumNN (mode ∷ modes) =
          ℚP.+-mono-≤ (modeEnergyNonnegative system mode) (sumNN modes)
      in sumNN _
    cutoffNN : 0ℚ ≤ cutoffEnergy system
    cutoffNN = ℚP.≤-trans qNN restriction
    scaled =
      L2.nonnegativeProductMonotone
        outputNN qNN outputNN cutoffNN ℚP.≤-refl restriction
  in
  ℚP.≤-trans first scaled

staticRationalOverlayEffectiveComplexityFrameBound :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (O : Leray.RationalInverseNormOrder E I)
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (output : Z3.FourierMode)
    (outputNonzero : Z3.NonZeroMode output)
    (commutatorValue : Z3.FourierMode → ℚ)
    (hh : Fine.HHOwnerSelection) →
  Effective.effectiveComplexity
    (Overlay.twoChannelFactors
      (Static.staticRationalTwoChannelOverlay
        system output commutatorValue hh))
  ≤ modeEnergy system output * cutoffEnergy system
staticRationalOverlayEffectiveComplexityFrameBound
    O system output outputNonzero commutatorValue hh =
  let
    classified =
      Support.classifiedPhysicalOutputFiber (Audit.cutoff system) output
    pairing = Static.staticRationalPhysicalPairing system output commutatorValue
    exact = Sum.factorComplexityFromClassifiedExact
      system pairing hh classified (λ selected → refl)
    physical = fixedOutputCanonicalWSumFrameBound
      O system output outputNonzero
  in
  subst
    (_≤ modeEnergy system output * cutoffEnergy system)
    (sym exact)
    physical

round75FixedOutputQCoordinateInjective : Bool
round75FixedOutputQCoordinateInjective = true

round75FixedOutputQEnergyIsUniqueCutoffRestriction : Bool
round75FixedOutputQEnergyIsUniqueCutoffRestriction = true

round75FixedOutputResponseFrameHasNoCardinalityLoss : Bool
round75FixedOutputResponseFrameHasNoCardinalityLoss = true

round75StaticOverlayEffectiveComplexityFrameBoundConstructed : Bool
round75StaticOverlayEffectiveComplexityFrameBoundConstructed = true

round75StaticOverlayEffectiveComplexityFrameBoundConstructedIsTrue :
  round75StaticOverlayEffectiveComplexityFrameBoundConstructed ≡ true
round75StaticOverlayEffectiveComplexityFrameBoundConstructedIsTrue = refl
