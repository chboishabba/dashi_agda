module DASHI.Physics.Closure.NSTriadKNFixedOutputTwoChannelChargeRound75Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- DOI: 10.1007/BF02547354.
--
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- DOI: 10.1090/chel/343.
--
-- ROUND75 / FIXED-OUTPUT CANONICAL Q IS ENERGY + DISSIPATION CONTROLLED
--
-- The source-native two-channel left mass is
--
--   Q_tau = |-i (u_p dot q)|^2
--           <= ||u_p||^2 |q|^2.
--
-- On a fixed output k, q=k-p.  Instead of the crude cutoff estimate |q|^2
-- <= O(N^2), we use the exact Hilbert-space inequality
--
--   |q|^2 <= 2 |k|^2 + 2 |p|^2.
--
-- The p-coordinate is injective on one output fibre and lies in the cutoff
-- cube.  Summing therefore gives the cutoff-independent structural form
--
--   Q_k <= 2 |k|^2 E_N + 2 D_N,
--
-- where
--
--   E_N = sum_p ||u_p||^2,
--   D_N = sum_p |p|^2 ||u_p||^2.
--
-- Thus the canonical concentration charge is not an arbitrary Cauchy factor
-- and does not require an N^2 cardinality/cutoff tax: it is controlled by the
-- same energy/enstrophy quantities already present in the Galerkin energy law.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Sigma using (Σ; _,_)
import Data.Integer.Base as Int
open import Data.Product.Base using (_×_; _,_; proj₁)
open import Data.Rational.Base using
  (ℚ; 0ℚ; _+_; _*_; _≤_; _/_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym; trans)
open import Relation.Nullary.Decidable.Core using (toWitness)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiberPermutationRound35Exact as Permutation
import DASHI.Physics.Closure.NSTriadKNFixedOutputFiberThreeDOFRound72Exact as Fixed
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3AlgebraLaws as Algebra
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as RationalL2
import DASHI.Physics.Closure.NSTriadKNRationalComplex3Separation as Separation
import DASHI.Physics.Closure.NSTriadKNLuoPhysicalFiveClassSupportRound25Exact as Support
import DASHI.Physics.Closure.NSTriadKNStaticPairingEmitsStructuredTriadicAtomsRound72Exact as Fine
import DASHI.Physics.Closure.NSTriadKNFactorizedEffectiveComplexityCauchyRound72Exact as Effective
import DASHI.Physics.Closure.NSTriadKNTwoChannelStructuredCauchyOverlayRound74Exact as Overlay
import DASHI.Physics.Closure.NSTriadKNCanonicalTwoChannelPhysicalMassBoundsRound75Exact as Bounds
import DASHI.Physics.Closure.NSTriadKNStaticRationalTwoChannelOverlayRound75Exact as Static
import DASHI.Physics.Closure.NSTriadKNTwoChannelOutputFibreMassSumRound75Exact as Sum
import DASHI.Physics.Closure.NSTriadKNFixedOutputTwoChannelFrameRound75Exact as Frame

F : C3.RealField _
F = RationalL2.rationalRealField

two : ℚ
two = Int.+ 2 / 1

twoNonnegative : 0ℚ ≤ two
twoNonnegative = toWitness {a? = 0ℚ ℚP.≤? two} _

modeNorm :
  (E : C3.IntegerEmbedding F) → Z3.FourierMode → ℚ
modeNorm E mode = L2.complex3NormSquared (C3.modeVector E mode)

modeNormNonnegative :
  (E : C3.IntegerEmbedding F) →
  ∀ mode → 0ℚ ≤ modeNorm E mode
modeNormNonnegative E mode =
  Separation.complex3NormSquaredNonnegative (C3.modeVector E mode)

------------------------------------------------------------------------
-- Rational C3 inequality ||v||^2 <= 2||u+v||^2 + 2||u||^2.
------------------------------------------------------------------------

rightNormBelowTwiceSumPlusLeft :
  (left right : C3.Complex3 F) →
  L2.complex3NormSquared right
  ≤ two * L2.complex3NormSquared (C3.complex3Add left right)
    + two * L2.complex3NormSquared left
rightNormBelowTwiceSumPlusLeft
    (C3.complex3
      (C3.complex axr axi) (C3.complex ayr ayi) (C3.complex azr azi))
    (C3.complex3
      (C3.complex bxr bxi) (C3.complex byr byi) (C3.complex bzr bzi)) =
  let
    defect =
        RationalL2.square (axr + axr + bxr)
      + RationalL2.square (axi + axi + bxi)
      + RationalL2.square (ayr + ayr + byr)
      + RationalL2.square (ayi + ayi + byi)
      + RationalL2.square (azr + azr + bzr)
      + RationalL2.square (azi + azi + bzi)

    defectNN : 0ℚ ≤ defect
    defectNN =
      RationalL2.addNonnegative
        (RationalL2.addNonnegative
          (RationalL2.addNonnegative
            (RationalL2.addNonnegative
              (RationalL2.addNonnegative
                (RationalL2.squareNonnegative (axr + axr + bxr))
                (RationalL2.squareNonnegative (axi + axi + bxi)))
              (RationalL2.squareNonnegative (ayr + ayr + byr)))
            (RationalL2.squareNonnegative (ayi + ayi + byi)))
          (RationalL2.squareNonnegative (azr + azr + bzr)))
        (RationalL2.squareNonnegative (azi + azi + bzi))

    base = L2.complex3NormSquared
      (C3.complex3
        (C3.complex bxr bxi) (C3.complex byr byi) (C3.complex bzr bzi))

    withDefect : base ≤ base + defect
    withDefect =
      subst
        (base ≤_)
        (sym (ℚP.+-identityˡ base))
        (ℚP.+-mono-≤ ℚP.≤-refl defectNN)
  in
  subst
    (base ≤_)
    (solve
      ( axr ∷ axi ∷ ayr ∷ ayi ∷ azr ∷ azi
      ∷ bxr ∷ bxi ∷ byr ∷ byi ∷ bzr ∷ bzi ∷ []))
    withDefect

modeQNormFixedOutputBound :
  (E : C3.IntegerEmbedding F) →
  (tau : Physical.PhysicalTriadIncidence) →
  modeNorm E (Physical.q tau)
  ≤ two * modeNorm E (Physical.k tau)
    + two * modeNorm E (Physical.p tau)
modeQNormFixedOutputBound E tau =
  let
    base = rightNormBelowTwiceSumPlusLeft
      (C3.modeVector E (Physical.p tau))
      (C3.modeVector E (Physical.q tau))
    sumToOutput :
      C3.complex3Add
        (C3.modeVector E (Physical.p tau))
        (C3.modeVector E (Physical.q tau))
      ≡ C3.modeVector E (Physical.k tau)
    sumToOutput =
      trans
        (sym (Algebra.modeVectorAdd E (Physical.p tau) (Physical.q tau)))
        (cong (C3.modeVector E) (Physical.resonance tau))
  in
  subst
    (λ sumMass →
      modeNorm E (Physical.q tau)
      ≤ two * sumMass + two * modeNorm E (Physical.p tau))
    (cong L2.complex3NormSquared sumToOutput)
    base

------------------------------------------------------------------------
-- p is likewise an injective coordinate on one fixed output fibre.
------------------------------------------------------------------------

pModes : List Physical.PhysicalTriadIncidence → List Z3.FourierMode
pModes [] = []
pModes (tau ∷ rest) = Physical.p tau ∷ pModes rest

pModePreimage :
  ∀ {mode triads} →
  mode Cube.∈ pModes triads →
  Σ Physical.PhysicalTriadIncidence
    (λ tau → (tau Cube.∈ triads) × (mode ≡ Physical.p tau))
pModePreimage {triads = []} ()
pModePreimage {triads = head ∷ tail} (Cube.here equality) =
  head , (Cube.here refl , equality)
pModePreimage {triads = head ∷ tail} (Cube.there member)
  with pModePreimage member
... | tau , (tauMember , equality) =
  tau , (Cube.there tauMember , equality)

fixedOutputPModesNoDuplicatesGeneral :
  ∀ {output triads} →
  Cube.NoDuplicates triads →
  (∀ tau → tau Cube.∈ triads → Physical.k tau ≡ output) →
  Cube.NoDuplicates (pModes triads)
fixedOutputPModesNoDuplicatesGeneral Cube.unique[] allOutput = Cube.unique[]
fixedOutputPModesNoDuplicatesGeneral
    {output} {triads = head ∷ tail}
    (Cube.unique∷ fresh restUnique) allOutput =
  Cube.unique∷ headPFresh tailUnique
  where
  tailAllOutput : ∀ tau → tau Cube.∈ tail → Physical.k tau ≡ output
  tailAllOutput tau member = allOutput tau (Cube.there member)

  tailUnique : Cube.NoDuplicates (pModes tail)
  tailUnique = fixedOutputPModesNoDuplicatesGeneral restUnique tailAllOutput

  headPFresh : Physical.p head Cube.∉ pModes tail
  headPFresh pMember with pModePreimage pMember
  ... | tau , (tauMember , pEqual) =
    let
      headK = allOutput head (Cube.here refl)
      tailK = tailAllOutput tau tauMember
      qEqual = Fixed.qDeterminedByPAndOutput head tau pEqual
        (trans headK (sym tailK))
      triadEqual = Permutation.physicalIncidenceExtPQ head tau pEqual qEqual
      headInTail : head Cube.∈ tail
      headInTail =
        subst (λ selected → selected Cube.∈ tail) (sym triadEqual) tauMember
    in fresh headInTail

fixedOutputPModesNoDuplicates :
  ∀ cutoff output →
  Cube.NoDuplicates (pModes (Output.physicalOutputFiber cutoff output))
fixedOutputPModesNoDuplicates cutoff output =
  fixedOutputPModesNoDuplicatesGeneral
    (Permutation.filterOutputNoDuplicates
      output
      (Physical.physicalTriadEnumeration cutoff)
      (Physical.physicalTriadEnumerationNoDuplicates cutoff))
    (λ tau member → Output.physicalOutputFiberSound member)

fixedOutputPModesInCutoff :
  ∀ {cutoff output mode} →
  mode Cube.∈ pModes (Output.physicalOutputFiber cutoff output) →
  mode Cube.∈ Cube.cutoffModes cutoff
fixedOutputPModesInCutoff {cutoff} member with pModePreimage member
... | tau , (tauMember , modeEqualsP) =
  subst
    (λ selected → selected Cube.∈ Cube.cutoffModes cutoff)
    (sym modeEqualsP)
    (proj₁ (Fixed.fixedOutputInputCutoff tauMember))

------------------------------------------------------------------------
-- Full cutoff energy and dissipation, and their p-fibre restrictions.
------------------------------------------------------------------------

modeDissipation :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Audit.FiniteComplex3GalerkinSystem F E I → Z3.FourierMode → ℚ
modeDissipation system mode =
  modeNorm (Audit.integerEmbedding system) mode * Frame.modeEnergy system mode

modeDissipationNonnegative :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    mode → 0ℚ ≤ modeDissipation system mode
modeDissipationNonnegative system mode =
  let
    leftNN = modeNormNonnegative (Audit.integerEmbedding system) mode
    rightNN = Frame.modeEnergyNonnegative system mode
  in
  ℚP.nonNegative⁻¹ _
  where
  instance
    leftNNI = Data.Rational.Base.nonNegative
      (modeNormNonnegative (Audit.integerEmbedding system) mode)
    rightNNI = Data.Rational.Base.nonNegative
      (Frame.modeEnergyNonnegative system mode)
    productNNI = ℚP.nonNeg*nonNeg⇒nonNeg
      (modeNorm (Audit.integerEmbedding system) mode)
      (Frame.modeEnergy system mode)

cutoffDissipation :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Audit.FiniteComplex3GalerkinSystem F E I → ℚ
cutoffDissipation system =
  Frame.sumMass
    (modeDissipation system)
    (Cube.cutoffModes (Audit.cutoff system))

fixedOutputPEnergy :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Audit.FiniteComplex3GalerkinSystem F E I → Z3.FourierMode → ℚ
fixedOutputPEnergy system output =
  Frame.sumMass
    (Frame.modeEnergy system)
    (pModes (Output.physicalOutputFiber (Audit.cutoff system) output))

fixedOutputPDissipation :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Audit.FiniteComplex3GalerkinSystem F E I → Z3.FourierMode → ℚ
fixedOutputPDissipation system output =
  Frame.sumMass
    (modeDissipation system)
    (pModes (Output.physicalOutputFiber (Audit.cutoff system) output))

fixedOutputPEnergyBelowCutoffEnergy :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    output →
  fixedOutputPEnergy system output ≤ Frame.cutoffEnergy system
fixedOutputPEnergyBelowCutoffEnergy system output =
  Frame.uniqueRestrictionMassBound
    (Frame.modeEnergy system)
    (Frame.modeEnergyNonnegative system)
    (fixedOutputPModesNoDuplicates (Audit.cutoff system) output)
    (λ mode member → fixedOutputPModesInCutoff member)

fixedOutputPDissipationBelowCutoffDissipation :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    output →
  fixedOutputPDissipation system output ≤ cutoffDissipation system
fixedOutputPDissipationBelowCutoffDissipation system output =
  Frame.uniqueRestrictionMassBound
    (modeDissipation system)
    (modeDissipationNonnegative system)
    (fixedOutputPModesNoDuplicates (Audit.cutoff system) output)
    (λ mode member → fixedOutputPModesInCutoff member)

------------------------------------------------------------------------
-- Sum the per-triad Q estimate and insert the two unique restrictions.
------------------------------------------------------------------------

rawCanonicalQSum :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Audit.FiniteComplex3GalerkinSystem F E I →
  List Physical.PhysicalTriadIncidence → ℚ
rawCanonicalQSum system triads =
  Sum.canonicalQSum system (Support.classifyPhysicalTriads triads)

rawPEnergy :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Audit.FiniteComplex3GalerkinSystem F E I →
  List Physical.PhysicalTriadIncidence → ℚ
rawPEnergy system triads =
  Frame.sumMass (Frame.modeEnergy system) (pModes triads)

rawPDissipation :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Audit.FiniteComplex3GalerkinSystem F E I →
  List Physical.PhysicalTriadIncidence → ℚ
rawPDissipation system triads =
  Frame.sumMass (modeDissipation system) (pModes triads)

rawCanonicalQFixedOutputBound :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (output : Z3.FourierMode)
    (triads : List Physical.PhysicalTriadIncidence) →
  (∀ tau → tau Cube.∈ triads → Physical.k tau ≡ output) →
  rawCanonicalQSum system triads
  ≤
    two * modeNorm (Audit.integerEmbedding system) output * rawPEnergy system triads
    + two * rawPDissipation system triads
rawCanonicalQFixedOutputBound system output [] allOutput = ℚP.≤-refl
rawCanonicalQFixedOutputBound system output (head ∷ tail) allOutput =
  let
    E = Audit.integerEmbedding system
    headK = allOutput head (Cube.here refl)
    headClassified = Support.classifyOnePhysicalTriad head
    headMass =
      DASHI.Physics.Closure.NSTriadKNOrderedInteractionTwoChannelMassIdentityRound74Exact.leftChannelSquaredMass
        (Static.channelsForClassified system headClassified)
    localQ = Bounds.orderedInteractionCanonicalQBound system head
    qModeBound = modeQNormFixedOutputBound E head
    velocityNN = Frame.modeEnergyNonnegative system (Physical.p head)
    qNormNN = modeNormNonnegative E (Physical.q head)
    upperNN =
      RationalL2.addNonnegative
        (let
          instance
            tNN = Data.Rational.Base.nonNegative twoNonnegative
            kNN = Data.Rational.Base.nonNegative (modeNormNonnegative E (Physical.k head))
          in ℚP.nonNegative⁻¹ _)
        (let
          instance
            tNN = Data.Rational.Base.nonNegative twoNonnegative
            pNN = Data.Rational.Base.nonNegative (modeNormNonnegative E (Physical.p head))
          in ℚP.nonNegative⁻¹ _)
    localScaled =
      ℚP.≤-trans localQ
        (RationalL2.nonnegativeProductMonotone
          velocityNN qNormNN velocityNN upperNN
          ℚP.≤-refl qModeBound)
    localFixed :
      headMass
      ≤
        two * modeNorm E output * Frame.modeEnergy system (Physical.p head)
        + two * modeDissipation system (Physical.p head)
    localFixed =
      subst
        (λ kNorm →
          headMass
          ≤ two * kNorm * Frame.modeEnergy system (Physical.p head)
            + two * modeDissipation system (Physical.p head))
        (cong (modeNorm E) headK)
        (subst
          (headMass ≤_)
          (solve
            ( modeNorm E (Physical.k head)
            ∷ modeNorm E (Physical.p head)
            ∷ Frame.modeEnergy system (Physical.p head)
            ∷ []))
          localScaled)
    tailOutput : ∀ tau → tau Cube.∈ tail → Physical.k tau ≡ output
    tailOutput tau member = allOutput tau (Cube.there member)
    tailBound = rawCanonicalQFixedOutputBound system output tail tailOutput
    combined = ℚP.+-mono-≤ localFixed tailBound
  in
  subst
    (λ upper → rawCanonicalQSum system (head ∷ tail) ≤ upper)
    (solve
      ( two
      ∷ modeNorm E output
      ∷ Frame.modeEnergy system (Physical.p head)
      ∷ modeDissipation system (Physical.p head)
      ∷ rawPEnergy system tail
      ∷ rawPDissipation system tail
      ∷ []))
    combined

fixedOutputCanonicalQEnergyDissipationBound :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (output : Z3.FourierMode) →
  Sum.canonicalQSum system
    (Support.classifiedPhysicalOutputFiber (Audit.cutoff system) output)
  ≤
    two * modeNorm (Audit.integerEmbedding system) output * Frame.cutoffEnergy system
    + two * cutoffDissipation system
fixedOutputCanonicalQEnergyDissipationBound system output =
  let
    fibre = Output.physicalOutputFiber (Audit.cutoff system) output
    first = rawCanonicalQFixedOutputBound
      system output fibre (λ tau member → Output.physicalOutputFiberSound member)
    eRestriction = fixedOutputPEnergyBelowCutoffEnergy system output
    dRestriction = fixedOutputPDissipationBelowCutoffDissipation system output
    firstFactorNN =
      let
        instance
          twoNN = Data.Rational.Base.nonNegative twoNonnegative
          kNN = Data.Rational.Base.nonNegative
            (modeNormNonnegative (Audit.integerEmbedding system) output)
      in ℚP.nonNegative⁻¹
        (two * modeNorm (Audit.integerEmbedding system) output)
    eScaled =
      let instance factorNN = Data.Rational.Base.nonNegative firstFactorNN
      in ℚP.*-monoˡ-≤-nonNeg
        (two * modeNorm (Audit.integerEmbedding system) output)
        eRestriction
    dScaled =
      let instance twoNN = Data.Rational.Base.nonNegative twoNonnegative
      in ℚP.*-monoˡ-≤-nonNeg two dRestriction
  in
  ℚP.≤-trans first (ℚP.+-mono-≤ eScaled dScaled)

staticRationalOverlayChargeEnergyDissipationBound :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (output : Z3.FourierMode)
    (commutatorValue : Z3.FourierMode → ℚ)
    (hh : Fine.HHOwnerSelection) →
  Effective.concentrationCharge
    (Overlay.twoChannelFactors
      (Static.staticRationalTwoChannelOverlay
        system output commutatorValue hh))
  ≤
    two * modeNorm (Audit.integerEmbedding system) output * Frame.cutoffEnergy system
    + two * cutoffDissipation system
staticRationalOverlayChargeEnergyDissipationBound
    system output commutatorValue hh =
  let
    classified = Support.classifiedPhysicalOutputFiber (Audit.cutoff system) output
    pairing = Static.staticRationalPhysicalPairing system output commutatorValue
    exact = Sum.factorChargeFromClassifiedExact
      system pairing hh classified (λ selected → refl)
    physical = fixedOutputCanonicalQEnergyDissipationBound system output
  in
  subst
    (_≤
      two * modeNorm (Audit.integerEmbedding system) output * Frame.cutoffEnergy system
      + two * cutoffDissipation system)
    (sym exact)
    physical

round75CanonicalQControlledByEnergyAndDissipation : Bool
round75CanonicalQControlledByEnergyAndDissipation = true

round75CanonicalQNoRawCardinalityOrCutoffSquareTax : Bool
round75CanonicalQNoRawCardinalityOrCutoffSquareTax = true

round75StaticOverlayChargeEnergyDissipationBoundConstructed : Bool
round75StaticOverlayChargeEnergyDissipationBoundConstructed = true

round75StaticOverlayChargeEnergyDissipationBoundConstructedIsTrue :
  round75StaticOverlayChargeEnergyDissipationBoundConstructed ≡ true
round75StaticOverlayChargeEnergyDissipationBoundConstructedIsTrue = refl
