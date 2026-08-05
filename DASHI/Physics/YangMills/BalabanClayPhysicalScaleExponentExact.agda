module DASHI.Physics.YangMills.BalabanClayPhysicalScaleExponentExact where

------------------------------------------------------------------------
-- PRIMARY CONTEXT
--
-- Arthur Jaffe and Edward Witten,
-- "Quantum Yang-Mills Theory", in The Millennium Prize Problems,
-- Clay Mathematics Institute / American Mathematical Society (2006).
-- No DOI is assigned to the problem description used here.
--
-- DASHI CONTRIBUTION
--
-- A lattice decay exp(-m_lat n) becomes a physical decay at distance a*n
-- only after proving m_phys*a <= m_lat uniformly in the cutoff.  The theorem
-- below proves the exact ordered-algebra transport and then applies any
-- antitone decay envelope.  This makes physical-units survival a standalone
-- producer rather than an informal rescaling remark.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel

record OrderedScaleAlgebra : Set₁ where
  field
    Carrier : Set
    multiply : Carrier → Carrier → Carrier
    LessEqual : Carrier → Carrier → Set
    lessEqualTransitive : ∀ {a b c} →
      LessEqual a b → LessEqual b c → LessEqual a c
    multiplyRightMonotone : ∀ right {a b} →
      LessEqual a b → LessEqual (multiply a right) (multiply b right)
    multiplyAssociative : ∀ first second third →
      multiply (multiply first second) third
      ≡ multiply first (multiply second third)

open OrderedScaleAlgebra public

physicalDistance :
  (algebra : OrderedScaleAlgebra) →
  Carrier algebra → Carrier algebra → Carrier algebra
physicalDistance algebra spacing latticeSeparation =
  multiply algebra spacing latticeSeparation

latticeDecayExponent :
  (algebra : OrderedScaleAlgebra) →
  Carrier algebra → Carrier algebra → Carrier algebra
latticeDecayExponent algebra latticeMass latticeSeparation =
  multiply algebra latticeMass latticeSeparation

physicalDecayExponent :
  (algebra : OrderedScaleAlgebra) →
  Carrier algebra → Carrier algebra → Carrier algebra → Carrier algebra
physicalDecayExponent algebra physicalMass spacing latticeSeparation =
  multiply algebra physicalMass
    (physicalDistance algebra spacing latticeSeparation)

physicalMassScaleBridge :
  ∀ {algebra physicalMass spacing latticeMass latticeSeparation} →
  LessEqual algebra
    (multiply algebra physicalMass spacing)
    latticeMass →
  LessEqual algebra
    (physicalDecayExponent algebra physicalMass spacing latticeSeparation)
    (latticeDecayExponent algebra latticeMass latticeSeparation)
physicalMassScaleBridge
    {algebra} {physicalMass} {spacing} {latticeMass} {latticeSeparation}
    scaleBound =
  subst
    (λ lower →
      LessEqual algebra lower
        (multiply algebra latticeMass latticeSeparation))
    (multiplyAssociative algebra physicalMass spacing latticeSeparation)
    (multiplyRightMonotone algebra latticeSeparation scaleBound)

record AntitoneDecayEnvelope
    (algebra : OrderedScaleAlgebra) : Set₁ where
  field
    Bound : Set
    BoundLessEqual : Bound → Bound → Set
    envelope : Carrier algebra → Bound
    envelopeAntitone : ∀ {smaller larger} →
      LessEqual algebra smaller larger →
      BoundLessEqual (envelope larger) (envelope smaller)

open AntitoneDecayEnvelope public

latticeEnvelopeImpliesPhysicalEnvelope :
  ∀ {algebra}
    (decay : AntitoneDecayEnvelope algebra)
    {physicalMass spacing latticeMass latticeSeparation} →
  LessEqual algebra
    (multiply algebra physicalMass spacing)
    latticeMass →
  BoundLessEqual decay
    (envelope decay
      (latticeDecayExponent algebra latticeMass latticeSeparation))
    (envelope decay
      (physicalDecayExponent algebra physicalMass spacing latticeSeparation))
latticeEnvelopeImpliesPhysicalEnvelope decay scaleBound =
  envelopeAntitone decay (physicalMassScaleBridge scaleBound)

record UniformPhysicalScaleClustering
    (Cutoff : Set)
    (algebra : OrderedScaleAlgebra) : Set₁ where
  field
    physicalMass : Carrier algebra
    spacing latticeMass : Cutoff → Carrier algebra
    scaleBridge : ∀ cutoff →
      LessEqual algebra
        (multiply algebra physicalMass (spacing cutoff))
        (latticeMass cutoff)

open UniformPhysicalScaleClustering public

uniformPhysicalExponentAtEveryCutoff :
  ∀ {Cutoff algebra}
    (dataSet : UniformPhysicalScaleClustering Cutoff algebra)
    cutoff latticeSeparation →
  LessEqual algebra
    (physicalDecayExponent algebra
      (physicalMass dataSet) (spacing dataSet cutoff) latticeSeparation)
    (latticeDecayExponent algebra
      (latticeMass dataSet cutoff) latticeSeparation)
uniformPhysicalExponentAtEveryCutoff dataSet cutoff latticeSeparation =
  physicalMassScaleBridge (scaleBridge dataSet cutoff)

physicalScaleExponentTransportLevel : ProofLevel
physicalScaleExponentTransportLevel = machineChecked

uniformPhysicalMassScaleBridgeInputsLevel : ProofLevel
uniformPhysicalMassScaleBridgeInputsLevel = conditional
