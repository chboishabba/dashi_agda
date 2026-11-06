module DASHI.Moonshine.Y443JMDFromRelatorsToPowerExact where

------------------------------------------------------------------------
-- The source-written Y443 group relator list supplies x4^2=1 AND
-- all four x4/beta nonadjacent commutations.
--
-- The only group-algebra premise left for JMD's initial w^5/w^6
-- segment is beta^5=1: the four-node A4 Coxeter-path element lemma.
--
-- The original Lean proof establishes beta^5=1 using
-- pathCoxeterElement_pow_length_succ p2; native Agda path-Coxeter
-- reconstruction or a checked cross-prover witness is still needed.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
import DASHI.Moonshine.Y443CoxeterPresentationExact as Y
import DASHI.Moonshine.Y443VNaturalPairGenerationExact as Pair
import DASHI.Moonshine.TwistedModuleModularity as TM
import DASHI.Moonshine.Y443JMDSourceWordInstantiationExact as JMD
import DASHI.Moonshine.Y443JMDTracePowerExact as Power
import DASHI.Moonshine.Y443JMDPowerFiveSixAlgebraExact as Algebra
import DASHI.Moonshine.Y443JMDConcretePairPowerCompilerExact as Compiler
import DASHI.Moonshine.Y443JMDNonadjacentRelatorConsequencesExact as Relations

record JMDBetaOrderFive
  {G : Set} (gi : TM.GroupWithInverse G) (nodes : Y.Node → G) : Set where
  field
    fifthPower :
      Power.groupPower gi (JMD.betaElement gi nodes) 5 ≡ Pair.identity gi

open JMDBetaOrderFive public

powerFromActualEightyRelators :
  ∀ {G} (gi : TM.GroupWithInverse G) (nodes : Y.Node → G) →
  Pair.RelatorsSatisfied gi nodes Y.monsterRelators →
  JMDBetaOrderFive gi nodes →
  Compiler.JMDConcretePowers gi nodes
powerFromActualEightyRelators gi nodes relators betaProof =
  Algebra.deriveConcretePowers gi nodes
    record
      { Algebra.x4Square =
          Relations.SourceConsequences.e1Squared gi nodes relators
      ; Algebra.betaOrderFive = fifthPower betaProof
      ; Algebra.x4CommutesBeta =
          Relations.SourceConsequences.e1CommutesBeta gi nodes relators
      }

x4InJMDPairFromActualRelators :
  ∀ {G} (gi : TM.GroupWithInverse G) (nodes : Y.Node → G) →
  (relators : Pair.RelatorsSatisfied gi nodes Y.monsterRelators) →
  (betaProof : JMDBetaOrderFive gi nodes) →
  Pair.RepresentedByPair gi
    (JMD.uElement gi nodes) (JMD.vElement gi nodes)
    (nodes JMD.x4)
x4InJMDPairFromActualRelators gi nodes relators betaProof =
  Compiler.sourceX4Word gi nodes
    (powerFromActualEightyRelators gi nodes relators betaProof)

betaInJMDPairFromActualRelators :
  ∀ {G} (gi : TM.GroupWithInverse G) (nodes : Y.Node → G) →
  (relators : Pair.RelatorsSatisfied gi nodes Y.monsterRelators) →
  (betaProof : JMDBetaOrderFive gi nodes) →
  Pair.RepresentedByPair gi
    (JMD.uElement gi nodes) (JMD.vElement gi nodes)
    (JMD.betaElement gi nodes)
betaInJMDPairFromActualRelators gi nodes relators betaProof =
  Compiler.sourceBetaWord gi nodes
    (powerFromActualEightyRelators gi nodes relators betaProof)
