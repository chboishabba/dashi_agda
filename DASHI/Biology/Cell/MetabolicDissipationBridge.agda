module DASHI.Biology.Cell.MetabolicDissipationBridge where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; subst)

import DASHI.Energy.Core as EC
import DASHI.Analysis.DissipationPathMonotonicity as DPM
import DASHI.Biology.Cell.OpenMetabolicNetwork as OMN

------------------------------------------------------------------------
-- Metabolic adapter for an exact dissipation identity.
--
-- The energy carrier may later be instantiated by thermodynamic free energy,
-- relative entropy, or another physically justified Lyapunov quantity.  The
-- bridge does not identify any such quantity with MDL by default.
------------------------------------------------------------------------

record MetabolicDissipationBridge
    {e : Level}
    (N : OMN.OpenMetabolicNetwork)
    (Energy : Set e)
    (ES : EC.EnergySpace
      (OMN.OpenMetabolicNetwork.NetworkState N)
      Energy)
    : Set (lsuc e) where
  field
    environment :
      OMN.OpenMetabolicNetwork.Environment N

    dissipative :
      DPM.DissipativeTransition ES
        (OMN.OpenMetabolicNetwork.Reaction N)

    stepMatchesNetwork :
      (reaction : OMN.OpenMetabolicNetwork.Reaction N) →
      (state : OMN.OpenMetabolicNetwork.NetworkState N) →
      DPM.step dissipative reaction state
        ≡ OMN.OpenMetabolicNetwork.step N environment reaction state

open MetabolicDissipationBridge public

metabolicReactionEnergyDescends :
  ∀ {e N Energy ES} →
  (B : MetabolicDissipationBridge {e} N Energy ES) →
  (reaction : OMN.OpenMetabolicNetwork.Reaction N) →
  (state : OMN.OpenMetabolicNetwork.NetworkState N) →
  EC.Preorder._≤_ (EC.EnergySpace.P ES)
    (EC.EnergySpace.energy ES
      (OMN.OpenMetabolicNetwork.step N (environment B) reaction state))
    (EC.EnergySpace.energy ES state)
metabolicReactionEnergyDescends {ES = ES} B reaction state =
  subst
    (λ left →
      EC.Preorder._≤_ (EC.EnergySpace.P ES)
        left
        (EC.EnergySpace.energy ES state))
    (cong
      (EC.EnergySpace.energy ES)
      (stepMatchesNetwork B reaction state))
    (DPM.transitionEnergyDescends (dissipative B) reaction state)

runMetabolicDissipativePath :
  ∀ {e N Energy ES} →
  (B : MetabolicDissipationBridge {e} N Energy ES) →
  List (OMN.OpenMetabolicNetwork.Reaction N) →
  OMN.OpenMetabolicNetwork.NetworkState N →
  OMN.OpenMetabolicNetwork.NetworkState N
runMetabolicDissipativePath B [] state = state
runMetabolicDissipativePath {N = N} B (reaction ∷ reactions) state =
  runMetabolicDissipativePath B reactions
    (OMN.OpenMetabolicNetwork.step N (environment B) reaction state)

metabolicPathEnergyDescends :
  ∀ {e N Energy ES} →
  (B : MetabolicDissipationBridge {e} N Energy ES) →
  (reactions : List (OMN.OpenMetabolicNetwork.Reaction N)) →
  (state : OMN.OpenMetabolicNetwork.NetworkState N) →
  EC.Preorder._≤_ (EC.EnergySpace.P ES)
    (EC.EnergySpace.energy ES
      (runMetabolicDissipativePath B reactions state))
    (EC.EnergySpace.energy ES state)
metabolicPathEnergyDescends {ES = ES} B [] state =
  EC.Preorder.refl (EC.EnergySpace.P ES)
    (EC.EnergySpace.energy ES state)
metabolicPathEnergyDescends {N = N} {ES = ES}
    B (reaction ∷ reactions) state =
  EC.Preorder.trans (EC.EnergySpace.P ES)
    (metabolicPathEnergyDescends B reactions
      (OMN.OpenMetabolicNetwork.step N (environment B) reaction state))
    (metabolicReactionEnergyDescends B reaction state)

record MetabolicDissipationCertificate
    {e : Level}
    {N : OMN.OpenMetabolicNetwork}
    {Energy : Set e}
    {ES : EC.EnergySpace
      (OMN.OpenMetabolicNetwork.NetworkState N)
      Energy}
    (B : MetabolicDissipationBridge N Energy ES)
    : Set (lsuc e) where
  field
    genericCertificate :
      DPM.DissipationMonotonicityCertificate (dissipative B)

    reactionDescent :
      (reaction : OMN.OpenMetabolicNetwork.Reaction N) →
      (state : OMN.OpenMetabolicNetwork.NetworkState N) →
      EC.Preorder._≤_ (EC.EnergySpace.P ES)
        (EC.EnergySpace.energy ES
          (OMN.OpenMetabolicNetwork.step N (environment B) reaction state))
        (EC.EnergySpace.energy ES state)

    pathDescent :
      (reactions : List (OMN.OpenMetabolicNetwork.Reaction N)) →
      (state : OMN.OpenMetabolicNetwork.NetworkState N) →
      EC.Preorder._≤_ (EC.EnergySpace.P ES)
        (EC.EnergySpace.energy ES
          (runMetabolicDissipativePath B reactions state))
        (EC.EnergySpace.energy ES state)

open MetabolicDissipationCertificate public

certifyMetabolicDissipation :
  ∀ {e N Energy ES} →
  (B : MetabolicDissipationBridge {e} N Energy ES) →
  MetabolicDissipationCertificate B
certifyMetabolicDissipation B = record
  { genericCertificate =
      DPM.certifyDissipationMonotonicity (dissipative B)
  ; reactionDescent = metabolicReactionEnergyDescends B
  ; pathDescent = metabolicPathEnergyDescends B
  }
