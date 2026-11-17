# Smith/Filsinger — actual Agda formalisation/weld maximum cut
**17 November 2026. Explicit correction:** the prior 99 Python tests and source-first numerical examples did *not* fulfill the requested *formalisation/weld* task. This pass creates proof-bearing **Agda consumers**, not simulations.

## Source-first imports, no duplicated theorem authorities

The new code is on PR #1524 (draft), and reuses:
- DASHI/Physics/Motors/Circuit36927RecoveryEnergyBoundExact.agda — canonical finite Nat work order, upper-bound transport and monotonicity.
- DASHI/Physics/Motors/SmithFilsingerTimeIndexedTransferExact.agda — original source families and finite causal-flight witness; a time-indexed receipt is NOT continuous spatial Maxwell.
- DASHI/Physics/Motors/SmithFilsingerReflectedPortBidiExact.agda — distinct filmed Earth circuit, unbuilt portable proposal and Smith source families, reciprocal reflected port admission (uninhabited).
- DASHI/Physics/Motors/SmithFilsingerMidpointPhaseWorkExact.agda — **signed** separate natural/driver incident/outgoing work and original finite same-boundary conservation, independent of acoustic output or phase.
- DASHI/Physics/Motors/SmithFilsingerFinitePhaseMatchingExact.agda — exact finite complementary phase identities, natural-source-off negative control; no golden matching assumption.
- DASHI/Physics/Motors/SmithFilsingerReplenishedCycleCapExact.agda — repeatable full-store return and independently admitted source cap.
- DASHI/Physics/Motors/SmithFilsingerSunEarthCoupledSourceExact.agda — original source study/evidence tiers and the port/source ontology; literature's cloud observation is not a controlled manipulation.
- DASHI/Promotion/MaxwellExteriorCalculusAdapter.agda — canonical F=dA, dF=0 symbolic homogeneous equation and **authority-bound** metric/Hodge/current/empirical terms.

PR #1521's SmithFilsingerDispersiveMaterialPortExact.agda and source admittance (not merged onto #1524) remain distinct donors; this branch does **not** import their path speculatively. Integration should use their actual normalized energy laws after the branch bases converge, not pretend these PRs' sources are one checkout.

## New owner 1: signed Maxwell → finite source/receiver port

DASHI/Physics/Motors/SmithFilsingerSourceMaxwellBoundaryWeldExact.agda

### Typed provenance rather than string labels

The dependent SourceOwner relation only constructs:
- Filsinger original Earth narration ↔ Filsinger Earth source owner;
- separately proposed portable plate ↔ Filsinger portable source owner;
- Smith suitcase figure ↔ Smith compiled / Kelly–Darrer historical source owners.

The typed SelectedBoundary is *indexed* by this owner relation, a declared natural source-port kind, the source regime (coherent wave vs independent DC vs nonlinear memory), and **internal branch phase versus independently referenced environmental phase**. Consequently it is not valid to silently attach a portable-plate proof to the Earth filmed circuit. Source type is necessary, not a proof of its existence.

### Actual imported evidence needed to couple fields to work

FormalFieldToPort b has:
- the original MaxwellExteriorCalculusAdapter object, which **does not claim its physical inhomogeneous Maxwell/Hodge/current equations were solved**;
- an existing RetardedFlight with launch+duration=arrival;
- a selected MidpointTwoPortWorkWindow with explicit signed boundary balance;
- *uninhabited* original source-current, causal material-response and Poynting-to-terminal-work equality evidence obligations, not a guessed atmospheric source.

SignedSourceCycleWeld b f demands the existing repeatable cycle + independent natural-source cap, **and additionally**:
1. natural incident = natural outgoing + natural **net** real input;
2. controller incident = controller outgoing + controller **net** real input;
3. exact same-original useful-load and heat/loss port equality to the original finite ledger;
4. full local stored-state return;
5. the pre-existing independently source-qualified physical evidence record.

None of these original-world physical evidence fields has been populated by audio spectra, capacitor display or atmospheric paper values. Choosing source port identifiers does not establish independent positive work.

### Real proofs, not copied fields

**signedPortBalanceAfterFullStoreReturn** is a general Nat semiring theorem taking the *existing signed two-port boundary equation*, independently evidenced source/controller incident-minus-outgoing laws, and restored storage. The proof uses exact polynomial rearrangement in the repo's canonical Data.Nat.Solver and cancellation from SmithFilsingerReplenishedCycleCapExact:

\[
(n_{\rm in}+c_{\rm in})+U_i
=W_{\rm load}+W_{\rm loss}+(n_{\rm out}+c_{\rm out}+U_f),
\quad U_i=U_f,
\]

with the exact port laws

\[
n_{\rm in}=n_{\rm out}+n_{\rm net},\quad
c_{\rm in}=c_{\rm out}+c_{\rm net},
\]

therefore

\[
\boxed{n_{\rm net}+c_{\rm net}=W_{\rm load}+W_{\rm loss}}.
\]

This is the nontrivial previously missing *port → repeatable cycle* cancellation step; it is **derived, not assumed** as a second identical work ledger. It covers the nonnegative net-supplied regime, not arbitrary signed negative net work in an integer grid. For a physically signed bidirectional real-source operator, split flows into nonnegative incoming/outgoing or use an ordered additive group; do not silently generalise Nat subtraction.

**signedNaturalAndControllerWorkPaysSamePortLoad** instantiates the generic theorem with the imported MidpointTwoPortWorkWindow and the typed SameOriginal source/port equalities. **signedPortLoadBoundAfterStoreReturn** derives load <= natural net work + controller net work, independently of the earlier RepeatableSourceCycle balance field.

**sourceCapTransfersToSameOriginalPort** is a separate proof that transports the pre-existing independently admitted natural-access cap through the *same actual load* equality, yielding

\[
W_{\rm load,original}\le W_{\rm nat,cap}+W_{\rm controller,net}.
\]

**sourceOffExcludesPositiveNaturalNet** reuses rather than recodes the signed nature/off original owner: an empty natural incident port cannot have strictly positive net incoming natural power even if drive energy radiates outward at it. **fieldPortArrivalNotBeforeLaunch** imports the existing causality theorem; **complementaryFinitePhasesPreserveTotal** imports the actual discrete two-slot phase identity. **symbolicMaxwellIsNotPhysicalAdmission** proves the existing Maxwell adapter is still marked as *unpromoted*.

**What these proofs do not establish:** true continuous Maxwell well-posedness, selected physical Earth/plate geometry, positive-real natural source-admittance bound, actual positive environmental power, ionospheric independent generator, original actual phase/switch V/I, or measured material coefficients.

## New owner 2: formal F14 and F16 source-indexed causal welds

DASHI/Physics/Motors/SmithFilsingerCloudCausalWeldExact.agda

The original observational sources are typed by the existing study tier: both electric-field/raindrop and local cold-pool studies are **observedNaturalAssociation**. **associationIsNotIntervention** proves those tags are not a controlled-intervention receipt.

OriginalCloudInterventionWeld b f w uses the **same field, same original source, and same signed-port source-work boundary** as the first weld, and requires explicit causal arrows:

\[
\text{actual controller intervention}
\longrightarrow \text{measured cloud-field change}
\longrightarrow \text{controlled droplet response}
\longrightarrow \text{controlled rainfall change}
\longrightarrow \text{local cold-pool heat budget}.
\]

**controlledLocalCoolingRequiresAllCausalArrows** is the actual Agda composition proof; all arrow functions and a real controlled intervention are arguments within the receipt, not synthesized from a statistical correlation or weather simulator. A separate GlobalClimatePromotion record requires measured radiative forcing, global energy balance and climate counterfactual—local rain/cooling alone is insufficient.

**observationalCloudRainAssociationDoesNotWeld** proves a finite two-world impossibility: the same natural cloud field/rain observation is compatible with different controlled-rain effects. The proof is a no-confusion/injectivity obstruction over exact data constructors, not a made-up numerical rainfall coefficient.

OriginalElectricalRegimeWeld b f w is an **F14** physical admission requiring the same selected original pins, time-aligned electrical switching/source/load work and acoustic startup/hot/null/shutdown, plus a single material/field parameter set and same-object explanation. It cannot be constructed from F16 cloud studies.

## Exact gate readout: formal versus physical

| Gate | This formalisation's result | Strict original result |
|---|---|---|
| **F10** retarded nonlinear Maxwell energy | Source-indexed Maxwell adapter + explicit causal material/field/Poynting-to-port authority boundary, no hidden material work; imported F=dA and dF=0 | Open: full physical metric/Hodge/current/constitutive Poynting solution |
| **F13** original soil/ionosphere source | Typed source owner/port + independently admitted source cap + actual natural incident/outgoing work identification | Open: measured source operator, physical geometry and strength |
| **F14** same original regime | Source-indexed electrical/acoustic/switch/current/one-parameter evidence record | Open: original selected physical measurements and fit |
| **F15** positive replenished work | **Derived signed-port cancellation** + **original load <= independent natural cap + controller** | Open: physical net positive incoming natural power and full-store cycles |
| **F16** rain/cloud/cooling | Exact causal-arrow composition, tier discrimination and observational nonidentifiability | Open: controller→cloud and downstream measured interventions |
| **D1/D2** | No postulates/holes deliberately introduced; pinned Agda checker committed | Open: no Agda/Nix compiler in current runtime, no original empirical receipt |

### Kernel and scope

Run **scripts/check_smith_filsinger_formal_weld_agda29.sh** at the source-selected PR #1524 head on the pinned Agda 2.9 environment. It explicitly checks all dependency paths, rejects any new \`postulate\` or \`{!!}\` proof hole, and asks the existing repo-pinned Agda wrapper to type-check **both** new owner modules.

**Not checked here:** no available Agda/Nix executable, therefore no statement that these new Agda proof terms were kernel accepted. The prior 99/99 Python results do not verify this proof code. No ESD module was edited and the unpublished, unverified local welds should not be promoted to TOE golden import graph prematurely.

### Remaining maximum cut is now exact

1. **Kernel:** actually compile the two new Agda modules and fix any syntactic/elaboration holes while preserving source/owner identities; this is D1 and requires compiler execution.
2. **Physical F10/F13:** construct and import a *single selected*, parameterized causal Maxwell/material/soil/ionosphere model with independently calibrated source current and correctly signed Poynting surface; import the earlier #1521 dispersive material port when branches converge. Do not replace this with an arbitrary source work value.
3. **F14/F15:** instantiate the welded owner only from time-synchronous original pin-level and signed natural/controller/input/output stored-state work with independent environmental replenishment, then derive an actual same-device load/phase/hunting result.
4. **F16:** obtain an independently controlled device→cloud-field receipt and remaining causal precipitation/thermal arrows before asserting local cooling; a global-climate claim needs further independent forcing evidence.

**Takeaway:** the *formal* task is now no longer represented by plots, toy power gain or weather simulation. The missing portions are precisely the type-checked kernel and original-world admission witnesses, and the quantitative physical field/operator itself. Those are not derivable from the presently available corpus alone.


### Final F15 source-off theorem

The final Agda owner also proves noNaturalNetSourceMeansLoadAtMostController: on the exact same selected port, if the restored-cycle *net natural* input is zero, useful load work cannot exceed net controller work. This is derived by transporting the **already derived two-port signed bound** through the naturalWork=zero identity, not by postulating an absent source cap. The theorem leaves zero net incoming distinct from zero instantaneous field or lack of audio; and it does not claim an actual Filsinger controller/input measurement.

The SourceOwner relation additionally has absurd-pattern no-confusion witnesses earthReelCannotHavePortableProvenance, portableProposalCannotHaveEarthReelProvenance and smithFigureCannotHaveFilsingerEarthProvenance. These prohibit original-source identity swapping at the type level without equating physical components by anecdote.

**Kernel caveat unchanged:** none of these extra Agda theorem terms is accepted until the pinned repo-owned checker actually runs in an Agda 2.9 environment. Source scans are not a substitute for elaboration.


## Second Agda formal cut: Maxwell/material interface cancellation

**Task scope:** actual proof composition, not additional numerical simulations. New module [SmithFilsingerMaxwellMaterialEnergyCutExact.agda](../../DASHI/Physics/Motors/SmithFilsingerMaxwellMaterialEnergyCutExact.agda) reuses the already source-indexed Maxwell, signed port and cycle-cap owners. The #1521 dispersive material module is still a DIFFERENT unmerged branch and is NOT imported deceptively.

The dependent FieldMaterialEnergyWeld b f sourceCycle requires TWO independently supplied conservation witnesses on the SAME selected original source and receiver:
- FIELD: natural **net** source work + driver **net** work + field initial storage = field/material interface work + radiation/field loss + field final storage.
- MATERIAL: exact SAME internal field/material interface + separately paid material modulation + material initial storage = useful load + material dissipation + modulation recovery + final material storage.
- Equals the EXISTING sourceCycle natural **net** work, controller net work and same-original receiver load; additionally requires physical current/metric, retarded material Poynting and same physical pins/coefficients. None are inferred from phase, acoustic evidence or an arbitrary source parameter.

**Actual source-authored proof chain:**
1. cancelSharedInterface establishes the algebraic internal-port cancellation: if a=i+b and i+c=d then a+c=b+d, without double-counting field/material transfer.
2. fieldMaterialCombinedWork instantiates both separate energy identities and normalises the complete external system ledger.
3. fieldMaterialRepeatableWork cancels SUM OF field+material stored energy, requiring a full-store return, not simply a charged output capacitor.
4. fieldMaterialLoadBoundOnRepeatableCycle preserves both field and material loss and recovered modulation energy on the output side.
5. netNaturalUnderExistingAdmittedCap imports the existing actual-source cap and proves its transfer to the selected field natural net work.
6. fieldMaterialLoadBelowAdmittedCapPlusPaidModulation and sameOriginalMaterialCapWithControllerAndModulator combine these deductions and transport to the selected original load:
   W_original_load <= W_admitted_natural_cap + W_controller_net + W_paid_modulation.

No new physical fields or energy constants are invented. This is stronger than the earlier Nat cycle bound because the field/material interface is **proved to cancel** using two separately evidenced equations, and material modulation cannot masquerade as natural input.

**Kernel still OPEN:** scripts/check_smith_filsinger_formal_weld_agda29.sh now includes the third theorem owner. Agda 2.9/Nix unavailable in this environment: source authored and dependency signatures audited, but NO kernel acceptance. A physically calibrated Maxwell material/Poynting identity and the same-original #1521 source/receiver weld remain uninhabited; physical F10/F13/F14/F15/F16 remain OPEN. No ESD editing or TOE promotion.


## Direct canonical #1521 material-ledger import and same-original formal weld

**Reuse, not duplicate construction.** The exact original source bytes of DASHI/Physics/Motors/SmithFilsingerDispersiveMaterialPortExact.agda (PR #1521, Git blob fb4039927678b370f359b3151c1fc2a2286c33ab) are now on PR #1524, preserving the original author and code unchanged; retrieved Git blob SHA is IDENTICAL on both branches. The canonical owner is NOT rewritten, and a new consumer holds all additional proofs. This replaces the earlier declaration that a cross-branch import was impossible.

**New direct imported proof consumer:** DASHI/Physics/Motors/SmithFilsingerDispersiveMaterialWeldExact.agda. Existing proof owners: DispersiveMaterialPortExact.MemoryMaterialPortLedger, SourceMaxwellBoundaryWeldExact, MaxwellMaterialEnergyCutExact, ReplenishedCycleCapExact and Circuit36927RecoveryEnergyBoundExact. It establishes these source-authored theorems:

- donorAllStoresReturn: if both the original material donor's environment storage and local storage return individually, their combined store returns.
- donorReorderInputs/donorReorderOutputs: exact Nat polynomial normalisation of the ORIGINAL #1521 fullBalance, not a replacement equation.
- originalDispersiveRepeatableWork: using the source owner's actual MemoryMaterialPortLedger.fullBalance, proves source recharge + driver + material modulator input = useful load + resistive/relaxation heat + feed loss + modulator recovery when BOTH stored states return, by exact cancellation.
- originalDispersiveLoadBound: useful load bounded by those paid inputs from that derived equation.
- CanonicalDispersiveSameObject b f s w: a source-indexed record requiring the ORIGINAL Mat.SameOriginalAdmittanceAdmission witness and exact equalities of donor natural recharge to previously signed **net** natural work, paid driver, modulation input, modulation recovery, actual load and field/material losses. Requires separately witnessed environment and local storage return.
- donorOriginalLoadIsPaid: transports the original material donor's derived bound to the same selected original receiver useful load, without assuming its previous aggregate cycle equation.
- donorOriginalLoadBelowAdmittedNaturalCap: a second cross-owner theorem, bounding that original load by independent natural-source cap + **net** controller input + explicitly paid material modulation.

These are genuine formal join points, not a numerical source scenario. The original upstream source cap, source current/Poynting boundary and physical same-original witness remain EXTERNAL proof premises, so no claim that Filsinger's apparatus has a positive natural supply follows. The signed Nat-grid branch assumes nonnegative net natural work: arbitrary reverse power needs an ordered additive group or a pair-of-naturals representation.

**Kernel:** the pinned formal checker now targets FOUR consumers (source Maxwell, cloud causal, Maxwell material interface cut, canonical dispersive material weld) and checks original donor import. Agda 2.9/Nix unavailable to run here; all added theorem bodies are SOURCE-AUTHORED, not kernel-accepted. The unchanged donor's matching blob is evidence of attribution and reproducibility, not proof correctness. Physical F10/F13/F14/F15/F16 and D1 remain OPEN.

**Max-cut next:** a physically parameterised original Maxwell/material/port construction must inhabit the exact same-source field energy, nonlinear constitutive and signed flux equations, not choose their numeric values. The two mathematical joins are now authored; pin-level and environmental source measurements and actual Maxwell Hodge/inhomogeneous field source law still cannot be derived from the repository's symbolic exterior-calculus inventory.
