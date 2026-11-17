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


### Strongest joint theorem: transfer the actual donor storage receipts

The canonical cross-PR record now additionally equates **both initial and final** upstream environment storage and local material storage with the selected #1524 field/material split. This blocks false "same-object" matches that equate only total output while silently changing a donor state.

New exact Agda source terms:
- donorStorageReturnTransfersToSplit: derives simultaneous return of the field and material inventories using the **actual** #1521 environment/local storage returns and four same-original identity witnesses. It does NOT ask the caller to separately assert the split restoration.
- canonicalDispersiveFieldLoadBelowNaturalCap: directly instantiates the two-law Maxwell/material internal-interface cancellation and independent natural-source cap using this *derived* field/material storage return. Inferred selected original load is bounded by natural cap + net powered work + paid modulator work.

This cuts the dependency chain in a materially stronger way:

  ORIGINAL #1521 MemoryMaterialPortLedger fullBalance
  + its environmental and material storage restoration
  + 4 cross-ledger storage identity witnesses
  + 3 separate source/driver/load identity witnesses
  + #1524 Maxwell field/material internal work cancellation
  + source-selected independently admitted net natural cap
  -----------------------------------------------------------------
  SAME selected original useful load <= natural cap + controller + modulator.

**All source/current, constitutive PDE, original material and physical net power receipts remain obligations**, not inferred. This is a conditional formal mathematical connection that still requires pinned Agda 2.9 type-checking and empirical boundary admission.


## Max-cut continuation: reuse original 3-component Maxwell and all-N spatial port owners

**17 November 2026; specifically requested formalisation/welds, NOT simulations.** A repo-wide search found two existing higher-value mathematically explicit Agda owners which the initial Smith/Filsinger proof graph had failed to import:

- DASHI/Physics/Plasma/KSW668FullVectorMaxwellJetExact.agda, original KSW 668 B1 producer. It defines an actual three-component electric/magnetic/current derivative jet with Faraday and Ampere equations; exact pointwise fullVectorMaxwellPoyntingIdentity proves time-field-energy derivative + spatial Poynting divergence + J dot E = zero. This is a **genuine vector curl-jet algebraic theorem**, not a Maxwell PDE existence/uniqueness or a physical surface integral.
- DASHI/Physics/Motors/SmithFilsingerSpatialPortChainExact.agda, concurrent original all-N spatial chain producer. Its spatialChainWorkBalance proves conservation for arbitrary connected cells with shared internal source/receiver transfers canceled. Internal outgoing edges are not counted as independent natural energy, and the exterior positive/negative budget distinction is retained.

**New actual proof consumer 1:** DASHI/Physics/Motors/SmithFilsingerFullVectorPoyntingPortWeldExact.agda. It imports the *original* KSW vector theorem and the existing selected source/work algebra; it does NOT invent a new Maxwell jet.
- threeComponentPoyntingFromOriginalMaxwell: exact delegated source proof from the original curl-jet owner.
- MaxwellJetToSelectedFieldWork: a deliberately separate, **uninhabited physically integrated boundary implication** from pointwise local conservation to actual selected natural/controller net source work, field-to-material transfer and field outgoing loss. Spatial/time integration, orientation, constitutive currents, actual source identity and radiation need evidence; not an unproved immediate implication.
- fieldWorkFromMaxwellJetAndIntegration: applies the original pointwise theorem to that independently supplied physical field/port map.
- fullVectorMaxwellToMaterialCompleteLedger: composes the selected vector Maxwell identity plus a separately proved material/receiver energy equation and imports the existing cancelSharedInterface, eliminating internal transfer and deriving full combined external work including material modulation/recovery and all stored energy.
- sameOriginalFullVectorPoyntingNaturalCap: derives the original-port useful-load bound from the Maxwell bridge, material work, complete storage return and an independent natural cap.
- selectedSourceFullVectorMaxwellCap: **tightens** the general theorem to the same already-selected SignedSourceCycleWeld, fixing natural and controller input to its actual **net** source ledger and natural cap to its existing independently admitted value. No generic arbitrary source power can be silently instantiated.

**New actual proof consumer 2:** DASHI/Physics/Motors/SmithFilsingerSpatialSourceCapWeldExact.agda.
- reorderSpatialInput and reorderSpatialOutput use the canonical Data.Nat.Solver.
- spatialChainNetSourceWork derives NATURAL NET input + all distributed controller inputs = all useful loads + all dissipation for arbitrary N, from the original all-N chain theorem, the first/last net boundary equation and **full chain stored-state restoration**. All internal transfers cancel exactly.
- spatialChainLoadBelowNetSourceAndController and selectedOriginalAllSpatialCellsBelowNaturalCap transport this derived bound to the *same* source-selected original receiver, admitted natural source cap and original controller net work. Original empirical input/output equality and source identity are explicitly demanded, not guessed.

### Gate audit after proof reuse

| Gate | New formal advancement | Strict still-open bridge |
|---|---|---|
| **F10** | original three-component Maxwell curl-jet and exact pointwise Poynting imported, no duplicated vector PDE algebra | Real field with spatiotemporal regularity, constitutive polarization/plasma currents, PDE existence and Poynting surface/time integration |
| **F13** | physical Maxwell-jet-to-source/terminal *typed implication*; all-N interior port cancellation | Same-original calibrated net exterior source work, source current, outgoing flux, geometry |
| **F14** | selected original net source/driver/load identities in all-N and vector Maxwell consumers | Actual original netlist, measured electrical clock and original joint acoustic/electrical states |
| **F15** | conditional cap on SAME selected useful output from both (1) differential pointwise full-vector + material work and (2) all-N spatial source chain; no internal flux double count | Physical source replenishment and storage-return readings, physically justified source cap |
| **F16** | prior observational-versus-causal formal obstruction retained; no weather-source promotion | Actual measured controller→cloud→rain effects |
| **D1** | pinned runner now lists SIX actual formal consumers plus existing vector Maxwell and all-N owners | No Agda/Nix executable available in this session; NO Agda-kernel acceptance or CI receipt |

**Numerical tests are not proof acceptance**. New source terms have no added postulate, but neither code-scan nor Git blob parity substitutes for pinned kernel checking; conditional field-operator and original-apparatus premises remain OPEN.

**Maximum-cut priority after this:** (a) pinned Agda compile/fix of six consumers; (b) physically valid spacetime/surface Poynting integration from KSW jet + real material field response into the same original electrode/receiver port; (c) source-selected fully replenished net work; (d) if original cloud-control interpretation is pursued, independent causal atmospheric interventions. Do NOT solve a new full 3D Maxwell PDE just to rederive an already-proven pointwise vector identity. No ESD edits, attribution to the original KSW vector producer and Smith/Filsinger source owners, no premature TOE promotion.


## Consistency gate: old signed cycle versus material-modulation work

The previous F15 signed-cycle ledger already asserted the ORIGINAL SAME selected load and net external controller+natural work, but the later field/material decomposition introduces a separately **paid material modulation input** and **recovered modulation output**. Absent explicit reconciliation, one might misstate both ledgers as simultaneous and hide or double-count material work.

New actual Agda theorem **materialModulationReconcilesOriginalCycleLoss** in SmithFilsingerMaxwellMaterialEnergyCutExact.agda imports the previously derived **signedNaturalAndControllerWorkPaysSamePortLoad** (from original incident/outgoing work + all-store return), imports **fieldMaterialRepeatableWork** (from independent Maxwell/material conservation with combined field/material store return), transports the SAME selected natural/controller/load port equalities, and cancels useful load. It derives exactly:

  W_original_signed_cycle_internal_loss + W_paid_material_modulator
    = W_field_radiative_loss + W_material_relaxation_loss
      + W_recovered_modulation.

This exposes a **new conditional consistency requirement** between #1521 and #1524 physical accounting partitions: externally paid modulator input cannot be renamed solar/Earth natural work, and recovered modulation cannot be silently dropped. A physically contradictory set of ledger receipts cannot both be inhabited unless their separate losses and modulation terms reconcile.

Further, the timed all-N spatial consumer **allTimedSelectedOriginalCellsBelowNaturalCap** now imports the existing TimedSpatialPortChainExact owner, erases its timing index into the existing all-N spatial conservation theorem without modifying the work data, and transports the same-original natural-source cap while **allTimedSelectedOriginalArrivalIsCausal** imports the exact finite launch<=arrival result. This is NOT a relativistic Maxwell signal-front result, and does not licence identifying an observed acoustic clock with the electrical controller.

**Remaining maximum cut:** the admitted Maxwell-jet pointwise-to-integral *physical* transport, original source+material constitutive identity and source-current/pin equality, and Agda 2.9 kernel acceptance; no more numerical simulation or duplicate algebraic power bounds is called for. The mathematical pointwise curl-jet and all-N spatial cancellation owners now exist and are consumed, not reinvented.


## Refinement: typed full-vector Maxwell admission rather than free Set placeholders

A second F10 pass strengthened SmithFilsingerFullVectorPoyntingPortWeldExact.agda. The original provisional SameOriginalPhysicalFieldBoundary had free evidence types which could be declared as arbitrary inhabitable Sets without proving equations. It has now been replaced by a dependent Agda record indexed by a real **FullVectorMaxwellJet F**, SelectedBoundary b, FormalFieldToPort f and original signed-cycle s. The fields contain the actual external source/driver and internal material/receiver work equations:

- MaxwellIntegrationIntoSelectedTerminal: explicitly consumes the original three-component pointwise Poynting equation and supplies a **physically independent domain/surface/time integration result**, with net natural/controller work drawn from the selected s, field storage, internal field-to-material transfer, outgoing field losses and final field storage;
- materialWorkLaw: requires exactly the SAME internal work transfer, paid modulation, initial/final material storage, useful load, relaxation dissipation and recovered modulation;
- allFieldAndMaterialStatesRestored: an equality of combined field and material stored energies, not a capacitor voltage proxy;
- originalUsefulPortIdentity: directly identifies the selected physical receiver useful load, preventing an unrelated source/receiver value substitution.

selectedFullVectorPhysicalAdmissionCap derives the original receiver load bound from this contentful record by consuming selectedSourceFullVectorMaxwellCap. No free arbitrary chosen Set witnesses can satisfy the required mathematical equalities just by selecting an empty or unit type. **This is still a conditional formal theorem**: a trivial zero-energy model could inhabit the equations, so *original physical provenance and measured source/work* remain external and cannot be claimed from a type constructor. The real Maxwell PDE solution and source current, physical surface integration, and actual device measurements remain OPEN.

**Separate mathematical consistency:** materialModulationReconcilesOriginalCycleLoss is added to the existing MaxwellMaterialEnergyCutExact owner and strictly derives that any paid modulation in the new material ledger must reconcile the losses and recovered modulation in the already-closed original signed cycle. This is especially important when comparing purported high-gain nonlinear field manipulation against a separately powered controller.

**Kernel status unchanged:** Agda and Nix unavailable locally. These are source-authored exact proof candidates and must not be reported as kernel accepted until the pinned check runs.


## Complete formal compositional diagram: full-vector Maxwell jets to all-N timed original ports

**Source-authored Agda consumer:** DASHI/Physics/Motors/SmithFilsingerMaxwellTimedSpatialWeldExact.agda. This is the shortest logically useful **actual formal weld**, not a simulation and not a new duplicate Maxwell or network algebra owner. It imports the already-present KSW668FullVectorMaxwellJetExact, TimedSpatialPortChainExact and SpatialSourceCapWeldExact.

### Type-level structure

- MaxwellTimedPath b f s first last start finish is a dependent all-N path **indexed by the selected original b**, its existing field/port f, and its same-original signed environmental cycle s. It has a zero-cell terminal and a constructor for a single physical link.
- Every physical link carries a **three-component Maxwell curl-jet with Ampere/Faraday equations** and an independently supplied implication from the original pointwise fullVectorSignedBudget = zero to an actual CausalSpatialCell. That target cell already contains a typed RetardedFlight and a local Poynting/work conservation receipt. The implication is the exact physical spacetime integration, orientation, constitutive and source/terminal identification obligation; it is NOT automatically constructed from an acoustic phase, scalar voltage, or arbitrary receiver.
- eraseMaxwellToTimedSpatial is the source-to-consumer compiler: it applies the original fullVectorMaxwellPoyntingIdentity for each link and uses its independently supplied field-to-cell integration witness to build the existing timed/spatial work chain. It preserves the selected original source b/f/s across all links.
- allIntegratedMaxwellCellsConserveWork is the inherited all-N network conservation theorem; allIntegratedMaxwellCellsRespectFlight is the inherited no-early-arrival finite causal theorem.
- allIntegratedMaxwellCellsBelowSelectedNaturalCap consumes the original natural NET first/last source boundary, selected same-original source work, controller work, useful receiver and full aggregate stored-state return, then invokes the previously derived allTimedSelectedOriginalCellsBelowNaturalCap. It yields selected original useful load <= independent natural-source cap + net controller work. No internal field-to-material/current transfer or outgoing radiation is classified as a new source.

### Dependency chain and exact remaining source gate

KSW original true 3-component Maxwell **pointwise curl jet**
  → REQUIRED independently proved physical field integral for EACH causal cell
  → TimedSpatialPortChainExact (arbitrary N, launch <= arrival)
  → SpatialPortChainExact (all shared internal flux cancels)
  → SpatialSourceCapWeldExact (outgoing environment not credited as incoming)
  → signed original source-identity and replenished-cycle cap
  → selected original load bound.

**Physical gate unchanged:** existence of a physically parameterized Maxwell/plasma/soil source-current field on the original device geometry, an integration/trace theorem with correct constitutive/material modulation and boundary conditions, independently replenished terminal source strength, and measured synchronous original hardware state. Any of these may fail. This is a conditional compositional theorem: it does not manufacture physical observations.

**Acceptance:** the exact pinned script now includes this new owner and its original imports. Agda/Nix are unavailable in this environment; none of this new source is claimed kernel-checked. Full, source-authored proofs are subject to the actual compiler's elaboration/type/universe constraints. No ESD modification; no TOE promotion before acceptance and attribution audit.


## D1 acceptance guard correction: explicit Agda holes must actually be detected

The pinned formal acceptance script previously contained a double-escaped grep ERE meant to reject Agda proof holes. A direct shell negative control showed that it DID NOT match the literal hole syntax {!!}: an explicit hole could pass that preflight.

The checker now uses grep -nF for literal {!!} and separately rejects explicit postulates and unsafe compiler pragmas that weaken proof obligations. A local fixture test was 4/4: clean source accepted; explicit hole, postulate and allow-unsolved-metas flag each rejected. This is proof-source integrity validation, not physical simulation and NOT Agda kernel checking.

The pinned runner still requires actual repo-owned Agda 2.9, with no Python proof substitute. No Agda/Nix binary is available in this environment and no exact-head GitHub workflow run has been verified; D1 remains OPEN. The local fixture result does NOT prove any theorem type-correct.


## 17 Nov highest-alpha correction: prove finite open Gauss and derive timed cells

The audit uncovered two specific mathematical and proof-checking issues, addressed on PR #1524 without numerical simulation:

1. **Syntax blocker** in SmithFilsingerMaxwellMaterialEnergyCutExact.agda: an unmatched closing parenthesis in the fieldMaterialRepeatableWork proof term. Fixed after a whole-file token/delimiter scan. The previously claimed source-level hole scan alone was not sufficient to establish syntactic readiness. Recheck of three modified modules found delimiter balance with no explicit postulates/holes; Agda elaboration is STILL NOT run.
2. **Vacuous integration interface** in MaxwellTimedSpatialWeldExact: the previous throughField accepted a function returning an already-assembled CausalSpatialCell, which could obscure where its work equation came from. Replaced with IntegratedFieldCell, an actual typed numeric signed work equation conditioned on the KSW pointwise Poynting identity, and a separate buildCausalCellFromMaxwell constructor that derives SpatialCell.work and the timed cell from that premise and the original flight receipt.

### New physically relevant *mathematical* finite Gauss cut

The source-first search discovered a pre-existing, exact rational forward-difference telescoping theorem in DASHI/Physics/YangMills/YangMillsLatticeStressWardSliceConservationExact.agda: differencePartialTelescopes. The Filsinger programme now reuses that canonical owner directly in:

**DASHI/Physics/Motors/SmithFilsingerOpenBoundaryPoyntingGaussExact.agda**

- OpenRectangularPoyntingFaces carries **cross-section-aggregated** signed rational face fluxes along x, y, z. This is *not* a claim that a scalar profile represents an arbitrary 3D physical vector field; the cross-section aggregation and metric orientation need source evidence.
- threeAxisFiniteDivergence is the sum of finite forward differences, NOT a continuous derivative.
- exteriorOrientedPoyntingFlux keeps the actual differences between the opposite external faces, with NO fictitious periodic-box cancellation.
- **finiteOpenBoundaryPoyntingGauss** proves the exact identity sum of discrete divergence = outward right-face flux minus left-face flux, summed for all three axes, simply by invoking the pre-existing Yang–Mills telescoping lemma once per axis. This is new cross-programme mathematical reuse; it is source-authored and still awaits pinned Agda acceptance.
- **originalFullVectorJetOpenBoundaryFlux** composes the existing KSW full-vector pointwise Poynting identity with the exact finite Gauss identity, requiring TWO independent physically meaningful receipts: the actual field/time spatial integration into the finite face divergence, and calibrated signed exterior flux to the same-original source port.
- **No field solution, actual atmosphere/soil source-current or real-device power can be inferred from these mathematical identities.** The KSW jet is pointwise, while the finite faces are rational sums. Their equality in the actual measurement units is a separately required physical integration/trace law.

### Direct continuation of the all-N timed physical chain

SmithFilsingerMaxwellTimedSpatialWeldExact.agda now also imports the open-Gauss owner. IntegratedOpenGaussCell has a real 3-vector Maxwell jet and OriginalMaxwellOpenFaceTrace, discrete retarded flight, local driver/stored/load/loss work and a **separate** rational exterior-flux-to-Nat work/unit calibration implication. **buildCausalCellFromOpenGauss** uses the original KSW pointwise result and original Yang–Mills finite Gauss proof to derive the required local SpatialCell.work and timed path. throughOpenGauss is a new constructor of MaxwellTimedPath; eraseMaxwellToTimedSpatial consumes it, and the existing all-N energy, causal-arrival and selected-original source-cap theorems apply without duplicate proof of the chain algebra.

This is a real proof *weld* but does NOT complete full F10 physical source-to-port: every cell's divergence-to-face quadrature and signed rational-to-original terminal calibration remain physical premises, as does full source replenishment. It is deliberately limited to cross-section-aggregated finite face fluxes; continuous Maxwell PDE, geometry, constitutive material relaxation and time integration are not proved by this Nat/ℚ algebra.

### Updated gate distinctions

| Target | New mathematical result | Open physical / kernel obstruction |
|---|---|---|
| F10a pointwise local vector Maxwell | Reuse canonical KSW FullVectorMaxwellJet exact identity | Real continuum source-current and constitutive field solution |
| F10b finite spatial divergence → exterior flux | NEW finiteOpenBoundaryPoyntingGauss reusing canonical YM Ward difference telescoping | Exact Agda 2.9 kernel acceptance; physical cross-section face trace and continuum integral |
| F10c exterior flux → physical terminal work | New typed OriginalMaxwellOpenFaceTrace + IntegratedOpenGaussCell + buildCausalCellFromOpenGauss | Physically justified signed port mapping and rational-to-Nat energy calibration |
| F13 all-N exterior net source | Existing SpatialPortChain, strengthened all-N cap and timed Maxwell path | Source identity, outgoing boundary flux, independently admitted natural source cap |
| F15 material/returned cycle | Exact field/material cancellation, #1521 donor reuse, materialModulationReconcilesOriginalCycleLoss; delimiter bug fixed | Actual all-state return and paid modulation/source evidence |
| F14/F16 original apparatus & weather | Existing source-indexed same-object and causal-arrow obligations remain | Original electrical work and independent atmosphere intervention |
| D1 | Source-integrity guard corrected, finite Gauss added to pinned checker, delimiter audit on three changed modules | Agda/Nix unavailable locally, no current kernel/CI acceptance |

**Highest-alpha remaining formal target:** independently justified field-to-boundary integration at the actual selected geometry and material law, with consistent units/signs and no implicit 3D continuum promotion. Do not reprove the YM finite difference telescope or KSW 3D curl jet. Verify this source with the repo-owned Agda 2.9 toolchain before naming any new kernel-closed theorem.


## 17 Nov signed-port completion and cross-branch real-field distinction

The original all-N Nat source-cap theorem was deliberately restricted to nonnegative NET environmental supply: naturalIncident = naturalOutgoing + naturalNet. That fails to represent a genuine environmental SINK, even if all fields and stores return. This is a mathematical modelling restriction, not a physical prohibition.

**New Agda source consumer** DASHI/Physics/Motors/SmithFilsingerSignedBoundaryGroupCompletionExact.agda imports the actual MidpointTwoPortWorkExact original signed incident/outgoing conservation law, Circuit36927RecoveryEnergyBoundExact and ReplenishedCycleCapExact. Rather than inventing negative Nats, it uses pairs of nonnegative directed work and exact cross-sum equality of their signed differences. This is a setoid **pre-quotient**, not a claim to have constructed a quotient type, a real-field measurement or a physical signed-power device.

Source-authored theorem bodies:
- sameSignedReflexive, sameSignedSymmetric and sameSignedTransitive: directed-work cross-sum equality is an equivalence.
- signedWorkInverseCancels and sameSignedAddCongruenceRight: pairing a flow with the opposite direction cancels, and adding the same directed flow respects equivalent net work.
- originalTwoPortSignedWorkConservation: from the actual original natural/controller incident and outgoing work plus full storage return, derive **signed** net environmental + controller work equals useful load + losses, WITHOUT presupposing naturalIncident >= naturalOutgoing.
- reverseEnvironmentalFlowConsumesControllerWork: if naturalOutgoing = naturalIncident + returnedEnvironmentalWork and controllerIncident = controllerOutgoing + controllerNet, original complete boundary law implies
    controllerNet = usefulLoad + internalLoss + returnedEnvironmentalWork.
- reverseEnvironmentalLoadPlusSinkBelowController and originalReverseEnvironmentalPortFundedByController: at the SAME source-selected original receiver, usefulLoad + returnedEnvironmentalWork <= controllerNet. Environmental sinks cannot be relabeled as natural power sources.

This is a genuine negative control. It prevents the earlier nonnegative-natural-cap theorem from accidentally being applied to a negative natural source. A separate source CAP still requires independent calibration; the signed-work theorem alone does not establish source access or real-world physics.

**Source-first deduplication audit:** other concurrent modules in #1524 now include SmithFilsingerSignedIndexedFaceFluxExact and SmithFilsingerIndexedSignedCellStokesExact (actual C3.RealField additive inverse with face IDs), plus SmithFilsingerSpaceTimePoyntingTelescopeExact (rational four-direction finite Poynting flux). These are MORE GENERAL at field-space and mesh-incidence levels; do not duplicate their real-field additive algebra. The newly introduced Nat-pair carrier is only the nonnegative metering/port interface needed to derive the original reverse-flow bound. The next remaining formal weld should carry an actual calibrated signed real-field / rational exterior flux to that discrete original terminal receipt with chosen units, not assert that the same numerical flux was measured.

**Verification gates:** new Agda source is hole/postulate-free by inspection, delimiter-balanced and Nat Solver arities are matched in a static audit. This is NOT a substitute for pinned Agda kernel elaboration. Strict F10/F13/F14/F15/F16 original physical and D1 verification gates remain open.


## Quantisation obstruction: exact integer signed meter cannot encode half a work quantum

The field/port sources in the same PR now include a mathematically signed C3.RealField indexed-face flux owner, a signed rational finite spacetime Poynting owner and the original Nat-grid terminal-work owner. A tempting but INVALID weld would require an exact globally additive conversion from all rational/real field work to an integer Nat-pair signed meter, with no rounding uncertainty.

**New Agda negative-control proof source:** in SmithFilsingerSignedBoundaryGroupCompletionExact.agda, doubleNatNormalization derives n+n = 2n for the canonical inductively defined doubleNat; doubleCannotBeOdd rules out 2a = 2b+1 by constructor induction; oneWorkQuantumHasNoExactSignedHalf lifts that impossibility to arbitrary signed directed-work pairs using cross-sum equality. This is a concrete obstruction: a nonzero field source quantum cannot be split into two equal rational halves and exactly encoded as two integer half-quanta while preserving addition. The theorem is **source-authored, not kernel-accepted**.

It does NOT prohibit accurate measurement. The valid next weld must either:
- retain signed rational/real energy through the exact spatial and temporal source flux algebra and introduce an explicitly stated discrete quantum lattice for the meter, OR
- construct interval/rounding-error receipts for the signed physical terminal measurement, where the total error accumulates under all-N conservation rather than being magically zero.

A trivially zero conversion from reals to integer work would be additive but would NOT preserve nonzero observed physical source power. Do not use it to claim source admission. A measured original source/port V-I integral is a separate physical witness.

The signed work branch also imports the actual original driverOnlyCanRadiateIntoEnvironment record, proving originalDriverOnlyReverseFlowIsPaid and originalDriverOnlySinkBound without constructing a new toy example. Source/field real-domain algebra stays owned by SignedIndexedFaceFluxExact, IndexedSignedCellStokesExact and SpaceTimePoyntingTelescopeExact. No duplicate real-field solver.

Agda/Nix and exact-head CI are still unavailable in this session. No new source-level mathematical theorem is claimed kernel accepted or a physical proof of Filsinger Earth power, an actual surface integral or cloud/rain intervention.


## Exact additive meter no-go under a half-divisible source carrier

**New source-authored formal consumer:** DASHI/Physics/Motors/SmithFilsingerSignedMeterQuantisationNoGoExact.agda. It imports the canonical SignedBoundaryGroupCompletionExact signed Nat-pair pre-quotient, the original oneWorkQuantumHasNoExactSignedHalf theorem and the existing MidpointTwoPortWorkExact contradiction owner. It does NOT create a new real-field or sign-flux algebra.

Theorem additiveExactMeterCannotSendHalvedUnitToOneQuantum is universe-polymorphic in any source carrier A with an operation plus, a half element h, a full element u and exact h plus h = u. If an integer signed-pair meter respects the source operation via cross-sum equivalence AND maps the full element to one integer quantum, its value at half would have to be half an odd integer, contradicting the original exact Nat-pair parity theorem. This is a formal argument against an unrestricted EXACT nonzero additive C3.RealField/rational -> integer-quanta bridge; it is NOT a theorem against approximate meters or discrete finite-lattice models.

The actual physics lane should use the existing C3.RealField indexed signed face algebra and rational SpaceTimePoyntingTelescopeExact source carriers, preserving the field metric, source-current and integrated Poynting identity. For comparison with Nat terminal energy, a future *independently calibrated* metering map must either have a declared discrete domain/quantum lattice or bounded interval/rounding uncertainty with summed error. Such a map has not yet been constructed and may fail to exist for the original device.

A GitHub update race was resolved by creating a **separate proof consumer**, avoiding overwrites in the signed boundary owner. The pinned script now lists the consumer. Agda/Nix remain unavailable locally, so all new proof bodies remain pending kernel type-check; no physical F10/F13/F14/F15/F16 source/weather claims are promoted.


## F10/F13 signed rational metering: canonical finite residual sums and two-sided certified bounds

**This pass continues the FORMALISATION / WELD, not numerical simulation.** The previous no-half-quantum theorem correctly blocks an unrestricted exact nonzero additive rational-to-integer Nat meter. The canonical signed rational field-work and source-window owners must therefore remain rational through integration and certification.

A repository-wide reuse search identified **DASHI/Core/ProofCarryingFiniteSumEnclosureExact.agda** (a reusable proof-carrying finite-sum/error aggregate and certified upper endpoint, already consumed by the RH programme). No new interval framework was written.

### New exact Agda proof consumer 1 — signed rational residual

DASHI/Physics/Motors/SmithFilsingerCertifiedSignedMeterResidualExact.agda:

- rationalAdditiveCarrier is the concrete Data.Rational.Base rational additive carrier for the existing generic proof-carrying finite-sum owner.
- FiniteSignedMeterWork certificate carries the **same** finite error terms, per-term physically calibrated signed actual work and observed rational work, and requires EACH equality actualTerm = meteredTerm + signedResidualTerm. The term samples cannot be silently selected from different apparatus clocks or port orientations.
- signedResidualsTelescope proves by induction and the existing rational ring solver that TOTAL actual work = TOTAL measured work + sum of the SAME signed per-term residuals. Errors accumulate algebraically, rather than being silently dropped or rounded to integer quanta.
- SelectedOriginalCertifiedMeter window requires this finite certificate, the measured term sum to be the original terminal reading, and the physically sourced term sum to equal the actual same-original 4D Poynting window useful receiver work. **These are substantive physical trace/calibration hypotheses, not derived Maxwell PDE or invented meter data.**
- originalUsefulReceiverEqualsMeterPlusResidual derives the actual selected original receiver work identity from those per-term laws, not by assuming a new aggregate energy equation.
- originalSignedResidualBelowCertifiedUpper imports the canonical finiteSumBelowCertifiedUpper, with the SAME exact residual sample collection; no arbitrary unrelated interval bound can be used.
- SignedMeterUpperMonotonicity adds only the necessary proof that the chosen certified order is stable under adding the actual observed work. originalReceiverBelowObservedPlusCertifiedResidual then derives receiverWork <= observedWork + certifiedUpper using equality transport. This is a conditional ordered theorem, not an empirical bound.

### New exact Agda proof consumer 2 — *two-sided* signed uncertainty

DASHI/Physics/Motors/SmithFilsingerCertifiedSignedMeterTwoSidedExact.agda:

- TwoSidedMeterCertificate w reuses the existing original certificate and independently supplies the canonical ProofCarryingFiniteSumEnclosure + ProofCarryingFiniteSumUpperEnclosure for the NEGATIVE residual.
- exactOppositeErrorSum forces the negative certificate's total to be the additive inverse of the SAME original aggregate signed-error total. It must satisfy the same aggregate residual equality, but need not have a term-by-term sample bijection; provenance remains an independent admission.
- positiveUpperIsRationalOrder, negativeUpperIsRationalOrder, negativeReversesOrder and translateOrder demand the actual rational-order transport laws; an arbitrary relation labelled LessOrEqual cannot silently become a usable physical inequality.
- twoSidedOriginalReceiverUpper and twoSidedOriginalReceiverLower derive both physical-source indexed receiver-work bounds:

    observedNetWork - certifiedNegativeResidualUpper
      <= originalUsefulReceiverWork
      <= observedNetWork + certifiedPositiveResidualUpper.

**All bounds are symbolic/certified and have NO assigned numerical magnitude.** The existence of the physical sampling, independent source provenance, signed full-vector Poynting→same terminal calibration, control/modulator power and dual error certificates is unproved. A deliberately coarse valid interval would not demonstrate gain; physical identification remains necessary.

### Source / acceptance / remaining max-cut

Both new Agda modules are authored on draft #1524 and added to scripts/check_smith_filsinger_formal_weld_agda29.sh, including the ORIGINAL core certificate donor. A source delimiter and literal hole/postulate scan is clean in both, but **Agda/Nix kernel checking is not available locally**, and no Agda 2.9 acceptance is claimed. Do not confuse the stronger typed proof obligations with actual SI units, a measured calibrated Poynting integral, a finite-grid convergence theorem or a real battery/current-source measurement.

**Next highest-alpha cut:** instantiate an original-device time-synchronous, current/voltage and signed environmental-face measurement with *independently obtained* finite residual certificates, then integrate the existing space–time signed rational Poynting ledger and terminal-work decomposition. The user requested FORMAL proof welds, not simulations, so if empirical calibration is unavailable the correct gate remains OPEN rather than fabricated. Other open gates F14 original electrical clock/geometry, F15 actual source replenishment, F16 atmospheric controlled causal evidence, and D1 pinned kernel type-check remain unchanged. No ESD edits or premature TOE promotion.


## 17 November five requested gates: evidence acceptance and pinned kernel route

The user requested completion of F10 physical Maxwell-to-original terminal calibration, original measurements/error certificates, F15 sustained natural-source replenishment, F16 atmospheric causality and D1 Agda kernel checking **all at once**. The exact source-first audit of the locally available original archive yielded **0/24 original raw evidence roles** across those five categories (F10 0/6, METER 0/3, F15 0/5, F16 0/6, D1 0/4). Therefore **no scientific physical gate can honestly be closed**. Do not infer impossibility from missing data, and do not invent source currents, electrical currents, controlled weather or calibrated certificate magnitudes.

New concrete accepted work, not another physical simulation:

1. **D1 focused CI route**: `.github/workflows/filsinger-agda29-acceptance.yml` adds a true Agda 2.9 Nix-pinned PR kernel check and failure-log artifacts, separate from the historical manual-only Agda 2.6.4.3 CI. It pins the exact upstream experimental stdlib source commit `008f12c2908479567a3ae3c873f9cf0b8fe5987e`, and the compiler comes from the repository's flake-locked `.#agda29-parallel`. `scripts/check_smith_filsinger_formal_weld_agda29.sh` was deduplicated (41→39 owners, 30→28 new-owner targets) while preserving all distinct proof modules. This is a **kernel acceptance route**, not a PASS: no exact-head workflow run or successful Agda elaboration exists at this writing.
2. **Original-evidence guard**: `scripts/check_smith_filsinger_original_gate_evidence.py` with 10 adversarial `scripts/test_smith_filsinger_original_gate_evidence.py` tests. Negative controls reject absent data, other apparatus IDs, model/proxy receipts, duplicate role claims, absent sampling clocks, path escape and raw-file hash mismatch. All 10 local tests PASS. The checker *never* declares a physical claim or kernel proof closed, even with complete hash-matched metadata, because raw bytes/metadata do not verify an SI calibration or causal treatment effect. New detailed role contract: `Docs/research/SmithFilsingerFiveGateEvidenceAcceptance20261117.md`.
3. **No fake scientific closure:** full-vector Poynting mathematics, rational signed port accounting and certified finite-sum interval consumers remain conditional formal work. **F10 physical** requires original pin geometry, material/ground/source-current, field flux and synchronous VI trace; **METER** requires independent calibration, clocked raw VI and signed residual bounds; **F15** requires actual net natural-source work and full repeated state restoration after controller and material losses; **F16** requires preregistered randomized intervention, sham/negative controls, meteorological covariates, replication. None is established by a symbolic Maxwell theorem, a modelled sphere/slab, filmed sound or GitHub mergeability.

Highest-alpha next action is to collect/verify the actual original instrument/current and calibration receipts and obtain an Agda CI/kernel PASS. There is no rigorous way to produce those five physical results from the present repository alone. Keep all five scientific gates OPEN; treat the evidence checker and CI workflow as infrastructure, not evidence.


## Continuation: F10/F15 signed raw VI interval transport and independent receipt guard

**Implemented original-data reader, not numerical simulation:** `scripts/check_smith_filsinger_signed_vi_intervals.py` consumes five actual source/return/receiver V/I ports on the SAME original ID, identical rational time grid and sampling clock, checks SHA256 and explicit signed orientation, and integrates conservative exact-Fraction V·I intervals under the explicitly DECLARED piecewise-linear POWER/trapezoidal sampling assumption. It returns natural incident-minus-outgoing, net controller, useful load and unassigned losses/storage-change interval, retaining sign and two-sided voltage/current error radii. It has no permission to claim independent natural-source replenishment, original Maxwell field calibration, all storage restoration, or final physical truth; positivity is at most a **conditional arithmetic interval**.

New `scripts/test_smith_filsinger_signed_vi_intervals.py` contains 13 source-authored exact arithmetic/negative-control tests: signed V/I products and differences, exact half trapezoid, five-port conservation arithmetic, wrong clock, duplicate port bytes, bad hashes, misaligned sample grids, negative uncertainty radii, unknown port orientation, incomplete port roles, non-string floating-point inputs, repeated timestamps. Wired into focused PR CI. **Do not claim a local test PASS until actually executed.**

The prior original evidence role checker now rejects reusing the same file or identical SHA256 content for multiple independent roles. `scripts/test_smith_filsinger_original_gate_evidence.py` gains two adversarial controls (12 test methods total) and a role-distinct test fixture. Exact raw file identity, origin, sampling and calibration remain separate from physically demonstrated independent environmental work. One valid file cannot automatically satisfy all F10/METER/F15/F16/D1 receipts by being relabelled.

All five physical/kernel science gates still OPEN. In particular a positive conditional V/I integral is NOT a proof that the source was natural, independently replenished, or atmospheric; and a source-authored Agda theorem is NOT D1 kernel acceptance until the pinned compiler actually checks it. F16 requires randomized meteorological intervention, not simply an electric field / rain association.


## 17 Nov continuation — conditional same-original Maxwell-to-meter bound weld and alias-error admission

**Source-first proof weld (NOT another Maxwell simulation):** `DASHI/Physics/Motors/SmithFilsingerOriginalMaxwellMeterIntervalWeldExact.agda` directly consumes the EXISTING `SmithFilsingerSelectedSpaceTimePortWeldExact`, `SmithFilsingerCertifiedSignedMeterTwoSidedExact`, the canonical `ProofCarryingFiniteSumEnclosureExact`, original `KSW668FullVectorMaxwellJetExact` and 4D space-time Poynting owners. Its `OriginalMaxwellMeterIntervalWeld jet b f` record demands a two-sided proof-carrying meter certificate indexed by the **same selected Maxwell `physicalTrace.window`**, preventing a separately chosen meter interval from masquerading as this original apparatus. It authors `originalMaxwellReceiverUpperFromSignedMeter`, `originalMaxwellReceiverLowerFromSignedMeter` and `originalCalibratedPortUpperFromSignedMeter` via equality transport, with no independent aggregate conservation assumption.

**Critical numerical acceptance correction:** the earlier exact-Fraction V/I integrator bounded only pointwise sampled meter calibration and set intersample energy error to zero. Switching and pulsed waveforms make that unsafe. `scripts/check_smith_filsinger_signed_vi_intervals.py` now **requires** `integration_error_bound_J` (nonnegative exact rational string), `integration_error_certificate` (different file from all port CSVs and other certificates), and `integration_error_certificate_sha256` for **each** of the five ports; it changes the trapezoid work interval `[L,U]` to `[L−ε,U+ε]`. This is a conditional data check, not a derivation or scientific validation of ε. An asserted ε=0 is admissible to the parser ONLY with an independently archived certificate, and is not automatically physically justified. Five regression test methods now exercise this gap; V/I suite contains 18 authored tests, evidence-inventory suite contains 12 authored tests.

**D1:** new Agda consumer added to both `owners` and `new_owners` of `scripts/check_smith_filsinger_formal_weld_agda29.sh`. No Agda 2.9 kernel check was executed successfully in this session, and the tests are source-authored rather than observed passing runs. The 2.9 pinned CI route exists in the PR, and should be run before this new module is treated as a theorem. Original Maxwell terminal field calibration F10, actually measured and independently bounded SI work, repeated-source replenishment F15, controlled weather intervention F16 and D1 kernel PASS remain OPEN.

**Pareto next cut:** obtain original clock-synchronous, signed, calibrated instrument traces and validated intersample/phase error certificates; apply the new meter-weld to that selected original `jet/b/f` only; do not infer atmospheric output or unmetered natural supply from a symbolic electromagnetic identity. ESD surfaces unchanged.


## Further continuation — symmetric original calibrated port bounds and signed environmental sink regression

**Source-first formal improvement**: the existing `SmithFilsingerOriginalMaxwellMeterIntervalWeldExact.agda` now provides `originalCalibratedPortLowerFromSignedMeter`, the missing lower analogue of `originalCalibratedPortUpperFromSignedMeter`. Both use `SelectedOriginalSpaceTimePort.loadIsSameOriginal` to transport the already certified physical receiver bounds to the **same selected original calibrated b/f terminal**, not an independently chosen terminal or new field identity. The result is **source-authored and not Agda-kernel accepted** until pinned D1 actually typechecks all modules.

**Numerical/F15 adversarial improvement**: `check_smith_filsinger_signed_vi_intervals.py` now computes `unassigned_loss_or_storage_change` by folding the existing explicit five-port `ROLE_SIGNS` ledger, not maintaining a competing handwritten balance. It exposes `conditional_environmental_sink_interval` when the upper endpoint of natural incident-minus-outgoing is <0; a `natural`-labelled channel that sends more work OUT than IN is not independently replenishing the apparatus. New `test_reverse_natural_port_is_a_sink_not_independent_supply` checks the negative-control case: sample-only hypothetical natural input 5 J, outgoing 7 J, controller net 1 J and load 2 J gives natural −2 J and unassigned −3 J. This is a regression fixture, **not an original measured source**.

**Execution distinction**: actually ran the two older **locally mounted** source-evidence and original Maxwell/replenishment suites in this session: 10/10 `unittest` and 45/45 selected `pytest` tests passed. These are *not* the latest connected GitHub branch tests. The PR branch now contains 12 source-evidence methods and 19 signed V/I interval methods (31 authored total); none of those exact-head 31 can be claimed PASS without execution. No available local Agda/Nix binaries and no successful exact-head Agda workflow receipt. Thus F10 original field-to-port physical admission, authentic meter calibration and error records, F15 independent sustained natural replenishment, F16 atmospheric causal intervention and D1 kernel acceptance remain OPEN.

**Next Pareto cut:** run the 31 source-authored branch tests on the checked-out PR and fix actual failures; then obtain pinned Agda 2.9 compiler acceptance for the same commit; separately require independently authenticated original electrical/waveform records to instantiate F10/F15. No ESD edits or unsupported TOE promotion.


## Verification correction — exact signed port-role fold and negative-flow fixture

- In `scripts/check_smith_filsinger_signed_vi_intervals.py`, the signed net balance now folds the ORIGINAL `ROLE_SIGNS` map once, so the environmental incident/outgoing and controller incident/outgoing directions are not accidentally reimplemented differently in an ad hoc expression. Conditional `natural[1] < 0` is reported explicitly as `conditional_environmental_sink_interval`.
- In `SmithFilsingerOriginalMaxwellMeterIntervalWeldExact.agda`, authored `originalCalibratedPortLowerFromSignedMeter`, the missing companion to the same-original calibrated terminal upper theorem. Both consume the existing original load equality and SAME signed rational two-sided meter certificate.
- Authored `test_reverse_natural_port_is_a_sink_not_independent_supply`, checking the source-side negative control (5 J incident, 7 J outbound, -2 J natural net; 1 J controller net and 2 J useful load imply -3 J unassigned work). This must NOT be promoted to a natural-energy gain. A static source inspection discovered and corrected a literal `\\n` versus newline CSV fixture escape mistake in the first authored version; no remaining double-escaped literal newlines were found in either connected branch test file.
- **Local execution in this turn**: older on-disk evidence-audit tests 10/10 PASS; older on-disk original Maxwell and dynamic replenishment regression tests 45/45 PASS. Those exact on-disk files are not the latest connected PR versions, so the branch's 12 evidence plus 19 signed V/I tests (31) are **not yet verified**. Similarly, a structure/no-hole scan is NOT pinned Agda acceptance; no Agda/Nix available in the present runtime and no CI run on the current PR head.

The five user-requested scientific gates F10/METER/F15/F16/D1 remain OPEN where original physical data or kernel acceptance is absent. Do not convert those into PASS because a theorem, an interval calculation or a unit test exists.


## 17 Nov F15 follow-up — exact-branch, locally executed restored-cycle first-law discriminator

Reused the existing signed V/I port interval receipt rather than inventing a Maxwell source. Added `scripts/check_smith_filsinger_restored_cycle_intervals.py`, which consumes the previous measured/source-labelled work interval output together with an **independently supplied** (not scientifically authenticated by this script) signed total stored-energy change interval and all dissipative/outgoing-loss interval. The programme's exact first-law discriminator is

`R = natural_net + controller_net − useful_load − independently_supplied_losses − (U_final − U_initial)`.

All operations use standard-library `Fraction` with outward conservative interval arithmetic: if `0 ∉ R`, the asserted complete same-window budget is inconsistent; if `0 ∈ R`, the supplied intervals are merely **compatible**, not sufficient proof of a power source. A `[0,0]` storage-change interval is a *claimed exact* restoration, not proof that original device stores were completely enumerated. A signed negative natural interval is retained as an environmental sink. `f15_closed` and `physical_claim_closed` are always false, including on a mathematically compatible example. The code guards same original ID, same clock, previous interpolation remainder admission, valid ordered rational endpoints, and nonnegative aggregate loss lower bound.

Added `scripts/test_smith_filsinger_restored_cycle_intervals.py` with 12 adversarial exact-rational test methods. **This round actually executed 12/12 PASS** on the local exact source files, and verified the local `git hash-object` identifiers equal the GitHub branch blob hashes:
- consumer `0678622bee219188999ecf1b979b43b22f4bec15`;
- test suite `1197828f45641082f9087c0e597b2b142f42243f`.

Tests cover exact zero residual with F15 still false, environmental sink rejection, stored-energy drawdown falsely implying restoration, conservative uncertainty, wrong original ID, wrong clock, absent integration remainder admission, invalid/reversed intervals, negative physical loss, floating-point endpoints, and incomplete interval endpoints. Both new files are wired into `.github/workflows/filsinger-agda29-acceptance.yml`.

**Acceptance boundary:** these 12 local source-matched passing tests are a verified Python audit, not calibrated original experiment data nor Agda 2.9 kernel acceptance. The 31 previously committed GitHub-branch V/I and role-evidence tests remain unexecuted in this container; no pinned Agda 2.9 run is shown for the exact PR head. Physical F10, authentic metering/calibration, F15 independently replenished natural work, F16 atmospheric intervention and D1 remain OPEN. Do not classify an input merely named `natural` as independent source work without a separately established origin certificate. Original ESD material remains import-only.


## 17 Nov next cut — F15 upstream receipt recomputation + original Maxwell restored-source funding

1. **F15 JSON integrity weld actually tested.** `scripts/check_smith_filsinger_restored_cycle_intervals.py` now REFUSES a bare net-source summary. It requires the upstream exact V/I producer's `signed_balance_from_named_port_role_map = true` and all five independently named `conditional_port_work` interval entries, recomputes natural incident−outgoing, controller incident−outgoing, load, and the unassigned work interval, and requires exact equality with **all four** purported producer summary fields before performing the original loss/storage first-law residual test. This closes the previous danger that an independently edited source/load summary could be accepted as an arithmetic premise. It does **not** authenticate a signed input's physical provenance. The suite now has **17/17 actually locally executed PASS**, and local Git blob identities match the connected PR branch exactly: consumer `831b986ee5857236d61b0474604b399d88436995`, tests `c3c6d1a563779c92ea35f67426e21328938ce917`. Five new adversarial controls cover tampered environmental summary, load, unassigned residual, missing physical port role, missing sign map.
2. **Same-original Agda proof joining, source-authored.** Added `DASHI/Physics/Motors/SmithFilsingerOriginalMaxwellRestoredMeterFundingExact.agda`. Its `restoredSourceFundsSameOriginalMaxwellReceiver` consumes the **same b/f original field/port** both as `OriginalMaxwellMeterIntervalWeld jet b f` and the independently admitted `SignedSourceCycleWeld b f`, then transports the existing Nat `Cycle.workPaidAfterStorageReturns` through the existing additive rational `calibratedWork`, original Maxwell `loadIsSameOriginal`, and the source's same-original load/loss identifications. The conclusion is original Maxwell receiver work plus calibrated original internal loss equals calibrated independently admitted natural work plus calibrated controller input. No secondary conservation equation is stipulated. **This is conditional on an original source admission and cannot establish a physical natural-source replenishment claim.** The named imported field and theorem declarations are present, source has no holes or postulates, and the module is listed in both pinned Agda checker arrays. **Agda kernel ACCEPTANCE NOT RUN / NOT CLAIMED.**
3. **Unchanged physics gates:** F10 Maxwell→original terminal material+field calibration OPEN; authentic electrical measurement and certified intersample/phase errors OPEN; F15 independently replenished original natural net work plus all-store return OPEN; F16 controlled/replicated weather intervention OPEN; D1 pinned full Agda 2.9 kernel PASS OPEN. The existing numerically exact F15 result is a source-linked arithmetic consistency checker only, not experimental validation. Do not derive global energy/climate claims, and do not edit ESD.


## 17 Nov F15 acceptance hardening — mandatory original-file replay

**High-alpha fix:** F15 previously recomputed the claimed five-port net from five JSON intervals, which still permitted a malicious or stale upstream `conditional_port_work` and four summary fields to be edited *consistently*. `scripts/check_smith_filsinger_restored_cycle_intervals.py` now has `analyze_from_original_files`, which calls the original `check_smith_filsinger_signed_vi_intervals.calculate(vi_manifest, vi_root)` against the **raw five V/I CSV files, individual SHA256 identities, calibration/intersample-error certificates and the declared common clock**. It compares every original signed producer field (original ID, clock, port intervals, natural/controller/load net, unassigned sum, and both acceptance flags) with the supplied V/I JSON receipt, rejecting any mismatch **before** applying the independent all-loss/storage first-law interval audit.

The F15 CLI is intentionally fail-closed: `--vi-manifest ORIGINAL_VI_MANIFEST.json --vi-root RAW_ORIGINAL_PORTS` are now mandatory. The old invocation accepting two self-described JSON receipts alone is not an accepted F15 check. This binds arithmetic consistency back to the exact source files, though **hashes and copied certificate text cannot establish meter truth or environmental independence**.

New `scripts/test_smith_filsinger_restored_cycle_raw_replay.py` adds seven adversarial raw-file checks: replay-compatible-but-not-physical, self-consistent forgery of signed port data and summaries, stale raw CSV hashes, wrong original acquisition clock, absent integration-error evidence, mismatched original apparatus and load-only tampering. Included in `.github/workflows/filsinger-agda29-acceptance.yml`. These seven tests are source-authored and **not yet executed in this session**. Previous F15 17/17 locally executed matches its earlier exact commit but must be rerun with changes. D1 pinned Agda kernel acceptance continues to require actual compiler execution; GitHub workflow execution must be confirmed at the exact PR head.

The independent `all_dissipative_and_outgoing_loss_J` and `total_stored_energy_final_minus_initial_J` remain *submitted intervals* (not independently authenticated observations). F10 original Maxwell→terminal calibration, physical error provenance, F15 independently replenished source and fully restored original stores, F16 causal atmospheric experiment, and D1 kernel PASS remain **OPEN**. The proof owners and ESD modules are unchanged.

Reproducible invocation after obtaining authentic original files:

```bash
python3 scripts/test_smith_filsinger_restored_cycle_raw_replay.py
python3 scripts/check_smith_filsinger_signed_vi_intervals.py original_vi_manifest.json --root raw_original_ports --out signed_vi_work.json
python3 scripts/check_smith_filsinger_restored_cycle_intervals.py signed_vi_work.json independent_loss_and_storage.json --vi-manifest original_vi_manifest.json --vi-root raw_original_ports --out first_law_audit.json
```


## 17 November — reproducible D1/Python exact-head acceptance runner

**Execution bottleneck fixed in-repo, not misrepresented as a kernel PASS.** The focused acceptance GitHub workflow had `pull_request`/manual triggers but no observed workflow runs. Added an explicit `push` event for `research/sun-earth-coupled-source-20261116` on SmithFilsinger source/test/workflow changes. An event trigger cannot force Actions to run if the repository/runner policy prevents execution; check actual statuses.

New `scripts/run_smith_filsinger_acceptance.sh` is one reproducible local command. From a CLEAN checkout of the exact branch head:

```sh
bash scripts/run_smith_filsinger_acceptance.sh --python-only
bash scripts/run_smith_filsinger_acceptance.sh --full
```

The runner rejects uncommitted relevant source/test changes, records `git rev-parse HEAD`, executes the four current suites (original evidence inventory, signed V/I exact intervals, restored first-law intervals, original raw-V/I replay), and under `--full` also invokes **the real** `scripts/check_smith_filsinger_formal_weld_agda29.sh` compiler checker on all 41 designated Agda owners. Shell `set -euo pipefail` makes any Python or Agda failure fatal; the previous `acceptance-pass.txt` marker is deleted before work and only recreated when ALL selected checks return zero. The success status is **`PYTHON_ONLY_NO_AGDA_ACCEPTANCE`** or **`ACCEPTED_PYTHON_AND_PINNED_AGDA`**, never an unqualified physical-success flag. Logs/marker are stored in `.filsinger-acceptance/`, and CI uploads them even if the task fails. CI's pinned Agda step now calls this runner `--full`; its initial Python checks remain a quicker fail-fast stage.

**Current truth:** workflow authored and source committed, but no GitHub Actions run has been observed for the exact latest head and Agda/Nix are not available in the current assistant container. Do not claim D1 kernel PASS, nor convert valid Python meter arithmetic into physical F10, independent sustained F15 replenishment, or F16 controlled atmospheric causality. Original experiment/source authentication and all-store return are still required.


### D1 rerunnable source-identity refinement

The clean-head acceptance runner was refined after source review: it now rejects **all modified tracked project inputs** by `git diff --quiet HEAD` and rejects **new untracked project source files** under `DASHI`, `scripts` and the focused workflow; it deliberately ignores untracked `.agdai` caches so a second run can succeed and ignores the third-party `pinned-agda-stdlib` checkout installed by CI. Without this restriction, the workflow's own pinned stdlib checkout could falsely trigger dirty-source rejection. All results remain pending actual full execution; source-level repair is not a PASS receipt.
