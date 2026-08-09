# Relational Shared-State and Process-Bearing Response Formalism

This document abstracts a recurring parent–child communication pattern without treating either role as a diagnosis or moral identity. The same structures may apply to other caregiving, dependent, familial, clinical, administrative, or institutional relationships.

## 1. Shared-state update

A conversation maintains a provisional shared state

\[
S_t=(O_t,C_t,P_t,Q_t,A_t,D_t,U_t,R_t),
\]

where the components record:

- \(O_t\): current conversational object;
- \(C_t\): contribution history;
- \(P_t\): explicitly retained durable preferences, each with owner, scope, time, and provenance;
- \(Q_t\): unresolved questions;
- \(A_t\): recorded assents and refusals;
- \(D_t\): decision kind and provenance;
- \(U_t\): attributed future obligations;
- \(R_t\): rupture status.

A preference contribution does not automatically become a durable preference. Promotion into \(P_t\) requires an explicit retained state object.

A contribution may be heard without being taken up:

\[
\operatorname{Heard}(c)\not\Rightarrow\operatorname{Uptaken}(c).
\]

The Agda `Uptaken c before after` type now requires an exact `ContributionTransition` witness:

\[
\operatorname{contributions}(after)
=
c::\operatorname{contributions}(before).
\]

Only after that state transition is proved does the uptake record describe whether the contribution retained its conversational role and constrained later responses and decision history. A bare report that something was heard cannot inhabit this retained-state guarantee.

Object displacement occurs when a still-open contribution triggers an association, solution, preference, defensive reaction, or regulatory need which then replaces the jointly established object.

## 2. Pseudo-consultation and provenance

Consultation is genuine only when the consulted contribution enters the decision procedure as actual information. It does not give the consulted person control, but the decision must be sensitive to their input.

The following implications are invalid:

\[
\operatorname{Asked}(y,p)\not\Rightarrow\operatorname{Agreed}(y,p),
\]

\[
\operatorname{Discussed}(p)\not\Rightarrow\operatorname{JointlyDecided}(p),
\]

\[
\operatorname{NoReply}(y,p)\not\Rightarrow\operatorname{Assent}(y,p).
\]

If a participant does not answer and action is necessary, the correct provenance is *unilateral decision due to no recorded response*, not *joint decision*.

## 3. Conditional proposition trees

The object of response is normally not an atomic proposition. It is an exact guarded node

\[
n=(\Gamma,\alpha,\mu,\tau,\omega,\epsilon,\kappa)
\]

within a refinement tree, where the fields encode context, contemplated action, modality, temporal scope, practical extent, exceptions, and unresolved conditions.

The general response object is

\[
\operatorname{ActualResponse}(x,n,d,t),
\]

indexed to participant, node, decision episode, and time.

Affirmation is local. It does not automatically transport to:

- descendant tasks;
- broader antecedents;
- stronger modalities;
- larger practical scopes;
- later decision episodes;
- changed capacity states.

In particular,

\[
\operatorname{Affirm}(\mathsf{Consider}(z)\mid\Gamma)
\not\Rightarrow
\operatorname{Affirm}(\mathsf{Commit}(z)\mid\Gamma').
\]

Transport is represented at two levels.

1. `ResponseTransportWitness source target` is an **assessment**. Its Boolean fields may explicitly report failed locality conditions.
2. `AuthorisedResponseTransport source target` is the licensing type. It contains the assessment plus equality proofs that node, context, modality, scope, temporal validity, and any strengthened commitment requirement are all `true`.

Therefore:

\[
\operatorname{TransportAssessment}
\not\Rightarrow
\operatorname{TransportAuthorised}.
\]

Only the proof-carrying authorised type may be supplied to the transport operation.

A statement that an option *might be considered* can positively affirm branch liveness while leaving the option itself unresolved:

\[
+1\text{ toward }\mathsf{MightConsider}(z),
\qquad
z=0_{\mathrm{open}}.
\]

## 4. Refined zero

A bare zero destroys important historical distinctions. Relevant zero states include:

\[
0_{\mathrm{absent}},
0_{\mathrm{open}},
0_{\mathrm{suspended}},
0_{\mathrm{blocked}},
0_{\mathrm{expired-unweighed}},
0_{\mathrm{handover}},
0_{\mathrm{completed-neutral}}.
\]

Hence:

\[
0_{\mathrm{expired-unweighed}}\neq -1_{\mathrm{rejected}}.
\]

Memory must retain whether a branch was rejected, blocked, expired, abandoned, or remained pending.

## 5. Future-capacity capture

Ambiguous present participation can later be rewritten as an obligation against another person's future labour:

\[
\operatorname{Invitation}_t
\to
\operatorname{AttributedCommitment}_{t+1}
\to
\operatorname{DemandOnFutureCapacity}.
\]

The protective invariant is:

\[
\operatorname{FutureObligation}(x,a)
\Rightarrow
\operatorname{ExplicitCommitment}(x,a).
\]

This matters most where capacity is scarce or unpredictable because attribution errors are not cheaply reversible.

## 6. Causal order and defensive reversal

Conflict reconstruction should preserve

\[
\text{act}\to\text{impact}\to\text{objection}\to\text{defensive response}.
\]

The objection and its delivery may require review, but they must not erase the event that prompted them.

A defensive route may transform a concrete complaint into an unparticularised counter-allegation. A request for exact particulars can then itself be reframed as further misconduct, generating recursive conflict expansion:

\[
\mathcal D(M,x)=(M\text{ unresolved},x\text{ newly accused}).
\]

“DARVO-like” is therefore used only as a cautious structural descriptor. It is not inferred without incident reconstruction, and the formalism does not establish deliberate strategy or the truth of the initiating allegation.

## 7. Experience reports and behavioural allegations

These are differently typed:

- “That felt accusatory” is an experience report.
- “You gaslit me” is a behavioural allegation.

A behavioural allegation requires an actor, observable particular, context, affected person, alleged effect, and evidential receipt. Requesting particulars does not negate the reported feeling; it makes behavioural repair determinate.

## 8. Partial family-name intrusion

The base `CorrectedNameIntrusion` record is an **observation carrier**. It records the intended and competing referents, candidates, emitted fragment, final name, stage, contextual flags, and whether a composite label was reported. Because an observation may be uncertain or miscoded, this base record alone does not prove that the event was immediately corrected or non-composite.

The stronger `ValidatedCorrectedNameIntrusion event` subtype requires proofs that:

- `immediatelySelfCorrected event ≡ true`;
- `deliberateCompositeLabelUsed event ≡ false`;
- speaker, intended referent, and competing referent have the required distinct typed roles;
- candidate roles agree with the intended and competing referents.

Only after those proofs exist is the following sequence licensed as the coded classification:

\[
\text{intended name activation}
+
\text{competing family-name activation}
\to
\text{partial intrusion}
\to
\text{monitoring and correction}.
\]

For example, a parent frustrated with a child may begin producing a sibling's name and then correct to the child's name; a grandparent may similarly begin another descendant's name. This is a corrected name intrusion only when the validation witness exists, and it is not thereby a deliberate “relative–child” composite label.

Freud's parapraxis framework supplies historical provenance for asking whether slips can reflect structured association. Modern lexical-access and speech-error models supply a less motive-heavy account in terms of competing semantic, lexical, phonological, and affective activation.

The evidence boundary is:

\[
\operatorname{PartialSlip}
\not\Rightarrow
\operatorname{DeliberateComparison},
\]

\[
\operatorname{PartialSlip}
\not\Rightarrow
\operatorname{StableIdentitySubstitution},
\]

\[
\operatorname{PartialSlip}
\not\Rightarrow
\operatorname{RecoveredHiddenMotive}.
\]

Repeated context-sensitive intrusions may support a defeasible associative-transport hypothesis, but current acts must still be evaluated on current evidence.

## 9. Process-bearing branches and memory

Some propositions authorise extended goal processes rather than atomic acts. A goal branch may carry applications, documents, contacts, queue positions, learned constraints, pending responses, deadlines, external dependencies, and handover obligations even while its outcome remains absent:

\[
G_t=0\not\Rightarrow S_t=0.
\]

A PNF memory should retain branch status, liveness layer, capacity, unresolved residual, alternatives, and provenance rather than quotienting every unrealised outcome into “nothing happened.”

Revocation changes which future transitions remain authorised; it does not erase completed acts, pending external processing, closure requirements, or accumulated state:

\[
\operatorname{AuthorityRevoked}
\neq
\operatorname{ProcessStateErased}.
\]

Quantitative promotion is synchronized. A family refinement carries one authoritative list of branch refinements and proves:

\[
\begin{aligned}
\text{qualitative branches}
&=\operatorname{map}(\text{qualitativeBranch},R),\\
\text{portfolio metrics}
&=\operatorname{map}(\text{selectionMetric},R),\\
\text{branch waves}
&=\operatorname{map}(\text{branchWave},R).
\end{aligned}
\]

Each branch refinement also proves metric identity/cost preservation and exact derivation of its wave from the branch's amplitude and phase. Foreign, missing, or duplicated metrics and waves therefore cannot inhabit the synchronized refinement type.

Hyperformal incidence likewise requires a membership proof that the participant occurs in the branch's `assignedParticipants`; it is no longer true by construction for every participant–branch pair.

## 10. Feasibility filtration

A named branch may be logically imaginable without being institutionally available, economically survivable, accessible to the agent, compatible with capacity, or temporally live.

Represent liveness as a vector over layers:

\[
\mathbf L(B,t)=
(L_{\mathrm{logical}},L_{\mathrm{institutional}},L_{\mathrm{economic}},L_{\mathrm{agent}},L_{\mathrm{capacity}},L_{\mathrm{temporal}}).
\]

Thus:

\[
\operatorname{NamedOption}(B)
\not\Rightarrow
\operatorname{FeasibleOption}(B).
\]

## 11. Attractor alignment and branch interference

More branches do not necessarily improve outcomes. A branch must be serviceable and usefully tend toward the desired attractor.

Qualitatively, a branch may be aligned, orthogonal, opposed, or of unknown alignment. Pairs of branches may interfere constructively, neutrally, destructively, or incoherently through shared resources, incompatible requirements, conflicting provenance, or timing.

The double-slit and \(n\)-slit analogy captures the non-additivity:

\[
\left|\sum_i a_i e^{i\phi_i}\right|^2
=
\sum_i a_i^2
+
2\sum_{i<j}a_i a_j\cos(\phi_i-\phi_j).
\]

In the exact optimizer, the \(i<j\) condition is enforced structurally by an upper-triangular typed interaction matrix. There is no diagonal cell, there is exactly one cell per unordered branch-position pair, and a cell may contain at most one interaction. Arbitrary string endpoints, self-interactions, and repeated pair entries cannot contribute to the portfolio ledger.

A useful branch family should:

- remain within servicing capacity;
- improve attractor reachability;
- preserve useful optionality;
- value information gain;
- penalise destructive interference;
- distinguish visible activity from genuine progress.

## 12. Trauma and memory deformation

A traumatic history may alter later branch-management weights. It can produce either branch hoarding, because closure feels dangerous, or premature pruning, because similar branches are expected to fail or harm.

This is represented as a defeasible transition deformation, not a diagnosis. A sound model records whether the transported constraint remains context-sensitive.

## 13. Repair invariants

A minimally corrigible relational process preserves:

1. open conversational objects until answered, explicitly deferred, or withdrawn by their originator;
2. exact proposition identity, context, modality, scope, and time;
3. decision provenance;
4. feeling–fact–allegation type separation;
5. causal order;
6. particularity of serious allegations;
7. unresolved rupture status until bilateral repair;
8. future-capacity protection;
9. care/accountability separation;
10. person-specific evaluation rather than inherited family substitution;
11. prior versions and provenance when accounts change;
12. a non-retaliatory correction channel.

The central law is:

\[
\boxed{
\operatorname{Transport}(r,n\to n')
\text{ is permitted only when }
\operatorname{AuthorisedResponseTransport}(n,n')
\text{ is inhabited.}
}
\]

An assessment record, narrative similarity, or Boolean flag with failed requirements is not an authorisation witness.
