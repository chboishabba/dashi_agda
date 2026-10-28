#!/usr/bin/env python3
"""Finite truth-table regression for the Goodman Sonic Warfare source bridge.

Exact enumeration of explicitly synthetic finite carriers only.
NO Agda kernel check. NO physical experiment, human affect inference,
operational acoustics, clinical inference or historical verification.
"""
from itertools import product
from json import dumps


def attempts(states, project, answer):
    """Exhaustively enumerate functions O -> A agreeing with answers on states."""
    observations = tuple(sorted(set(project[s] for s in states)))
    answers = tuple(sorted(set(answer[s] for s in states)))
    successes = []
    count = 0
    for mapped in product(answers, repeat=len(observations)):
        count += 1
        mapping = dict(zip(observations, mapped))
        if all(mapping[project[s]] == answer[s] for s in states):
            successes.append(mapping)
    return count, successes


def test_case(name, states, project, query_answers, expected):
    count, witnesses = attempts(states, project, query_answers)
    observed = bool(witnesses)
    assert observed == expected, (
        f"{name}: factorization={observed}, expected {expected}")
    return {"case": name, "candidate_functions_exhausted": count,
            "factors": observed, "expected": expected,
            "successful_functions": len(witnesses)}


def run():
    out = []
    mirrors = ('reflection', 'echo', 'figurative', 'kozyrev-candidate')
    mirror_surface = dict.fromkeys(mirrors, 'mirror')
    out.append(test_case('mirror label is adequate for name', mirrors,
        mirror_surface, dict.fromkeys(mirrors, 'mirror'), True))
    out.append(test_case('mirror label is inadequate for mechanism', mirrors,
        mirror_surface, {'reflection': 'ordinary', 'echo': 'ordinary',
            'figurative': 'not-established', 'kozyrev-candidate': 'not-established'}, False))

    encounters = ('low', 'high')
    common_features = dict.fromkeys(encounters, 'same-selected-acoustic-features')
    out.append(test_case('features adequately describe selected features', encounters,
        common_features, dict.fromkeys(encounters, 'feature'), True))
    out.append(test_case('selected features do not determine response', encounters,
        common_features, {'low': 'low-response', 'high': 'high-response'}, False))

    propaganda = ('persuasion-with-supported-content', 'persuasion-with-false-content')
    common_intent = dict.fromkeys(propaganda, 'same-persuasive-intent')
    out.append(test_case('propaganda intent does not determine truth', propaganda,
        common_intent, dict(zip(propaganda, ('supported', 'false-or-misleading'))), False))

    shared_content = ('deceptive-intent-unpaid', 'deceptive-intent-paid')
    same_content = dict.fromkeys(shared_content, 'same-content')
    out.append(test_case('same content does not determine deception', shared_content,
        same_content, dict(zip(shared_content, ('intent-unpaid', 'intent-paid'))), False))

    # M1 four-world interaction: neither signal nor context alone suffices,
    # but their joint observation recovers the synthetic response exactly.
    scenes = ('quiet-protected', 'quiet-exposed', 'loud-protected', 'loud-exposed')
    signal = dict(zip(scenes, ('quiet', 'quiet', 'loud', 'loud')))
    context = dict(zip(scenes, ('protected', 'exposed', 'protected', 'exposed')))
    response = dict(zip(scenes, ('baseline', 'baseline', 'baseline', 'elevated')))
    joint = {state: (signal[state], context[state]) for state in scenes}
    out.append(test_case('signal alone fails contextual response', scenes,
        signal, response, False))
    out.append(test_case('context alone fails contextual response', scenes,
        context, response, False))
    out.append(test_case('joint signal and context determine toy response', scenes,
        joint, response, True))

    # R1: Count/tempo metadata hides the onset phase in a two-slot trace.
    traces = ('slot-zero', 'slot-one')
    count = dict.fromkeys(traces, 'one-event')
    phase = dict(zip(traces, ('phase-zero', 'phase-one')))
    out.append(test_case('pulse count adequately answers count', traces,
        count, dict.fromkeys(traces, 'one-count-answer'), True))
    out.append(test_case('pulse count cannot determine phase', traces,
        count, phase, False))
    out.append(test_case('phase observation determines toy phase', traces,
        phase, phase, True))

    # I1: Under passive observation X=U in both structurally different
    # mechanisms. Model A has Y=X; model B has Y=U.
    # A controlled do(X=1), holding U=0, separates the two models.
    models = ('direct-sound-effect', 'common-driver-only')
    passive_quiet = dict.fromkeys(models, 'quiet-signal-quiet-response')
    passive_loud = dict.fromkeys(models, 'loud-signal-loud-response')
    passive = {model: (passive_quiet[model], passive_loud[model])
               for model in models}
    active = {
        'direct-sound-effect': 'loud-signal-loud-response',
        'common-driver-only': 'loud-signal-quiet-response',
    }
    out.append(test_case('passive profiles are equivalent', models,
        passive, passive, True))
    out.append(test_case('passive observations cannot select causal model', models,
        passive, active, False))
    out.append(test_case('controlled intervention distinguishes toy mechanisms', models,
        active, active, True))

    # T1: A binary toy transfer environment can mask source activity at
    # one receiver. This fixture is NOT a calibrated wave equation.
    transport_states = ('trans-off', 'trans-on', 'absorb-off', 'absorb-on')
    receiver = {
        'trans-off': 'silent', 'trans-on': 'signal',
        'absorb-off': 'silent', 'absorb-on': 'silent',
    }
    emitter = {
        'trans-off': 'off', 'trans-on': 'on',
        'absorb-off': 'off', 'absorb-on': 'on',
    }
    out.append(test_case('receiver projection adequately answers receiver', transport_states,
        receiver, receiver, True))
    out.append(test_case('receiver silence does not determine source activity', transport_states,
        receiver, emitter, False))
    for setting in ('trans', 'absorb'):
        for before in ('off', 'on'):
            for source in ('off', 'on'):
                after = f'{setting}-{source}'
                assert after in receiver
                assert emitter[after] == source
    assert receiver['trans-off'] != receiver['trans-on']
    assert receiver['absorb-off'] == receiver['absorb-on']

    # T2: An *additional* idealised source-side monitor recovers the toy
    # source-activity label even when the selected receiver is silent.
    monitor = {state: ('signal' if emitter[state] == 'on' else 'silent')
               for state in transport_states}
    joint_receivers = {state: (receiver[state], monitor[state])
                       for state in transport_states}
    out.append(test_case('source monitor recovers source-activity query', transport_states,
        monitor, emitter, True))
    out.append(test_case('joint receiver and monitor recover source activity', transport_states,
        joint_receivers, emitter, True))
    assert monitor['trans-off'] != monitor['absorb-on']

    # T4: A source monitor identifies the emitter but not the environment.
    # An additional idealised medium observation is independent evidence,
    # not reconstruction from a silent microphone.
    medium = {state: ('transmitting' if state.startswith('trans-') else 'absorbing')
              for state in transport_states}
    full_observer = {state: (joint_receivers[state], medium[state])
                     for state in transport_states}
    out.append(test_case('joint receiver and source monitor cannot determine medium',
        transport_states, joint_receivers, medium, False))
    out.append(test_case('full observer recovers declared medium',
        transport_states, full_observer, medium, True))
    out.append(test_case('full three-observer fixture identifies each toy world',
        transport_states, full_observer,
        {state: state for state in transport_states}, True))
    assert len(set(full_observer.values())) == 4
    assert joint_receivers['trans-off'] == joint_receivers['absorb-off']

    # T5 Pareto cut: source-monitor + independently known medium already
    # identifies all four worlds. The original receiver is informationally
    # redundant *relative to this finite set of candidate coordinates*.
    source_and_medium = {state: (monitor[state], medium[state])
                         for state in transport_states}
    receiver_and_medium = {state: (receiver[state], medium[state])
                           for state in transport_states}
    world_identity = {state: state for state in transport_states}
    out.append(test_case('source monitor alone does not identify whole world',
        transport_states, monitor, world_identity, False))
    out.append(test_case('medium alone does not identify whole world',
        transport_states, medium, world_identity, False))
    out.append(test_case('receiver and medium do not identify whole world',
        transport_states, receiver_and_medium, world_identity, False))
    out.append(test_case('source monitor plus medium identifies whole world',
        transport_states, source_and_medium, world_identity, True))
    out.append(test_case('Pareto pair determines omitted downstream receiver',
        transport_states, source_and_medium, receiver, True))

    # Finite two-way reconstruction demonstrates redundancy, not just
    # injectivity. Does not assume a real, independently calibrated sensor.
    def recover_full(pair):
        src, med = pair
        recv = src if med == 'transmitting' else 'silent'
        return ((recv, src), med)
    def forget_receiver(full):
        (recv, src), med = full
        return (src, med)
    assert all(
        full_observer[state] == recover_full(source_and_medium[state])
        and source_and_medium[state] == forget_receiver(full_observer[state])
        for state in transport_states
    )
    assert len(set(source_and_medium.values())) == 4
    assert len(set(receiver_and_medium.values())) == 3

    assert len(out) == 27
    print(dumps({"mode": "finite-exhaustive-synthetic-only",
                 "all_passed": True, "tests": out,
                 "non_promotion": ["not-Agda-kernel", "not-measured-acoustics",
                                   "not-human-affect", "not-historical-evidence",
                                   "not-Monster-same-object"]}, indent=2))


if __name__ == '__main__':
    run()
