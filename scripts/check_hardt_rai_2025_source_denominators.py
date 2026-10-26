#!/usr/bin/env python3
"""Paper/repository/code-source denominator audit; NOT original EEG reproduction.

Paper: Rai et al. iScience (2025) DOI 10.1016/j.isci.2025.112922.
Dataset: Rai and Orgs UCL RDR v1 DOI 10.5522/04/28508744.v1.
The authors own both records and data. A discrepancy is an unresolved
version/coverage JOIN, not proof of a study error or invented participants.
"""
from __future__ import annotations
from itertools import combinations
import argparse
import json
from pathlib import Path

PAPER = dict(recruited=69, lost_technical=9, lost_markers=1,
             retained=59, performances=(20, 18, 21))
DEPOSIT = dict(declared_recordings=57, accession='28508744',
               doi='10.5522/04/28508744.v1', license='CC0 1.0')
CODE_LOCATORS = ('https://osf.io/uz573/', 'https://osf.io/ursmc/')



# These counts come from different observational roles, including three
# appearances of N=57. Standard source-root/consumer identity matters more
# than equality of a scalar statistic. Do not assert participant-ID matches.
COHORT_ROLES = (
    dict(id='live_eeg_retained', source='paper:10.1016/j.isci.2025.112922',
         condition='live-P1-P2-P3', measure='retained_EEG_datasets', n=59),
    dict(id='live_questionnaires', source='paper:10.1016/j.isci.2025.112922',
         condition='live-P1-P2-P3', measure='questionnaire_responses', n=57),
    dict(id='cinema_participants', source='paper:10.1016/j.isci.2025.112922',
         condition='cinema-S1-S2-S3', measure='screening_participants', n=57),
    dict(id='ucl_eeg_deposit', source='dataset:10.5522/04/28508744.v1',
         condition='deposited_live_dataset', measure='described_EEG_recordings', n=57),
)


def audit_cohort_roles(roles=COHORT_ROLES):
    """Fail closed on count-only joins of distinct source/arm/measurement roles."""
    roles = tuple(roles)
    ids = [r['id'] for r in roles]
    typed = [(r['source'], r['condition'], r['measure']) for r in roles]
    if len(set(ids)) != len(ids) or len(set(typed)) != len(typed):
        raise ValueError('duplicate source-root or typed cohort identity')
    if any(not all(isinstance(r[k], str) and r[k].strip()
                   for k in ('id', 'source', 'condition', 'measure'))
           or isinstance(r['n'], bool) or not isinstance(r['n'], int)
           or r['n'] < 0 for r in roles):
        raise ValueError('unattributed or invalid cohort count')
    known = {r['id']: r for r in roles}
    expected = {
        'live_eeg_retained': ('paper:10.1016/j.isci.2025.112922', 59),
        'live_questionnaires': ('paper:10.1016/j.isci.2025.112922', 57),
        'cinema_participants': ('paper:10.1016/j.isci.2025.112922', 57),
        'ucl_eeg_deposit': ('dataset:10.5522/04/28508744.v1', 57),
    }
    if set(known) != set(expected) or any(
        (known[k]['source'], known[k]['n']) != v for k, v in expected.items()
    ):
        raise ValueError('original source-locked denominator role changed')
    if known['live_questionnaires']['measure'] != 'questionnaire_responses' \
       or known['live_eeg_retained']['measure'] != 'retained_EEG_datasets' \
       or known['ucl_eeg_deposit']['measure'] != 'described_EEG_recordings' \
       or known['cinema_participants']['condition'] != 'cinema-S1-S2-S3':
        raise ValueError('questionnaire, live EEG, cinema and deposit identities conflated')
    same_number_different_roles = [
        [a['id'], b['id']] for a, b in combinations(roles, 2)
        if a['n'] == b['n'] and
        (a['source'], a['condition'], a['measure']) !=
        (b['source'], b['condition'], b['measure'])
    ]
    assert len(same_number_different_roles) == 3
    return dict(typed_source_roles=len(roles),
                distinct_57_roles=3,
                equal_number_nonidentity_pairs=same_number_different_roles,
                role_count_joins_are_authenticated=False,
                paper_live_questionnaires_missing=59-57,
                deposited_subjects_match_questionnaire_respondents=None,
                deposited_subjects_match_paper_eeg=None,
                cinema_subjects_are_same_as_live=None)


def audit_metadata(paper=PAPER, deposit=DEPOSIT):
    if paper['recruited']-paper['lost_technical']-paper['lost_markers'] != paper['retained']:
        raise ValueError('publication recruitment/exclusion arithmetic')
    if sum(paper['performances']) != paper['retained']:
        raise ValueError('publication retained event counts')
    if deposit['declared_recordings'] > paper['retained'] or deposit['declared_recordings'] < 0:
        raise ValueError('deposit numerical coverage outside publication cohort')
    n=paper['performances']
    pair_counts=tuple(k*(k-1)//2 for k in n)
    return dict(paper_recruited=paper['recruited'],
                paper_reported_excluded=paper['lost_technical']+paper['lost_markers'],
                paper_retained=paper['retained'],
                published_event_counts=list(n),
                synthetic_max_same_event_pair_combinations=list(pair_counts),
                synthetic_max_all_event_pairs=sum(pair_counts),
                dataset_catalog_declared_recordings=deposit['declared_recordings'],
                nominal_record_gap=paper['retained']-deposit['declared_recordings'],
                deposit_doi=deposit['doi'], deposit_license=deposit['license'],
                osf_code_locators=list(CODE_LOCATORS),
                osf_code_identical_or_different_verified=False,
                original_file_inventory_verified=False,
                participant_membership_join_verified=False,
                real_eeg_reanalysis_verified=False,
                transmitter_to_receiver_effect_verified=False,
                typed_cohort_roles=audit_cohort_roles())


def subject_join(paper_ids, archive_ids):
    """Join supplied anonymised IDs only; their origin cannot be certified here."""
    p=list(paper_ids); a=list(archive_ids)
    if len(p)!=len(set(p)) or len(a)!=len(set(a)):
        raise ValueError('duplicate participant or recording ID')
    if not all(isinstance(x,str) and x.strip() for x in p+a):
        raise ValueError('missing anonymised identity')
    return dict(paper_ids=len(p),archive_ids=len(a),
                matched_ids=len(set(p)&set(a)),
                published_not_in_archive=sorted(set(p)-set(a)),
                archive_not_in_published=sorted(set(a)-set(p)),
                ids_authenticated_by_original_data=False,
                syntactic_archive_subset_of_supplied_ids=set(a).issubset(set(p)),
                cross_source_join_is_a_measurement_receipt=False)


def audit_manifest_file(path:Path):
    obj=json.loads(path.read_text(encoding='utf-8'))
    required=('paper_doi','deposit_doi','paper_retained','deposit_declared','paper_ids','archive_ids')
    if not isinstance(obj,dict) or any(x not in obj for x in required):
        raise ValueError('manifest missing original accession/identity fields')
    if obj['paper_doi']!='10.1016/j.isci.2025.112922' or obj['deposit_doi']!=DEPOSIT['doi']:
        raise ValueError('not same source publication/deposit identifiers')
    if obj['paper_retained']!=59 or obj['deposit_declared']!=57:
        raise ValueError('paper/deposit counts not source-locked')
    joined=subject_join(obj['paper_ids'],obj['archive_ids'])
    if joined['paper_ids']!=59 or joined['archive_ids']!=57:
        raise ValueError('not a complete source-specific identifier reconciliation')
    return joined


def main():
    p=argparse.ArgumentParser()
    p.add_argument('--manifest',type=Path)
    a=p.parse_args()
    output=audit_manifest_file(a.manifest) if a.manifest else audit_metadata()
    print(json.dumps(output,sort_keys=True,indent=2))

if __name__=='__main__':main()
