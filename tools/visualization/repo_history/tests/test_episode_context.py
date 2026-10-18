from dashi_repo_history.git_history import _episode_context_commits
from dashi_repo_history.model import CommitRecord


def test_episode_context_restores_omitted_branch_paths():
    commits = [
        CommitRecord("A", 0, ()),
        CommitRecord("B", 1, ("A",)),
        CommitRecord("C", 2, ("B",)),
        CommitRecord("D", 3, ("B",)),
        CommitRecord("E", 4, ("C",)),
        CommitRecord("F", 5, ("D",)),
        CommitRecord("M", 6, ("E", "F")),
        CommitRecord("N", 7, ("M",)),
    ]

    selected = [commits[0], commits[6], commits[7]]
    expanded, episodes = _episode_context_commits(commits, selected)

    assert [commit.commit for commit in expanded] == [
        "A", "B", "C", "D", "E", "F", "M", "N"
    ]
    assert len(episodes) == 1
    assert episodes[0].fork_base == "B"
