from capacity_atlas.data import load_atlas
from capacity_atlas.validate import validate_atlas


def test_seed_data_is_valid() -> None:
    atlas = load_atlas()
    assert atlas.problems
    assert validate_atlas(atlas) == []


def test_problem_ids_are_sorted_and_unique() -> None:
    atlas = load_atlas()
    problem_ids = [problem["id"] for problem in atlas.problems]
    assert problem_ids == sorted(problem_ids)
    assert len(problem_ids) == len(set(problem_ids))
