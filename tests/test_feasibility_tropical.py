import pytest

from tools.feasibility_algebra.tropical import choose_min_plus, tropical_add, tropical_multiply


def test_tropical_add_is_min():
    assert tropical_add(10, 3) == 3


def test_tropical_multiply_is_plus():
    assert tropical_multiply(10, 3) == 13


def test_choose_min_plus_selects_lowest_path():
    assert choose_min_plus([("a", 5), ("b", 2)]) == ("b", 2)


def test_choose_min_plus_rejects_empty():
    with pytest.raises(ValueError):
        choose_min_plus([])
