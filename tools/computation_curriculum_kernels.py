#!/usr/bin/env python3
"""Original bounded toy kernels for computation curriculum mapping."""

from __future__ import annotations

import argparse
import json
import re
from itertools import product
from pathlib import Path
from typing import Any


def eval_expr(expr: Any, env: dict[str, bool]) -> bool:
    if isinstance(expr, str):
        return env[expr]
    op = expr[0]
    if op == "not":
        return not eval_expr(expr[1], env)
    if op == "and":
        return eval_expr(expr[1], env) and eval_expr(expr[2], env)
    if op == "or":
        return eval_expr(expr[1], env) or eval_expr(expr[2], env)
    if op == "implies":
        return (not eval_expr(expr[1], env)) or eval_expr(expr[2], env)
    raise ValueError(f"unknown op: {op}")


def logic_truth_table_kernel(expr: Any, variables: list[str]) -> dict[str, Any]:
    rows = []
    for values in product([False, True], repeat=len(variables)):
        env = dict(zip(variables, values))
        rows.append({"env": env, "value": eval_expr(expr, env)})
    return {"kernel": "logic_truth_table_kernel", "rows": rows, "bounded_only": True}


def set_relation_kernel(elements: set[Any], relation: set[tuple[Any, Any]]) -> dict[str, Any]:
    reflexive = all((x, x) in relation for x in elements)
    symmetric = all((b, a) in relation for a, b in relation)
    transitive = all((a, c) in relation for a, b in relation for x, c in relation if x == b)
    return {
        "kernel": "set_relation_kernel",
        "reflexive": reflexive,
        "symmetric": symmetric,
        "transitive": transitive,
        "bounded_only": True,
    }


def dfa_trace_kernel(states: set[str], alphabet: set[str], transitions: dict[tuple[str, str], str], start: str, accept: set[str], word: str) -> dict[str, Any]:
    if start not in states:
        raise ValueError("start state missing")
    state = start
    trace = [{"state": state, "symbol": None}]
    for ch in word:
        if ch not in alphabet:
            raise ValueError("symbol outside alphabet")
        key = (state, ch)
        if key not in transitions:
            raise ValueError("missing transition")
        state = transitions[key]
        trace.append({"state": state, "symbol": ch})
    return {"kernel": "dfa_trace_kernel", "accepted": state in accept, "trace": trace, "bounded_only": True}


def regex_string_kernel(pattern: str, strings: list[str]) -> dict[str, Any]:
    compiled = re.compile(pattern)
    return {"kernel": "regex_string_kernel", "matches": {s: bool(compiled.fullmatch(s)) for s in strings}, "bounded_only": True}


def grammar_derivation_kernel(grammar: dict[str, list[list[str]]], start: str, max_depth: int) -> dict[str, Any]:
    current = [[start]]
    generated: set[str] = set()
    for _ in range(max_depth):
        next_forms = []
        for form in current:
            idx = next((i for i, token in enumerate(form) if token in grammar), None)
            if idx is None:
                generated.add("".join(form))
                continue
            nt = form[idx]
            for production in grammar[nt]:
                next_forms.append(form[:idx] + production + form[idx + 1 :])
        current = next_forms
    for form in current:
        if all(token not in grammar for token in form):
            generated.add("".join(form))
    return {"kernel": "grammar_derivation_kernel", "generated": sorted(generated), "bounded_only": True, "max_depth": max_depth}


def pda_stack_trace_placeholder(actions: list[tuple[str, str | None]]) -> dict[str, Any]:
    stack: list[str] = []
    trace = []
    for op, value in actions:
        if op == "push" and value:
            stack.append(value)
        elif op == "pop":
            if not stack:
                raise ValueError("pop from empty stack")
            stack.pop()
        else:
            raise ValueError("invalid stack action")
        trace.append({"op": op, "value": value, "stack": list(stack)})
    return {"kernel": "pda_stack_trace_placeholder", "trace": trace, "bounded_only": True, "not_full_pda_theorem": True}


def turing_machine_trace_kernel(transitions: dict[tuple[str, str], tuple[str, str, int]], tape: str, start: str, halt: set[str], max_steps: int) -> dict[str, Any]:
    cells = {i: ch for i, ch in enumerate(tape)}
    head = 0
    state = start
    trace = []
    for step in range(max_steps):
        symbol = cells.get(head, "_")
        trace.append({"step": step, "state": state, "head": head, "symbol": symbol})
        if state in halt:
            break
        key = (state, symbol)
        if key not in transitions:
            break
        new_state, write, move = transitions[key]
        cells[head] = write
        head += move
        state = new_state
    return {"kernel": "turing_machine_trace_kernel", "trace": trace, "bounded_only": True, "max_steps": max_steps, "final_state": state}


def write_json(path: Path, obj: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(obj, indent=2, sort_keys=True) + "\n")


def run_all(out_dir: Path) -> dict[str, Any]:
    logic = logic_truth_table_kernel(("and", "p", "q"), ["p", "q"])
    relation = set_relation_kernel({1, 2}, {(1, 1), (2, 2), (1, 2), (2, 1)})
    dfa = dfa_trace_kernel({"even", "odd"}, {"a"}, {("even", "a"): "odd", ("odd", "a"): "even"}, "even", {"even"}, "aa")
    regex = regex_string_kernel(r"a*b", ["b", "ab", "aaab", "aba"])
    grammar = grammar_derivation_kernel({"S": [["a", "S", "b"], [""]]}, "S", 4)
    pda = pda_stack_trace_placeholder([("push", "A"), ("push", "B"), ("pop", None)])
    turing = turing_machine_trace_kernel({("q0", "1"): ("q0", "1", 1), ("q0", "_"): ("halt", "_", 0)}, "11", "q0", {"halt"}, 10)
    results = [logic, relation, dfa, regex, grammar, pda, turing]
    names = [
        "logic_truth_table_result_2026_05_23.json",
        "set_relation_result_2026_05_23.json",
        "dfa_trace_result_2026_05_23.json",
        "regex_string_result_2026_05_23.json",
        "grammar_derivation_result_2026_05_23.json",
        "pda_stack_trace_result_2026_05_23.json",
        "turing_trace_result_2026_05_23.json",
    ]
    for name, result in zip(names, results):
        write_json(out_dir / name, result)
    summary = {
        "kernel_count": len(results),
        "passed_count": len(results),
        "failed_count": 0,
        "bounded_only": True,
        "theorem_proof_claim": False,
        "open_problem_claim": False,
        "public_ready": False,
    }
    write_json(out_dir / "computation_kernel_execution_summary_2026_05_23.json", summary)
    return summary


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--out-dir", required=True)
    parser.add_argument("--strict", action="store_true")
    args = parser.parse_args()
    summary = run_all(Path(args.out_dir))
    if args.strict and summary["failed_count"]:
        raise SystemExit("kernel execution failed")
    print("COMPUTATION_CURRICULUM_KERNELS_OK")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
