from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path

from generate_frontier_grammar_from_syntax import sym_of, terminal_of
from generate_partial_from_syntax import (
    CATS,
    LIST_CATS,
    PARTIAL_ATOMS,
    Elem,
    Production,
    Rule,
    derive_states,
    field_elems,
    fields_before,
    parse_syntax_rules,
    partial_app,
    subst,
)


ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / "LwRust" / "Extractor" / "Generated" / "FrontierLower.lean"


@dataclass(frozen=True)
class BoundaryGap:
    prod: Production
    dot: int
    partial_src: str
    exact_src: str


DENOTE_FOR_CAT = {
    "cty": ("denoteTy?", "Ty", "PartialTy"),
    "clval": ("denoteLVal?", "LVal", "PartialLVal"),
    "cterm": ("denoteTerm?", "Term", "PartialTerm"),
}

DENOTE_FOR_LIST = {
    "clval": ("denoteLVals?", "List LVal", "PartialLVals"),
    "cterm": ("denoteTerms?", "List Term", "PartialTerms"),
}


LOWER_FOR_CAT = {
    "cty": ("CheckedTyFrontierLower", "PartialTy", "CompletesTy", "denoteTy?"),
    "clval": ("CheckedLValFrontierLower", "PartialLVal", "CompletesLVal", "denoteLVal?"),
    "cterm": ("CheckedTermFrontierLower", "PartialTerm", "CompletesTerm", "denoteTerm?"),
}


LIST_LOWER_FOR_CAT = {
    "clval": {
        "full_cat": "clvals",
        "tail_cat": "clvalsTail",
        "full_relation": "CheckedLValsFrontierLower",
        "tail_relation": "CheckedLValsTailFrontierLower",
        "partial": "PartialLVals",
        "complete": "List LVal",
        "complete_rel": "CompletesLVals",
        "full_denote": "denoteLVals?",
        "tail_denote": "denoteLValsTail?",
        "empty_rule": "clvalsEmptyRule",
        "cons_rule": "clvalsConsRule",
        "tail_empty_rule": "clvalsTailEmptyRule",
        "tail_cons_rule": "clvalsTailConsRule",
        "item_cat": "clval",
        "item_partial": "PartialLVal",
    },
    "cterm": {
        "full_cat": "cterms",
        "tail_cat": "ctermsTail",
        "full_relation": "CheckedTermsFrontierLower",
        "tail_relation": "CheckedTermsTailFrontierLower",
        "partial": "PartialTerms",
        "complete": "List Term",
        "complete_rel": "CompletesTerms",
        "full_denote": "denoteTerms?",
        "tail_denote": "denoteTermsTail?",
        "empty_rule": "ctermsEmptyRule",
        "cons_rule": "ctermsConsRule",
        "tail_empty_rule": "ctermsTailEmptyRule",
        "tail_cons_rule": "ctermsTailConsRule",
        "item_cat": "cterm",
        "item_partial": "PartialTerm",
    },
}


LIST_INFO_BY_GRAMMAR_CAT = {
    info["full_cat"]: (item_cat, False)
    for item_cat, info in LIST_LOWER_FOR_CAT.items()
} | {
    info["tail_cat"]: (item_cat, True)
    for item_cat, info in LIST_LOWER_FOR_CAT.items()
}


def lean_list(items: list[str]) -> str:
    return "[" + ", ".join(items) + "]"


def child_expr_for_elem(elem: Elem, name: str) -> str:
    if elem.kind == "token":
        return f".token .{terminal_of(elem)}"
    if elem.kind == "atom":
        terminal = terminal_of(elem)
        if elem.raw == "ident":
            return f".token (.{terminal} {name})"
        if elem.raw == "num":
            return f".token (.{terminal} {name})"
        if elem.raw == "term":
            return f".token (.{terminal} {name})"
        raise ValueError(elem)
    return f"{name}Tree"


def children_before_or_at(prod: Production, index: int) -> list[str]:
    fields = {i: name for i, _elem, name, _typ in field_elems(prod)}
    out: list[str] = []
    for i, elem in enumerate(prod.elems[: index + 1]):
        out.append(child_expr_for_elem(elem, fields.get(i, f"_field{i}")))
    return out


def children_before(prod: Production, index: int) -> list[str]:
    fields = {i: name for i, _elem, name, _typ in field_elems(prod)}
    out: list[str] = []
    for i, elem in enumerate(prod.elems[:index]):
        out.append(child_expr_for_elem(elem, fields.get(i, f"_field{i}")))
    return out


def children_for_start(prod: Production) -> list[str]:
    if not prod.elems or prod.elems[0].kind != "token":
        raise ValueError(prod.name)
    return [child_expr_for_elem(prod.elems[0], "_token")]


def children_for_complete(prod: Production) -> list[str]:
    return [
        child_expr_for_elem(elem, f"_field{i}")
        for i, elem in enumerate(prod.elems)
    ]


def item_expr(prod: Production, dot: int) -> str:
    return f"({{ rule := {prod.name}Rule, dot := {dot} }} : Item Cat Terminal)"


def item_expr_for_rule(rule_name: str, dot: int) -> str:
    return f"({{ rule := {rule_name}, dot := {dot} }} : Item Cat Terminal)"


def checked_before_type(prod: Production, dot: int, children: list[str]) -> str:
    item = item_expr(prod, dot)
    return (
        "CheckableGrammar.checkSeq checkableGrammar "
        f"{item}.before {lean_list(children)} = Bool.true"
    )


def checked_before_type_for_rule(rule_name: str, dot: int, children: list[str]) -> str:
    item = item_expr_for_rule(rule_name, dot)
    return (
        "CheckableGrammar.checkSeq checkableGrammar "
        f"{item}.before {lean_list(children)} = Bool.true"
    )


def boundary_state_expr(prod: Production, dot: int, children: list[str]) -> str:
    item = item_expr(prod, dot)
    return (
        "(CheckableGrammar.CheckedFrontierState.boundary "
        f"{item} (by native_decide) {lean_list(children)} checkedBefore)"
    )


def boundary_state_expr_for_rule(rule_name: str, dot: int, children: list[str]) -> str:
    item = item_expr_for_rule(rule_name, dot)
    return (
        "(CheckableGrammar.CheckedFrontierState.boundary "
        f"{item} (by native_decide) {lean_list(children)} checkedBefore)"
    )


def descend_state_expr(
    prod: Production,
    dot: int,
    active_cat: str,
    todo: list[str],
    children: list[str],
    child_state: str,
) -> str:
    item = item_expr(prod, dot)
    return (
        "(CheckableGrammar.CheckedFrontierState.descend "
        f"{item} (by native_decide) .{active_cat} {lean_list(todo)} "
        f"(by native_decide) {lean_list(children)} checkedBefore {child_state})"
    )


def descend_state_expr_for_rule(
    rule_name: str,
    dot: int,
    active_cat: str,
    todo: list[str],
    children: list[str],
    child_state: str,
) -> str:
    item = item_expr_for_rule(rule_name, dot)
    return (
        "(CheckableGrammar.CheckedFrontierState.descend "
        f"{item} (by native_decide) .{active_cat} {lean_list(todo)} "
        f"(by native_decide) {lean_list(children)} checkedBefore {child_state})"
    )


def partial_done(elem: Elem, complete_name: str) -> str:
    if elem.kind == "cat":
        partial = CATS[elem.cat][1]
        return f"{partial}.done {complete_name}"
    if elem.kind == "list":
        partial = LIST_CATS[elem.cat][1]
        return f"{partial}.done {complete_name}"
    if elem.kind == "atom" and elem.raw in PARTIAL_ATOMS:
        partial = PARTIAL_ATOMS[elem.raw][1]
        return f"{partial}.done {complete_name}"
    return complete_name


def partial_cutoff(elem: Elem) -> str | None:
    if elem.kind == "cat":
        partial = CATS[elem.cat][1]
        return f"{partial}.cutoff"
    if elem.kind == "list":
        partial = LIST_CATS[elem.cat][1]
        return f"{partial}.cutoff"
    if elem.kind == "atom" and elem.raw in PARTIAL_ATOMS:
        partial = PARTIAL_ATOMS[elem.raw][1]
        return f"{partial}.cutoff"
    return None


def completion_cutoff_premise(elem: Elem) -> str | None:
    if elem.kind == "cat":
        rel = CATS[elem.cat][2]
        return f"_root_.ConservativeExtractor.Generated.{rel}.cutoff"
    if elem.kind == "list":
        rel = LIST_CATS[elem.cat][2]
        return f"_root_.ConservativeExtractor.Generated.{rel}.cutoff"
    if elem.kind == "atom" and elem.raw in PARTIAL_ATOMS:
        rel = PARTIAL_ATOMS[elem.raw][2]
        return f"_root_.ConservativeExtractor.Generated.{rel}.cutoff"
    return None


def qualify_partial_constructors(src: str) -> str:
    for partial in [
        "PartialTy",
        "PartialLVal",
        "PartialTerm",
        "PartialLVals",
        "PartialTerms",
        "PartialName",
    ]:
        src = src.replace(
            f"{partial}.",
            f"_root_.ConservativeExtractor.Generated.{partial}.",
        )
    return src


def relation_constructor_for_rule(rule: Rule, cat: str) -> str:
    return (
        f"_root_.ConservativeExtractor.Generated.{LOWER_FOR_CAT[cat][2]}."
        f"{rule.production.name}_{rule.state_name}"
    )


def premises_for_done_children(prod: Production, index: int) -> list[str]:
    premises: list[str] = []
    for i, elem, name, _typ in field_elems(prod):
        if i > index:
            continue
        if elem.kind == "cat":
            denote, _complete, _partial = DENOTE_FOR_CAT[elem.cat]
            premises.append(f"      ({name}_denotes : {denote} {name}Tree = some {name})")
        elif elem.kind == "list":
            denote, _complete, _partial = DENOTE_FOR_LIST[elem.cat]
            premises.append(f"      ({name}_denotes : {denote} {name}Tree = some {name})")
    return premises


def binders_for_done_children(prod: Production, index: int) -> list[str]:
    binders: list[str] = []
    for i, elem, name, typ in field_elems(prod):
        if i > index:
            continue
        if elem.kind in {"cat", "list"}:
            binders.append(f"      {{{name}Tree : Tree Tok}} {{{name} : {typ}}}")
        else:
            binders.append(f"      {{{name} : {typ}}}")
    return binders


def premises_for_previous_children(prod: Production, index: int) -> list[str]:
    premises: list[str] = []
    for i, elem, name, _typ in field_elems(prod):
        if i >= index:
            continue
        if elem.kind == "cat":
            denote, _complete, _partial = DENOTE_FOR_CAT[elem.cat]
            premises.append(f"      ({name}_denotes : {denote} {name}Tree = some {name})")
        elif elem.kind == "list":
            denote, _complete, _partial = DENOTE_FOR_LIST[elem.cat]
            premises.append(f"      ({name}_denotes : {denote} {name}Tree = some {name})")
    return premises


def binders_for_previous_children(prod: Production, index: int) -> list[str]:
    binders: list[str] = []
    for i, elem, name, typ in field_elems(prod):
        if i >= index:
            continue
        if elem.kind in {"cat", "list"}:
            binders.append(f"      {{{name}Tree : Tree Tok}} {{{name} : {typ}}}")
        else:
            binders.append(f"      {{{name} : {typ}}}")
    return binders


def complete_field_values_for_state(prod: Production, index: int) -> list[tuple[str, str]]:
    out: list[tuple[str, str]] = []
    target_field = None
    target_elem = None
    for i, elem, name, typ in field_elems(prod):
        if i < index:
            out.append((name, typ))
        if i == index:
            target_field = (name, typ)
            target_elem = elem
    if target_field is None or target_elem is None:
        raise ValueError((prod.name, index))
    name, typ = target_field
    out.append((partial_done(target_elem, name), typ))
    return out


def partial_field_values_for_descend(prod: Production, index: int) -> list[tuple[str, str]]:
    out: list[tuple[str, str]] = []
    target_field = None
    target_elem = None
    for i, elem, name, typ in field_elems(prod):
        if i < index:
            out.append((name, typ))
        if i == index:
            target_field = (name, typ)
            target_elem = elem
    if target_field is None or target_elem is None:
        raise ValueError((prod.name, index))
    name, _typ = target_field
    if target_elem.kind == "cat":
        out.append((name, CATS[target_elem.cat][1]))
        return out
    if target_elem.kind == "list":
        out.append((name, LIST_CATS[target_elem.cat][1]))
        return out
    if target_elem.kind != "cat":
        raise ValueError((prod.name, index, target_elem.kind))
    raise AssertionError("unreachable")


def child_lower_for_elem(elem: Elem) -> tuple[str, str, str, str, str]:
    if elem.kind == "cat":
        relation, partial, complete_rel, denote = LOWER_FOR_CAT[elem.cat]
        return elem.cat, relation, partial, complete_rel, denote
    if elem.kind == "list":
        info = LIST_LOWER_FOR_CAT[elem.cat]
        return (
            info["full_cat"],
            info["full_relation"],
            info["partial"],
            info["complete_rel"],
            info["full_denote"],
        )
    raise ValueError((elem.kind, elem.raw))


def render_boundary_constructor(rule: Rule, cat: str) -> list[str]:
    prod = rule.production
    assert rule.index is not None
    dot = rule.index + 1
    children = children_before_or_at(prod, rule.index)
    fields = complete_field_values_for_state(prod, rule.index)
    relation, partial, _complete_rel, _denote = LOWER_FOR_CAT[cat]
    state = qualify_partial_constructors(
        partial_app(partial, rule.state_name, fields))
    lines = [
        f"  | {prod.name}_{rule.state_name}_boundary",
        *binders_for_done_children(prod, rule.index),
        *premises_for_done_children(prod, rule.index),
        f"      {{checkedBefore : {checked_before_type(prod, dot, children)}}} :",
        f"      {relation}",
        f"        {boundary_state_expr(prod, dot, children)}",
        f"        ({state})",
    ]
    return lines


def render_start_constructor(rule: Rule, cat: str) -> list[str]:
    prod = rule.production
    children = children_for_start(prod)
    relation, partial, _complete_rel, _denote = LOWER_FOR_CAT[cat]
    state = qualify_partial_constructors(
        partial_app(partial, rule.state_name, rule.fields))
    lines = [
        f"  | {prod.name}_{rule.state_name}_boundary",
        f"      {{checkedBefore : {checked_before_type(prod, 1, children)}}} :",
        f"      {relation}",
        f"        {boundary_state_expr(prod, 1, children)}",
        f"        ({state})",
    ]
    return lines


def done_partial_expr_for_prod(prod: Production) -> str:
    partial = CATS[prod.target_cat][1]
    ast = subst(prod.ast, {})
    return qualify_partial_constructors(f"{partial}.done ({ast})")


def render_done_constructor(prod: Production, cat: str) -> list[str]:
    dot = len(prod.elems)
    children = children_for_complete(prod)
    relation, _partial, _complete_rel, _denote = LOWER_FOR_CAT[cat]
    state = done_partial_expr_for_prod(prod)
    lines = [
        f"  | {prod.name}_done_boundary",
        f"      {{checkedBefore : {checked_before_type(prod, dot, children)}}} :",
        f"      {relation}",
        f"        {boundary_state_expr(prod, dot, children)}",
        f"        ({state})",
    ]
    return lines


def render_boundary_gap_constructor(gap: BoundaryGap, cat: str) -> list[str]:
    prod = gap.prod
    children = children_before(prod, gap.dot)
    relation, _partial, _complete_rel, _denote = LOWER_FOR_CAT[cat]
    lines = [
        f"  | {prod.name}_dot{gap.dot}_boundary",
        *binders_for_previous_children(prod, gap.dot),
        *premises_for_previous_children(prod, gap.dot),
        f"      {{checkedBefore : {checked_before_type(prod, gap.dot, children)}}} :",
        f"      {relation}",
        f"        {boundary_state_expr(prod, gap.dot, children)}",
        f"        ({gap.partial_src})",
    ]
    return lines


def render_descend_constructor(rule: Rule, cat: str) -> list[str]:
    prod = rule.production
    assert rule.index is not None
    elem = prod.elems[rule.index]
    assert elem.kind in {"cat", "list"}
    dot = rule.index
    done_children = children_before(prod, rule.index)
    todo = [sym_of(todo_elem) for todo_elem in prod.elems[rule.index + 1 :]]
    relation, partial, _complete_rel, _denote = LOWER_FOR_CAT[cat]
    child_cat, child_relation, child_partial, _child_complete_rel, _child_denote = (
        child_lower_for_elem(elem)
    )
    fname = next(name for i, _elem, name, _typ in field_elems(prod) if i == rule.index)
    fields = partial_field_values_for_descend(prod, rule.index)
    state = qualify_partial_constructors(
        partial_app(partial, rule.state_name, fields))
    lines = [
        f"  | {prod.name}_{rule.state_name}_descend",
        *binders_for_previous_children(prod, rule.index),
        *premises_for_previous_children(prod, rule.index),
        f"      {{{fname}State : CheckableGrammar.CheckedFrontierState checkableGrammar .{child_cat}}}",
        f"      {{{fname} : {child_partial}}}",
        f"      ({fname}_lower : {child_relation} {fname}State {fname})",
        f"      {{checkedBefore : {checked_before_type(prod, dot, done_children)}}} :",
        f"      {relation}",
        f"        {descend_state_expr(prod, dot, child_cat, todo, done_children, f'{fname}State')}",
        f"        ({state})",
    ]
    return lines


def completion_premise_for_rule(rule: Rule) -> str | None:
    if rule.index is None:
        return None
    prod = rule.production
    elem = prod.elems[rule.index]
    if elem.kind == "cat":
        rel = CATS[elem.cat][2]
        return f"_root_.ConservativeExtractor.Generated.{rel}.done"
    if elem.kind == "list":
        rel = LIST_CATS[elem.cat][2]
        return f"_root_.ConservativeExtractor.Generated.{rel}.done"
    if elem.kind == "atom" and elem.raw in PARTIAL_ATOMS:
        rel = PARTIAL_ATOMS[elem.raw][2]
        return f"_root_.ConservativeExtractor.Generated.{rel}.done"
    return None


def simp_args_for_rule(prod: Production) -> list[str]:
    return [
        "CheckableGrammar.CheckedFrontierState.rawCompletion",
        "CheckableGrammar.Defaults.completeBoundaryRaw",
        "defaults",
        f"{prod.name}Rule",
        "Item.after",
        "CheckableGrammar.Defaults.defaultSeq",
        "CheckableGrammar.Defaults.defaultSymTree",
        "defaultTree",
        "defaultToken",
        "denoteTerm?",
        "denoteLVal?",
        "denoteTerms?",
        "denoteTermsTail?",
        "denoteLVals?",
        "denoteLValsTail?",
        "denoteTy?",
    ]


def render_boundary_soundness_case(rule: Rule, cat: str) -> list[str]:
    prod = rule.production
    case_name = f"{prod.name}_{rule.state_name}_boundary"
    relation_constructor = (
        f"_root_.ConservativeExtractor.Generated.{LOWER_FOR_CAT[cat][2]}."
        f"{prod.name}_{rule.state_name}"
    )
    premise = completion_premise_for_rule(rule)
    exact = relation_constructor if premise is None else f"{relation_constructor} {premise}"
    return [
        f"  | {case_name} =>",
        "      simp_all [" + ", ".join(simp_args_for_rule(prod)) + "]",
        "      subst completed",
        f"      exact {exact}",
    ]


def render_done_soundness_case(prod: Production, cat: str) -> list[str]:
    complete_rel = LOWER_FOR_CAT[cat][2]
    return [
        f"  | {prod.name}_done_boundary =>",
        "      simp_all [" + ", ".join(simp_args_for_rule(prod)) + "]",
        "      subst completed",
        f"      exact _root_.ConservativeExtractor.Generated.{complete_rel}.done",
    ]


def render_boundary_gap_soundness_case(gap: BoundaryGap) -> list[str]:
    prod = gap.prod
    return [
        f"  | {prod.name}_dot{gap.dot}_boundary =>",
        "      simp_all [" + ", ".join(simp_args_for_rule(prod)) + "]",
        "      subst completed",
        f"      exact {gap.exact_src}",
    ]


def child_soundness_theorem(cat: str) -> str:
    return {
        "cty": "checkedTyFrontierLower_completes_of_rawDenotes",
        "clval": "checkedLValFrontierLower_completes_of_rawDenotes",
        "cterm": "checkedTermFrontierLower_completes_of_rawDenotes",
        "clvals": "checkedLValsFrontierLower_completes_of_rawDenotes",
        "clvalsTail": "checkedLValsTailFrontierLower_completes_of_rawDenotes",
        "cterms": "checkedTermsFrontierLower_completes_of_rawDenotes",
        "ctermsTail": "checkedTermsTailFrontierLower_completes_of_rawDenotes",
    }[cat]


def list_relation_stem(item_cat: str) -> str:
    return {
        "clval": "LVals",
        "cterm": "Terms",
    }[item_cat]


def list_state_soundness_theorem(item_cat: str, tail: bool) -> str:
    suffix = "Tail" if tail else ""
    return (
        f"checked{list_relation_stem(item_cat)}{suffix}"
        "FrontierLower_completes_of_stateCompletes"
    )


def list_simp_args(rule_name: str) -> list[str]:
    return [
        "CheckableGrammar.CheckedFrontierState.rawCompletion",
        "CheckableGrammar.Defaults.completeBoundaryRaw",
        "defaults",
        rule_name,
        "Item.after",
        "CheckableGrammar.Defaults.defaultSeq",
        "CheckableGrammar.Defaults.defaultSymTree",
        "defaultTree",
        "defaultToken",
        "denoteTerm?",
        "denoteLVal?",
        "denoteTerms?",
        "denoteTermsTail?",
        "denoteLVals?",
        "denoteLValsTail?",
        "denoteTy?",
    ]


def render_list_lower_inductive(item_cat: str, tail: bool) -> list[str]:
    info = LIST_LOWER_FOR_CAT[item_cat]
    cat = info["tail_cat"] if tail else info["full_cat"]
    relation = info["tail_relation"] if tail else info["full_relation"]
    partial = info["partial"]
    empty_rule = info["tail_empty_rule"] if tail else info["empty_rule"]
    cons_rule = info["tail_cons_rule"] if tail else info["cons_rule"]
    item_cat_name = info["item_cat"]
    item_partial = info["item_partial"]

    lines = [
        f"inductive {relation} :",
        f"    CheckableGrammar.CheckedFrontierState checkableGrammar .{cat} →",
        f"    {partial} → Prop where",
        f"  | fallback",
        f"      {{state : CheckableGrammar.CheckedFrontierState checkableGrammar .{cat}}} :",
        f"      {relation}",
        f"        state",
        f"        (_root_.ConservativeExtractor.Generated.{partial}.cutoff)",
        "",
        f"  | {empty_rule[:-4]}_done_boundary",
        f"      {{checkedBefore : {checked_before_type_for_rule(empty_rule, 0, [])}}} :",
        f"      {relation}",
        f"        {boundary_state_expr_for_rule(empty_rule, 0, [])}",
        f"        (_root_.ConservativeExtractor.Generated.{partial}.done [])",
        "",
        f"  | {cons_rule[:-4]}_start_boundary",
        f"      {{checkedBefore : {checked_before_type_for_rule(cons_rule, 0, [])}}} :",
        f"      {relation}",
        f"        {boundary_state_expr_for_rule(cons_rule, 0, [])}",
        f"        (_root_.ConservativeExtractor.Generated.{partial}.elems [] none)",
    ]
    if tail:
        comma_children = [".token .comma"]
        lines.extend(
            [
                "",
                f"  | {cons_rule[:-4]}_comma_boundary",
                f"      {{checkedBefore : {checked_before_type_for_rule(cons_rule, 1, comma_children)}}} :",
                f"      {relation}",
                f"        {boundary_state_expr_for_rule(cons_rule, 1, comma_children)}",
                f"        (_root_.ConservativeExtractor.Generated.{partial}.elems [] none)",
            ]
        )
        head_dot = 2
        head_children = [".token .comma", "headTree"]
        done_dot = 3
        done_children = [".token .comma", "headTree", "tailTree"]
        descend_head_dot = 1
        descend_head_children = [".token .comma"]
        descend_tail_dot = 2
        descend_tail_children = [".token .comma", "headTree"]
    else:
        head_dot = 1
        head_children = ["headTree"]
        done_dot = 2
        done_children = ["headTree", "tailTree"]
        descend_head_dot = 0
        descend_head_children = []
        descend_tail_dot = 1
        descend_tail_children = ["headTree"]

    lines.extend(
        [
            "",
            f"  | {cons_rule[:-4]}_head_boundary",
            f"      {{headTree : Tree Tok}}",
            f"      {{checkedBefore : {checked_before_type_for_rule(cons_rule, head_dot, head_children)}}} :",
            f"      {relation}",
            f"        {boundary_state_expr_for_rule(cons_rule, head_dot, head_children)}",
            f"        (_root_.ConservativeExtractor.Generated.{partial}.elems [] none)",
            "",
            f"  | {cons_rule[:-4]}_done_boundary",
            f"      {{headTree tailTree : Tree Tok}}",
            f"      {{checkedBefore : {checked_before_type_for_rule(cons_rule, done_dot, done_children)}}} :",
            f"      {relation}",
            f"        {boundary_state_expr_for_rule(cons_rule, done_dot, done_children)}",
            f"        (_root_.ConservativeExtractor.Generated.{partial}.elems [] none)",
            "",
            f"  | {cons_rule[:-4]}_head_descend",
            f"      {{headState : CheckableGrammar.CheckedFrontierState checkableGrammar .{item_cat_name}}}",
            f"      {{checkedBefore : {checked_before_type_for_rule(cons_rule, descend_head_dot, descend_head_children)}}} :",
            f"      {relation}",
            f"        {descend_state_expr_for_rule(cons_rule, descend_head_dot, item_cat_name, ['.cat .' + info['tail_cat']], descend_head_children, 'headState')}",
            f"        (_root_.ConservativeExtractor.Generated.{partial}.elems [] none)",
            "",
            f"  | {cons_rule[:-4]}_tail_descend",
            f"      {{headTree : Tree Tok}}",
            f"      {{tailState : CheckableGrammar.CheckedFrontierState checkableGrammar .{info['tail_cat']}}}",
            f"      {{checkedBefore : {checked_before_type_for_rule(cons_rule, descend_tail_dot, descend_tail_children)}}} :",
            f"      {relation}",
            f"        {descend_state_expr_for_rule(cons_rule, descend_tail_dot, info['tail_cat'], [], descend_tail_children, 'tailState')}",
            f"        (_root_.ConservativeExtractor.Generated.{partial}.elems [] none)",
        ]
    )
    return lines


def render_list_soundness_theorem(item_cat: str, tail: bool) -> list[str]:
    info = LIST_LOWER_FOR_CAT[item_cat]
    cat = info["tail_cat"] if tail else info["full_cat"]
    relation = info["tail_relation"] if tail else info["full_relation"]
    partial = info["partial"]
    complete = info["complete"]
    complete_rel = info["complete_rel"]
    denote = info["tail_denote"] if tail else info["full_denote"]
    empty_rule = info["tail_empty_rule"] if tail else info["empty_rule"]
    cons_rule = info["tail_cons_rule"] if tail else info["cons_rule"]
    cons_prefix = cons_rule[:-4]
    empty_prefix = empty_rule[:-4]
    cons_cases = [
        f"{cons_prefix}_start_boundary",
        f"{cons_prefix}_head_boundary",
        f"{cons_prefix}_done_boundary",
        f"{cons_prefix}_head_descend",
        f"{cons_prefix}_tail_descend",
    ]
    if tail:
        cons_cases.insert(1, f"{cons_prefix}_comma_boundary")

    lines = [
        "",
        "set_option linter.unusedSimpArgs false in",
        f"theorem {child_soundness_theorem(cat)}",
        f"    {{state : CheckableGrammar.CheckedFrontierState checkableGrammar .{cat}}}",
        f"    {{frontier : {partial}}} {{completed : {complete}}}",
        f"    (hlower : {relation} state frontier)",
        "    (hdenotes :",
        f"      {denote} (state.rawCompletion defaults).tree = some completed) :",
        f"    {complete_rel} frontier completed := by",
        "  cases hlower with",
        "  | fallback =>",
        "      exact _root_.ConservativeExtractor.Generated."
        f"{complete_rel}.cutoff",
        f"  | {empty_prefix}_done_boundary =>",
        "      simp_all [" + ", ".join(list_simp_args(empty_rule)) + "]",
        "      subst completed",
        f"      exact _root_.ConservativeExtractor.Generated.{complete_rel}.done",
    ]
    for case_name in cons_cases:
        lines.extend(
            [
                f"  | {case_name} =>",
                "      exact _root_.ConservativeExtractor.Generated."
                f"{complete_rel}.elemsDone",
            ]
        )
    return lines


def render_list_state_completion_soundness_theorem(
    item_cat: str,
    tail: bool,
) -> list[str]:
    info = LIST_LOWER_FOR_CAT[item_cat]
    cat = info["tail_cat"] if tail else info["full_cat"]
    relation = info["tail_relation"] if tail else info["full_relation"]
    partial = info["partial"]
    complete = info["complete"]
    complete_rel = info["complete_rel"]
    empty_rule = info["tail_empty_rule"] if tail else info["empty_rule"]
    cons_rule = info["tail_cons_rule"] if tail else info["cons_rule"]
    relation_stem = list_relation_stem(item_cat)
    denotes_rel = f"Denotes{relation_stem}{'Tail' if tail else ''}"
    empty_prefix = empty_rule[:-4]
    cons_prefix = cons_rule[:-4]
    cons_cases = [
        f"{cons_prefix}_start_boundary",
        f"{cons_prefix}_head_boundary",
        f"{cons_prefix}_done_boundary",
        f"{cons_prefix}_head_descend",
        f"{cons_prefix}_tail_descend",
    ]
    if tail:
        cons_cases.insert(1, f"{cons_prefix}_comma_boundary")

    lines = [
        "",
        "set_option linter.unusedSimpArgs false in",
        f"theorem {list_state_soundness_theorem(item_cat, tail)}",
        f"    {{state : CheckableGrammar.CheckedFrontierState checkableGrammar .{cat}}}",
        f"    {{frontier : {partial}}} {{tree : Tree Tok}} {{completed : {complete}}}",
        f"    (hlower : {relation} state frontier)",
        "    (hcomplete : CheckableGrammar.CheckedFrontierStateCompletes",
        "      checkableGrammar state tree)",
        f"    (hdenotes : {denotes_rel} tree completed) :",
        f"    {complete_rel} frontier completed := by",
        "  cases hlower with",
        "  | fallback =>",
        "      exact _root_.ConservativeExtractor.Generated."
        f"{complete_rel}.cutoff",
        f"  | {empty_prefix}_done_boundary =>",
        "      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=",
        "        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete",
        "      cases hdenotes with",
        f"      | {empty_prefix} =>",
        "          exact _root_.ConservativeExtractor.Generated."
        f"{complete_rel}.done",
        f"      | {cons_prefix} hhead htail =>",
        f"          simp [{empty_rule}] at htree",
    ]
    for case_name in cons_cases:
        lines.extend(
            [
                f"  | {case_name} =>",
                "      exact _root_.ConservativeExtractor.Generated."
                f"{complete_rel}.elemsDone",
            ]
        )
    return lines


def render_list_coverage_theorem(item_cat: str, tail: bool) -> list[str]:
    info = LIST_LOWER_FOR_CAT[item_cat]
    cat = info["tail_cat"] if tail else info["full_cat"]
    relation = info["tail_relation"] if tail else info["full_relation"]
    partial = info["partial"]
    suffix = "Tail" if tail else ""
    item_suffix = "LVal" if item_cat == "clval" else "Term"
    theorem_name = f"checked{item_suffix}s{suffix}FrontierLower_exists"
    return [
        "",
        f"theorem {theorem_name}",
        f"    (state : CheckableGrammar.CheckedFrontierState checkableGrammar .{cat}) :",
        f"    ∃ frontier : {partial}, {relation} state frontier := by",
        f"  exact ⟨_root_.ConservativeExtractor.Generated.{partial}.cutoff,",
        f"    {relation}.fallback⟩",
    ]


def render_descend_soundness_case(rule: Rule, cat: str) -> list[str]:
    prod = rule.production
    assert rule.index is not None
    elem = prod.elems[rule.index]
    assert elem.kind in {"cat", "list"}
    fname = next(name for i, _elem, name, _typ in field_elems(prod) if i == rule.index)
    case_name = f"{prod.name}_{rule.state_name}_descend"
    relation_constructor = (
        f"_root_.ConservativeExtractor.Generated.{LOWER_FOR_CAT[cat][2]}."
        f"{prod.name}_{rule.state_name}"
    )
    previous_premise_names = [
        f"{name}_denotes"
        for i, previous_elem, name, _typ in field_elems(prod)
        if i < rule.index and previous_elem.kind in {"cat", "list"}
    ]
    child_cat, _child_relation, _child_partial, _child_complete_rel, _child_denote = (
        child_lower_for_elem(elem)
    )
    if elem.kind == "cat" and elem.cat == cat:
        child_proof = f"({fname}_ih {fname}_denotes)"
        case_arg_names = previous_premise_names + [f"{fname}_lower", f"{fname}_ih"]
    else:
        child_proof = (
            f"({child_soundness_theorem(child_cat)} {fname}_lower "
            f"{fname}_denotes)"
        )
        case_arg_names = previous_premise_names + [f"{fname}_lower"]
    case_args = " ".join(case_arg_names)
    return [
        f"  | {case_name} {case_args} =>",
        "      simp_all [" + ", ".join(simp_args_for_rule(prod)) + "]",
        "      simp only [Option.bind_eq_some_iff] at hdenotes",
        f"      obtain ⟨{fname}Completed, {fname}_denotes, hcompleted⟩ := hdenotes",
        "      simp at hcompleted",
        "      subst completed",
        f"      exact {relation_constructor} {child_proof}",
    ]


def render_soundness_theorem(
    cat: str,
    done_prods: list[Production],
    boundary_gaps: list[BoundaryGap],
    rules: list[Rule],
    descend_rules: list[Rule],
) -> list[str]:
    relation, partial, complete_rel, denote = LOWER_FOR_CAT[cat]
    lines = [
        "",
        "set_option linter.unusedSimpArgs false in",
        f"theorem {child_soundness_theorem(cat)}",
        f"    {{state : CheckableGrammar.CheckedFrontierState checkableGrammar .{cat}}}",
        f"    {{frontier : {partial}}} {{completed : {CATS[cat][0]}}}",
        f"    (hlower : {relation} state frontier)",
        "    (hdenotes :",
        f"      {denote} (state.rawCompletion defaults).tree = some completed) :",
        f"    {complete_rel} frontier completed := by",
        "  induction hlower generalizing completed with",
        "  | fallback =>",
        f"      exact _root_.ConservativeExtractor.Generated.{complete_rel}.cutoff",
    ]
    for prod in done_prods:
        lines.extend(render_done_soundness_case(prod, cat))
    for gap in boundary_gaps:
        lines.extend(render_boundary_gap_soundness_case(gap))
    for rule in rules:
        lines.extend(render_boundary_soundness_case(rule, cat))
    for rule in descend_rules:
        lines.extend(render_descend_soundness_case(rule, cat))
    return lines


def render_coverage_theorem(cat: str) -> list[str]:
    relation, partial, _complete_rel, _denote = LOWER_FOR_CAT[cat]
    cat_title = {
        "cty": "Ty",
        "clval": "LVal",
        "cterm": "Term",
    }[cat]
    return [
        "",
        f"theorem checked{cat_title}FrontierLower_exists",
        f"    (state : CheckableGrammar.CheckedFrontierState checkableGrammar .{cat}) :",
        f"    ∃ frontier : {partial}, {relation} state frontier := by",
        f"  exact ⟨_root_.ConservativeExtractor.Generated.{partial}.cutoff,",
        f"    {relation}.fallback⟩",
    ]


def render_ty_state_completion_soundness_theorem() -> list[str]:
    return [
        "",
        "set_option linter.unusedSimpArgs false in",
        "theorem checkedTyFrontierLower_completes_of_stateCompletes",
        "    {state : CheckableGrammar.CheckedFrontierState checkableGrammar .cty}",
        "    {frontier : PartialTy} {tree : Tree Tok} {completed : Ty}",
        "    (hlower : CheckedTyFrontierLower state frontier)",
        "    (hcomplete : CheckableGrammar.CheckedFrontierStateCompletes",
        "      checkableGrammar state tree)",
        "    (hdenotes : DenotesTy tree completed) :",
        "    CompletesTy frontier completed := by",
        "  induction hlower generalizing tree completed with",
        "  | fallback =>",
        "      exact _root_.ConservativeExtractor.Generated.CompletesTy.cutoff",
        "  | ctyUnit_done_boundary =>",
        "      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=",
        "        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete",
        "      cases hdenotes <;> simp [ctyUnitRule] at htree",
        "      exact _root_.ConservativeExtractor.Generated.CompletesTy.done",
        "  | ctyInt_done_boundary =>",
        "      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=",
        "        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete",
        "      cases hdenotes <;> simp [ctyIntRule] at htree",
        "      exact _root_.ConservativeExtractor.Generated.CompletesTy.done",
        "  | ctyBool_done_boundary =>",
        "      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=",
        "        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete",
        "      cases hdenotes <;> simp [ctyBoolRule] at htree",
        "      exact _root_.ConservativeExtractor.Generated.CompletesTy.done",
        "  | ctyUnit_dot0_boundary =>",
        "      exact _root_.ConservativeExtractor.Generated.CompletesTy.cutoff",
        "  | ctyInt_dot0_boundary =>",
        "      exact _root_.ConservativeExtractor.Generated.CompletesTy.cutoff",
        "  | ctyBool_dot0_boundary =>",
        "      exact _root_.ConservativeExtractor.Generated.CompletesTy.cutoff",
        "  | ctyBorrowShared_dot0_boundary =>",
        "      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=",
        "        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete",
        "      cases hdenotes <;> simp [ctyBorrowSharedRule] at htree",
        "      exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBorrowShared_borrowSharedTargets",
        "        _root_.ConservativeExtractor.Generated.CompletesLVals.cutoff",
        "  | ctyBorrowShared_dot2_boundary =>",
        "      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=",
        "        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete",
        "      cases hdenotes <;> simp [ctyBorrowSharedRule] at htree",
        "      exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBorrowShared_borrowSharedTargets",
        "        _root_.ConservativeExtractor.Generated.CompletesLVals.cutoff",
        "  | ctyBorrowShared_dot4_boundary targets_denotes =>",
        "      rename_i stateTargetsTree stateTargets checkedBefore",
        "      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=",
        "        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete",
        "      cases hdenotes <;> simp [ctyBorrowSharedRule] at htree",
        "      rename_i actualTargetsTree actualTargets htargets",
        "      rcases htree with ⟨hTreeEq, _⟩",
        "      have hactual : denoteLVals? actualTargetsTree = some actualTargets :=",
        "        denoteLVals?_complete_of_denotes htargets",
        "      rw [hTreeEq] at hactual",
        "      rw [targets_denotes] at hactual",
        "      simp at hactual",
        "      subst actualTargets",
        "      exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBorrowShared_borrowSharedTargets",
        "        _root_.ConservativeExtractor.Generated.CompletesLVals.done",
        "  | ctyBorrowMut_dot0_boundary =>",
        "      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=",
        "        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete",
        "      cases hdenotes <;> simp [ctyBorrowMutRule] at htree",
        "      exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBorrowMut_borrowMutTargets",
        "        _root_.ConservativeExtractor.Generated.CompletesLVals.cutoff",
        "  | ctyBorrowMut_dot2_boundary =>",
        "      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=",
        "        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete",
        "      cases hdenotes <;> simp [ctyBorrowMutRule] at htree",
        "      exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBorrowMut_borrowMutTargets",
        "        _root_.ConservativeExtractor.Generated.CompletesLVals.cutoff",
        "  | ctyBorrowMut_dot3_boundary =>",
        "      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=",
        "        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete",
        "      cases hdenotes <;> simp [ctyBorrowMutRule] at htree",
        "      exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBorrowMut_borrowMutTargets",
        "        _root_.ConservativeExtractor.Generated.CompletesLVals.cutoff",
        "  | ctyBorrowMut_dot5_boundary targets_denotes =>",
        "      rename_i stateTargetsTree stateTargets checkedBefore",
        "      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=",
        "        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete",
        "      cases hdenotes <;> simp [ctyBorrowMutRule] at htree",
        "      rename_i actualTargetsTree actualTargets htargets",
        "      rcases htree with ⟨hTreeEq, _⟩",
        "      have hactual : denoteLVals? actualTargetsTree = some actualTargets :=",
        "        denoteLVals?_complete_of_denotes htargets",
        "      rw [hTreeEq] at hactual",
        "      rw [targets_denotes] at hactual",
        "      simp at hactual",
        "      subst actualTargets",
        "      exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBorrowMut_borrowMutTargets",
        "        _root_.ConservativeExtractor.Generated.CompletesLVals.done",
        "  | ctyBox_dot0_boundary =>",
        "      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=",
        "        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete",
        "      cases hdenotes <;> simp [ctyBoxRule] at htree",
        "      exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBox_boxElement",
        "        _root_.ConservativeExtractor.Generated.CompletesTy.cutoff",
        "  | ctyBorrowShared_borrowSharedTargets_boundary targets_denotes =>",
        "      rename_i stateTargetsTree stateTargets checkedBefore",
        "      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=",
        "        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete",
        "      cases hdenotes <;> simp [ctyBorrowSharedRule] at htree",
        "      rename_i actualTargetsTree actualTargets htargets",
        "      rcases htree with ⟨hTreeEq, _⟩",
        "      have hactual : denoteLVals? actualTargetsTree = some actualTargets :=",
        "        denoteLVals?_complete_of_denotes htargets",
        "      rw [hTreeEq] at hactual",
        "      rw [targets_denotes] at hactual",
        "      simp at hactual",
        "      subst actualTargets",
        "      exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBorrowShared_borrowSharedTargets",
        "        _root_.ConservativeExtractor.Generated.CompletesLVals.done",
        "  | ctyBorrowMut_borrowMutTargets_boundary targets_denotes =>",
        "      rename_i stateTargetsTree stateTargets checkedBefore",
        "      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=",
        "        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete",
        "      cases hdenotes <;> simp [ctyBorrowMutRule] at htree",
        "      rename_i actualTargetsTree actualTargets htargets",
        "      rcases htree with ⟨hTreeEq, _⟩",
        "      have hactual : denoteLVals? actualTargetsTree = some actualTargets :=",
        "        denoteLVals?_complete_of_denotes htargets",
        "      rw [hTreeEq] at hactual",
        "      rw [targets_denotes] at hactual",
        "      simp at hactual",
        "      subst actualTargets",
        "      exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBorrowMut_borrowMutTargets",
        "        _root_.ConservativeExtractor.Generated.CompletesLVals.done",
        "  | ctyBox_boxElement_boundary element_denotes =>",
        "      rename_i stateElementTree stateElement checkedBefore",
        "      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=",
        "        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete",
        "      cases hdenotes <;> simp [ctyBoxRule] at htree",
        "      rename_i actualElementTree actualElement helement",
        "      rcases htree with ⟨hTreeEq, _⟩",
        "      have hactual : denoteTy? actualElementTree = some actualElement :=",
        "        denoteTy?_complete_of_denotes helement",
        "      rw [hTreeEq] at hactual",
        "      rw [element_denotes] at hactual",
        "      simp at hactual",
        "      subst actualElement",
        "      exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBox_boxElement",
        "        _root_.ConservativeExtractor.Generated.CompletesTy.done",
        "  | ctyBorrowShared_borrowSharedStart_boundary =>",
        "      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=",
        "        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete",
        "      cases hdenotes <;> simp [ctyBorrowSharedRule] at htree",
        "      exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBorrowShared_borrowSharedStart",
        "  | ctyBorrowMut_borrowSharedStart_boundary =>",
        "      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=",
        "        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete",
        "      cases hdenotes <;> simp [ctyBorrowMutRule] at htree",
        "      exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBorrowMut_borrowSharedStart",
        "  | ctyBox_boxStart_boundary =>",
        "      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=",
        "        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete",
        "      cases hdenotes <;> simp [ctyBoxRule] at htree",
        "      exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBox_boxStart",
        "  | ctyBorrowShared_borrowSharedTargets_descend targets_lower =>",
        "      obtain ⟨childTree, _suffix, futureChildren, htree, hchild, _hfuture⟩ :=",
        "        CheckableGrammar.CheckedFrontierStateCompletes.descend_inv hcomplete",
        "      cases hdenotes <;> simp [ctyBorrowSharedRule] at htree",
        "      rename_i actualTargetsTree actualTargets htargets",
        "      rcases htree with ⟨hchildEq, _⟩",
        "      rw [← hchildEq] at hchild",
        "      exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBorrowShared_borrowSharedTargets",
        "        (checkedLValsFrontierLower_completes_of_stateCompletes",
        "          targets_lower hchild htargets)",
        "  | ctyBorrowMut_borrowMutTargets_descend targets_lower =>",
        "      obtain ⟨childTree, _suffix, futureChildren, htree, hchild, _hfuture⟩ :=",
        "        CheckableGrammar.CheckedFrontierStateCompletes.descend_inv hcomplete",
        "      cases hdenotes <;> simp [ctyBorrowMutRule] at htree",
        "      rename_i actualTargetsTree actualTargets htargets",
        "      rcases htree with ⟨hchildEq, _⟩",
        "      rw [← hchildEq] at hchild",
        "      exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBorrowMut_borrowMutTargets",
        "        (checkedLValsFrontierLower_completes_of_stateCompletes",
        "          targets_lower hchild htargets)",
        "  | ctyBox_boxElement_descend element_lower element_ih =>",
        "      obtain ⟨childTree, _suffix, futureChildren, htree, hchild, _hfuture⟩ :=",
        "        CheckableGrammar.CheckedFrontierStateCompletes.descend_inv hcomplete",
        "      cases hdenotes <;> simp [ctyBoxRule] at htree",
        "      rename_i actualElementTree actualElement helement",
        "      rcases htree with ⟨hchildEq, _⟩",
        "      rw [← hchildEq] at hchild",
        "      exact _root_.ConservativeExtractor.Generated.CompletesTy.ctyBox_boxElement",
        "        (element_ih hchild helement)",
    ]


def render_lval_state_completion_soundness_theorem() -> list[str]:
    return [
        "",
        "set_option linter.unusedSimpArgs false in",
        "theorem checkedLValFrontierLower_completes_of_stateCompletes",
        "    {state : CheckableGrammar.CheckedFrontierState checkableGrammar .clval}",
        "    {frontier : PartialLVal} {tree : Tree Tok} {completed : LVal}",
        "    (hlower : CheckedLValFrontierLower state frontier)",
        "    (hcomplete : CheckableGrammar.CheckedFrontierStateCompletes",
        "      checkableGrammar state tree)",
        "    (hdenotes : DenotesLVal tree completed) :",
        "    CompletesLVal frontier completed := by",
        "  induction hlower generalizing tree completed with",
        "  | fallback =>",
        "      exact _root_.ConservativeExtractor.Generated.CompletesLVal.cutoff",
        "  | clvalVar_dot0_boundary =>",
        "      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=",
        "        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete",
        "      cases hdenotes with",
        "      | clvalVar =>",
        "          exact _root_.ConservativeExtractor.Generated.CompletesLVal.clvalVar_varX",
        "            _root_.ConservativeExtractor.Generated.CompletesName.cutoff",
        "      | clvalDeref hoperand =>",
        "          simp [clvalVarRule] at htree",
        "  | clvalDeref_dot0_boundary =>",
        "      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=",
        "        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete",
        "      cases hdenotes with",
        "      | clvalVar =>",
        "          simp [clvalDerefRule] at htree",
        "      | clvalDeref hoperand =>",
        "          exact _root_.ConservativeExtractor.Generated.CompletesLVal.clvalDeref_derefOperand",
        "            _root_.ConservativeExtractor.Generated.CompletesLVal.cutoff",
        "  | clvalVar_varX_boundary =>",
        "      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=",
        "        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete",
        "      cases hdenotes with",
        "      | clvalVar =>",
        "          simp [clvalVarRule] at htree",
        "          rcases htree with ⟨hname, _⟩",
        "          rw [hname]",
        "          exact _root_.ConservativeExtractor.Generated.CompletesLVal.clvalVar_varX",
        "            _root_.ConservativeExtractor.Generated.CompletesName.done",
        "      | clvalDeref hoperand =>",
        "          simp [clvalVarRule] at htree",
        "  | clvalDeref_derefOperand_boundary operand_denotes =>",
        "      rename_i stateOperandTree stateOperand checkedBefore",
        "      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=",
        "        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete",
        "      cases hdenotes with",
        "      | clvalVar =>",
        "          simp [clvalDerefRule] at htree",
        "      | clvalDeref hoperand =>",
        "          rename_i actualOperandTree actualOperand",
        "          simp [clvalDerefRule] at htree",
        "          rcases htree with ⟨hTreeEq, _⟩",
        "          have hactual : denoteLVal? actualOperandTree = some actualOperand :=",
        "            denoteLVal?_complete_of_denotes hoperand",
        "          rw [hTreeEq] at hactual",
        "          rw [operand_denotes] at hactual",
        "          simp at hactual",
        "          subst actualOperand",
        "          exact _root_.ConservativeExtractor.Generated.CompletesLVal.clvalDeref_derefOperand",
        "            _root_.ConservativeExtractor.Generated.CompletesLVal.done",
        "  | clvalDeref_derefStart_boundary =>",
        "      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=",
        "        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete",
        "      cases hdenotes with",
        "      | clvalVar =>",
        "          simp [clvalDerefRule] at htree",
        "      | clvalDeref hoperand =>",
        "          exact _root_.ConservativeExtractor.Generated.CompletesLVal.clvalDeref_derefStart",
        "  | clvalDeref_derefOperand_descend operand_lower operand_ih =>",
        "      obtain ⟨childTree, _suffix, futureChildren, htree, hchild, _hfuture⟩ :=",
        "        CheckableGrammar.CheckedFrontierStateCompletes.descend_inv hcomplete",
        "      cases hdenotes with",
        "      | clvalVar =>",
        "          simp [clvalDerefRule] at htree",
        "      | clvalDeref hoperand =>",
        "          rename_i actualOperandTree actualOperand",
        "          simp [clvalDerefRule] at htree",
        "          rcases htree with ⟨hchildEq, _⟩",
        "          rw [← hchildEq] at hchild",
        "          exact _root_.ConservativeExtractor.Generated.CompletesLVal.clvalDeref_derefOperand",
        "            (operand_ih hchild hoperand)",
    ]


def render_term_state_completion_soundness_theorem() -> list[str]:
    return r"""

private theorem term_eq_of_denote_eq {stateTree actualTree : Tree Tok}
    {stateTerm actualTerm : Term}
    (hstate : denoteTerm? stateTree = some stateTerm)
    (hactual : DenotesTerm actualTree actualTerm)
    (htree : actualTree = stateTree) :
    stateTerm = actualTerm := by
  subst actualTree
  have hactual' : denoteTerm? stateTree = some actualTerm :=
    denoteTerm?_complete_of_denotes hactual
  rw [hstate] at hactual'
  simpa using hactual'

private theorem lval_eq_of_denote_eq {stateTree actualTree : Tree Tok}
    {stateLVal actualLVal : LVal}
    (hstate : denoteLVal? stateTree = some stateLVal)
    (hactual : DenotesLVal actualTree actualLVal)
    (htree : actualTree = stateTree) :
    stateLVal = actualLVal := by
  subst actualTree
  have hactual' : denoteLVal? stateTree = some actualLVal :=
    denoteLVal?_complete_of_denotes hactual
  rw [hstate] at hactual'
  simpa using hactual'

private theorem terms_eq_of_denote_eq {stateTree actualTree : Tree Tok}
    {stateTerms actualTerms : List Term}
    (hstate : denoteTerms? stateTree = some stateTerms)
    (hactual : DenotesTerms actualTree actualTerms)
    (htree : actualTree = stateTree) :
    stateTerms = actualTerms := by
  subst actualTree
  have hactual' : denoteTerms? stateTree = some actualTerms :=
    denoteTerms?_complete_of_denotes hactual
  rw [hstate] at hactual'
  simpa using hactual'

set_option linter.unusedSimpArgs false in
theorem checkedTermFrontierLower_completes_of_stateCompletes
    {state : CheckableGrammar.CheckedFrontierState checkableGrammar .cterm}
    {frontier : PartialTerm} {tree : Tree Tok} {completed : Term}
    (hlower : CheckedTermFrontierLower state frontier)
    (hcomplete : CheckableGrammar.CheckedFrontierStateCompletes
      checkableGrammar state tree)
    (hdenotes : DenotesTerm tree completed) :
    CompletesTerm frontier completed := by
  induction hlower generalizing tree completed with
  | fallback =>
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.cutoff
  | ctermUnit_done_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermUnitRule] at htree
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.done
  | ctermTrue_done_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermTrueRule] at htree
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.done
  | ctermFalse_done_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermFalseRule] at htree
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.done
  | ctermUnit_dot0_boundary =>
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.cutoff
  | ctermInt_dot0_boundary =>
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.cutoff
  | ctermTrue_dot0_boundary =>
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.cutoff
  | ctermFalse_dot0_boundary =>
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.cutoff
  | ctermBlock_dot0_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermBlockRule] at htree
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBlock_blockStart
  | ctermBlock_dot2_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermBlockRule] at htree
      rename_i actualLifetime actualTermsTree actualTerms hterms
      rcases htree with ⟨hlifetimeEq, _⟩
      subst actualLifetime
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBlock_blockTerms
        _root_.ConservativeExtractor.Generated.CompletesTerms.cutoff
  | ctermBlock_dot3_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermBlockRule] at htree
      rename_i actualLifetime actualTermsTree actualTerms hterms
      rcases htree with ⟨hlifetimeEq, _⟩
      subst actualLifetime
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBlock_blockTerms
        _root_.ConservativeExtractor.Generated.CompletesTerms.cutoff
  | ctermBlock_dot5_boundary terms_denotes =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermBlockRule] at htree
      rename_i actualLifetime actualTermsTree actualTerms hterms
      rcases htree with ⟨hlifetimeEq, htermsTreeEq, _⟩
      subst actualLifetime
      have htermsEq := terms_eq_of_denote_eq terms_denotes hterms htermsTreeEq
      subst actualTerms
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBlock_blockTerms
        _root_.ConservativeExtractor.Generated.CompletesTerms.done
  | ctermLetMut_dot0_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermLetMutRule] at htree
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermLetMut_letMutName
        _root_.ConservativeExtractor.Generated.CompletesName.cutoff
  | ctermLetMut_dot2_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermLetMutRule] at htree
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermLetMut_letMutName
        _root_.ConservativeExtractor.Generated.CompletesName.cutoff
  | ctermLetMut_dot4_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermLetMutRule] at htree
      rename_i actualName actualInitialiserTree actualInitialiser hinitialiser
      rcases htree with ⟨hnameEq, _⟩
      subst actualName
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermLetMut_letMutInitialiser
        _root_.ConservativeExtractor.Generated.CompletesTerm.cutoff
  | ctermAssign_dot0_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermAssignRule] at htree
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermAssign_assignLhs
        _root_.ConservativeExtractor.Generated.CompletesLVal.cutoff
  | ctermAssign_dot2_boundary lhs_denotes =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermAssignRule] at htree
      rename_i actualLhsTree actualRhsTree actualLhs actualRhs hlhs hrhs
      rcases htree with ⟨hlhsTreeEq, _⟩
      have hlhsEq := lval_eq_of_denote_eq lhs_denotes hlhs hlhsTreeEq
      subst actualLhs
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermAssign_assignRhs
        _root_.ConservativeExtractor.Generated.CompletesTerm.cutoff
  | ctermBox_dot0_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermBoxRule] at htree
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBox_boxOperand
        _root_.ConservativeExtractor.Generated.CompletesTerm.cutoff
  | ctermBorrowShared_dot0_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermBorrowSharedRule] at htree
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBorrowShared_borrowSharedOperand
        _root_.ConservativeExtractor.Generated.CompletesLVal.cutoff
  | ctermBorrowMut_dot0_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermBorrowMutRule] at htree
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBorrowMut_borrowMutOperand
        _root_.ConservativeExtractor.Generated.CompletesLVal.cutoff
  | ctermBorrowMut_dot2_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermBorrowMutRule] at htree
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBorrowMut_borrowMutOperand
        _root_.ConservativeExtractor.Generated.CompletesLVal.cutoff
  | ctermMove_dot0_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermMoveRule] at htree
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermMove_moveOperand
        _root_.ConservativeExtractor.Generated.CompletesLVal.cutoff
  | ctermCopy_dot0_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermCopyRule] at htree
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermCopy_copyOperand
        _root_.ConservativeExtractor.Generated.CompletesLVal.cutoff
  | ctermEq_dot0_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermEqRule] at htree
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermEq_termPrefix
        _root_.ConservativeExtractor.Generated.CompletesTerm.cutoff
  | ctermEq_dot2_boundary lhs_denotes =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermEqRule] at htree
      rename_i actualLhsTree actualRhsTree actualLhs actualRhs hlhs hrhs
      rcases htree with ⟨hlhsTreeEq, _⟩
      have hlhsEq := term_eq_of_denote_eq lhs_denotes hlhs hlhsTreeEq
      subst actualLhs
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermEq_eqRhs
        _root_.ConservativeExtractor.Generated.CompletesTerm.cutoff
  | ctermIte_dot0_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermIteRule] at htree
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermIte_iteCondition
        _root_.ConservativeExtractor.Generated.CompletesTerm.cutoff
  | ctermIte_dot4_boundary condition_denotes trueBranch_denotes =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermIteRule] at htree
      rename_i actualConditionTree actualTrueTree actualFalseTree actualCondition actualTrue actualFalse hcondition htrue hfalse
      rcases htree with ⟨hconditionTreeEq, htrueTreeEq, _⟩
      have hconditionEq :=
        term_eq_of_denote_eq condition_denotes hcondition hconditionTreeEq
      have htrueEq :=
        term_eq_of_denote_eq trueBranch_denotes htrue htrueTreeEq
      subst actualCondition
      subst actualTrue
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermIte_iteFalseBranch
        _root_.ConservativeExtractor.Generated.CompletesTerm.cutoff
  | ctermWhile_dot0_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermWhileRule] at htree
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermWhile_whileStart
  | ctermWhile_dot2_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermWhileRule] at htree
      rename_i actualBodyLifetime actualConditionTree actualBodyTree actualCondition actualBody hcondition hbody
      rcases htree with ⟨hlifetimeEq, _⟩
      subst actualBodyLifetime
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermWhile_whileCondition
        _root_.ConservativeExtractor.Generated.CompletesTerm.cutoff
  | ctermInt_intN_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermIntRule] at htree
      rename_i actualN
      rcases htree with ⟨hnEq, _⟩
      subst actualN
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermInt_intN
  | ctermBlock_blockTerms_boundary terms_denotes =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermBlockRule] at htree
      rename_i actualLifetime actualTermsTree actualTerms hterms
      rcases htree with ⟨hlifetimeEq, htermsTreeEq, _⟩
      subst actualLifetime
      have htermsEq := terms_eq_of_denote_eq terms_denotes hterms htermsTreeEq
      subst actualTerms
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBlock_blockTerms
        _root_.ConservativeExtractor.Generated.CompletesTerms.done
  | ctermLetMut_letMutName_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermLetMutRule] at htree
      rename_i actualName actualInitialiserTree actualInitialiser hinitialiser
      rcases htree with ⟨hnameEq, _⟩
      subst actualName
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermLetMut_letMutName
        _root_.ConservativeExtractor.Generated.CompletesName.done
  | ctermLetMut_letMutInitialiser_boundary initialiser_denotes =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermLetMutRule] at htree
      rename_i actualName actualInitialiserTree actualInitialiser hinitialiser
      rcases htree with ⟨hnameEq, hinitialiserTreeEq, _⟩
      subst actualName
      have hinitialiserEq :=
        term_eq_of_denote_eq initialiser_denotes hinitialiser hinitialiserTreeEq
      subst actualInitialiser
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermLetMut_letMutInitialiser
        _root_.ConservativeExtractor.Generated.CompletesTerm.done
  | ctermAssign_assignLhs_boundary lhs_denotes =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermAssignRule] at htree
      rename_i actualLhsTree actualRhsTree actualLhs actualRhs hlhs hrhs
      rcases htree with ⟨hlhsTreeEq, _⟩
      have hlhsEq := lval_eq_of_denote_eq lhs_denotes hlhs hlhsTreeEq
      subst actualLhs
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermAssign_assignLhs
        _root_.ConservativeExtractor.Generated.CompletesLVal.done
  | ctermAssign_assignRhs_boundary lhs_denotes rhs_denotes =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermAssignRule] at htree
      rename_i actualLhsTree actualRhsTree actualLhs actualRhs hlhs hrhs
      rcases htree with ⟨hlhsTreeEq, hrhsTreeEq, _⟩
      have hlhsEq := lval_eq_of_denote_eq lhs_denotes hlhs hlhsTreeEq
      have hrhsEq := term_eq_of_denote_eq rhs_denotes hrhs hrhsTreeEq
      subst actualLhs
      subst actualRhs
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermAssign_assignRhs
        _root_.ConservativeExtractor.Generated.CompletesTerm.done
  | ctermBox_boxOperand_boundary operand_denotes =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermBoxRule] at htree
      rename_i actualOperandTree actualOperand hoperand
      rcases htree with ⟨hoperandTreeEq, _⟩
      have hoperandEq := term_eq_of_denote_eq operand_denotes hoperand hoperandTreeEq
      subst actualOperand
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBox_boxOperand
        _root_.ConservativeExtractor.Generated.CompletesTerm.done
  | ctermBorrowShared_borrowSharedOperand_boundary operand_denotes =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermBorrowSharedRule] at htree
      rename_i actualOperandTree actualOperand hoperand
      rcases htree with ⟨hoperandTreeEq, _⟩
      have hoperandEq := lval_eq_of_denote_eq operand_denotes hoperand hoperandTreeEq
      subst actualOperand
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBorrowShared_borrowSharedOperand
        _root_.ConservativeExtractor.Generated.CompletesLVal.done
  | ctermBorrowMut_borrowMutOperand_boundary operand_denotes =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermBorrowMutRule] at htree
      rename_i actualOperandTree actualOperand hoperand
      rcases htree with ⟨hoperandTreeEq, _⟩
      have hoperandEq := lval_eq_of_denote_eq operand_denotes hoperand hoperandTreeEq
      subst actualOperand
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBorrowMut_borrowMutOperand
        _root_.ConservativeExtractor.Generated.CompletesLVal.done
  | ctermMove_moveOperand_boundary operand_denotes =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermMoveRule] at htree
      rename_i actualOperandTree actualOperand hoperand
      rcases htree with ⟨hoperandTreeEq, _⟩
      have hoperandEq := lval_eq_of_denote_eq operand_denotes hoperand hoperandTreeEq
      subst actualOperand
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermMove_moveOperand
        _root_.ConservativeExtractor.Generated.CompletesLVal.done
  | ctermCopy_copyOperand_boundary operand_denotes =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermCopyRule] at htree
      rename_i actualOperandTree actualOperand hoperand
      rcases htree with ⟨hoperandTreeEq, _⟩
      have hoperandEq := lval_eq_of_denote_eq operand_denotes hoperand hoperandTreeEq
      subst actualOperand
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermCopy_copyOperand
        _root_.ConservativeExtractor.Generated.CompletesLVal.done
  | ctermEq_termPrefix_boundary lhs_denotes =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermEqRule] at htree
      rename_i actualLhsTree actualRhsTree actualLhs actualRhs hlhs hrhs
      rcases htree with ⟨hlhsTreeEq, _⟩
      have hlhsEq := term_eq_of_denote_eq lhs_denotes hlhs hlhsTreeEq
      subst actualLhs
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermEq_termPrefix
        _root_.ConservativeExtractor.Generated.CompletesTerm.done
  | ctermEq_eqRhs_boundary lhs_denotes rhs_denotes =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermEqRule] at htree
      rename_i actualLhsTree actualRhsTree actualLhs actualRhs hlhs hrhs
      rcases htree with ⟨hlhsTreeEq, hrhsTreeEq, _⟩
      have hlhsEq := term_eq_of_denote_eq lhs_denotes hlhs hlhsTreeEq
      have hrhsEq := term_eq_of_denote_eq rhs_denotes hrhs hrhsTreeEq
      subst actualLhs
      subst actualRhs
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermEq_eqRhs
        _root_.ConservativeExtractor.Generated.CompletesTerm.done
  | ctermIte_iteCondition_boundary condition_denotes =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermIteRule] at htree
      rename_i actualConditionTree actualTrueTree actualFalseTree actualCondition actualTrue actualFalse hcondition htrue hfalse
      rcases htree with ⟨hconditionTreeEq, _⟩
      have hconditionEq :=
        term_eq_of_denote_eq condition_denotes hcondition hconditionTreeEq
      subst actualCondition
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermIte_iteCondition
        _root_.ConservativeExtractor.Generated.CompletesTerm.done
  | ctermIte_iteTrueBranch_boundary condition_denotes trueBranch_denotes =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermIteRule] at htree
      rename_i actualConditionTree actualTrueTree actualFalseTree actualCondition actualTrue actualFalse hcondition htrue hfalse
      rcases htree with ⟨hconditionTreeEq, htrueTreeEq, _⟩
      have hconditionEq :=
        term_eq_of_denote_eq condition_denotes hcondition hconditionTreeEq
      have htrueEq :=
        term_eq_of_denote_eq trueBranch_denotes htrue htrueTreeEq
      subst actualCondition
      subst actualTrue
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermIte_iteTrueBranch
        _root_.ConservativeExtractor.Generated.CompletesTerm.done
  | ctermIte_iteFalseBranch_boundary condition_denotes trueBranch_denotes falseBranch_denotes =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermIteRule] at htree
      rename_i actualConditionTree actualTrueTree actualFalseTree actualCondition actualTrue actualFalse hcondition htrue hfalse
      rcases htree with ⟨hconditionTreeEq, htrueTreeEq, hfalseTreeEq, _⟩
      have hconditionEq :=
        term_eq_of_denote_eq condition_denotes hcondition hconditionTreeEq
      have htrueEq :=
        term_eq_of_denote_eq trueBranch_denotes htrue htrueTreeEq
      have hfalseEq :=
        term_eq_of_denote_eq falseBranch_denotes hfalse hfalseTreeEq
      subst actualCondition
      subst actualTrue
      subst actualFalse
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermIte_iteFalseBranch
        _root_.ConservativeExtractor.Generated.CompletesTerm.done
  | ctermWhile_whileCondition_boundary condition_denotes =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermWhileRule] at htree
      rename_i actualBodyLifetime actualConditionTree actualBodyTree actualCondition actualBody hcondition hbody
      rcases htree with ⟨hlifetimeEq, hconditionTreeEq, _⟩
      subst actualBodyLifetime
      have hconditionEq :=
        term_eq_of_denote_eq condition_denotes hcondition hconditionTreeEq
      subst actualCondition
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermWhile_whileCondition
        _root_.ConservativeExtractor.Generated.CompletesTerm.done
  | ctermWhile_whileBody_boundary condition_denotes body_denotes =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermWhileRule] at htree
      rename_i actualBodyLifetime actualConditionTree actualBodyTree actualCondition actualBody hcondition hbody
      rcases htree with ⟨hlifetimeEq, hconditionTreeEq, hbodyTreeEq, _⟩
      subst actualBodyLifetime
      have hconditionEq :=
        term_eq_of_denote_eq condition_denotes hcondition hconditionTreeEq
      have hbodyEq := term_eq_of_denote_eq body_denotes hbody hbodyTreeEq
      subst actualCondition
      subst actualBody
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermWhile_whileBody
        _root_.ConservativeExtractor.Generated.CompletesTerm.done
  | ctermBlock_blockStart_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermBlockRule] at htree
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBlock_blockStart
  | ctermLetMut_letMutStart_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermLetMutRule] at htree
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermLetMut_letMutStart
  | ctermBox_boxStart_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermBoxRule] at htree
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBox_boxStart
  | ctermBorrowShared_borrowSharedStart_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermBorrowSharedRule] at htree
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBorrowShared_borrowSharedStart
  | ctermBorrowMut_borrowSharedStart_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermBorrowMutRule] at htree
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBorrowMut_borrowSharedStart
  | ctermCopy_copyStart_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermCopyRule] at htree
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermCopy_copyStart
  | ctermIte_iteStart_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermIteRule] at htree
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermIte_iteStart
  | ctermWhile_whileStart_boundary =>
      obtain ⟨_suffix, _futureChildren, htree, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.boundary_inv hcomplete
      cases hdenotes <;> simp [ctermWhileRule] at htree
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermWhile_whileStart
  | ctermBlock_blockTerms_descend terms_lower =>
      obtain ⟨childTree, _suffix, futureChildren, htree, hchild, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.descend_inv hcomplete
      cases hdenotes <;> simp [ctermBlockRule] at htree
      rename_i actualLifetime actualTermsTree actualTerms hterms
      rcases htree with ⟨hlifetimeEq, hchildEq, _⟩
      subst actualLifetime
      rw [← hchildEq] at hchild
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBlock_blockTerms
        (checkedTermsFrontierLower_completes_of_stateCompletes
          terms_lower hchild hterms)
  | ctermLetMut_letMutInitialiser_descend initialiser_lower initialiser_ih =>
      obtain ⟨childTree, _suffix, futureChildren, htree, hchild, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.descend_inv hcomplete
      cases hdenotes <;> simp [ctermLetMutRule] at htree
      rename_i actualName actualInitialiserTree actualInitialiser hinitialiser
      rcases htree with ⟨hnameEq, hchildEq, _⟩
      subst actualName
      rw [← hchildEq] at hchild
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermLetMut_letMutInitialiser
        (initialiser_ih hchild hinitialiser)
  | ctermAssign_assignLhs_descend lhs_lower =>
      obtain ⟨childTree, _suffix, futureChildren, htree, hchild, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.descend_inv hcomplete
      cases hdenotes <;> simp [ctermAssignRule] at htree
      rename_i actualLhsTree actualRhsTree actualLhs actualRhs hlhs hrhs
      rcases htree with ⟨hchildEq, _⟩
      rw [← hchildEq] at hchild
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermAssign_assignLhs
        (checkedLValFrontierLower_completes_of_stateCompletes
          lhs_lower hchild hlhs)
  | ctermAssign_assignRhs_descend lhs_denotes rhs_lower rhs_ih =>
      obtain ⟨childTree, _suffix, futureChildren, htree, hchild, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.descend_inv hcomplete
      cases hdenotes <;> simp [ctermAssignRule] at htree
      rename_i actualLhsTree actualRhsTree actualLhs actualRhs hlhs hrhs
      rcases htree with ⟨hlhsTreeEq, hchildEq, _⟩
      have hlhsEq := lval_eq_of_denote_eq lhs_denotes hlhs hlhsTreeEq
      subst actualLhs
      rw [← hchildEq] at hchild
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermAssign_assignRhs
        (rhs_ih hchild hrhs)
  | ctermBox_boxOperand_descend operand_lower operand_ih =>
      obtain ⟨childTree, _suffix, futureChildren, htree, hchild, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.descend_inv hcomplete
      cases hdenotes <;> simp [ctermBoxRule] at htree
      rename_i actualOperandTree actualOperand hoperand
      rcases htree with ⟨hchildEq, _⟩
      rw [← hchildEq] at hchild
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBox_boxOperand
        (operand_ih hchild hoperand)
  | ctermBorrowShared_borrowSharedOperand_descend operand_lower =>
      obtain ⟨childTree, _suffix, futureChildren, htree, hchild, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.descend_inv hcomplete
      cases hdenotes <;> simp [ctermBorrowSharedRule] at htree
      rename_i actualOperandTree actualOperand hoperand
      rcases htree with ⟨hchildEq, _⟩
      rw [← hchildEq] at hchild
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBorrowShared_borrowSharedOperand
        (checkedLValFrontierLower_completes_of_stateCompletes
          operand_lower hchild hoperand)
  | ctermBorrowMut_borrowMutOperand_descend operand_lower =>
      obtain ⟨childTree, _suffix, futureChildren, htree, hchild, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.descend_inv hcomplete
      cases hdenotes <;> simp [ctermBorrowMutRule] at htree
      rename_i actualOperandTree actualOperand hoperand
      rcases htree with ⟨hchildEq, _⟩
      rw [← hchildEq] at hchild
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermBorrowMut_borrowMutOperand
        (checkedLValFrontierLower_completes_of_stateCompletes
          operand_lower hchild hoperand)
  | ctermMove_moveOperand_descend operand_lower =>
      obtain ⟨childTree, _suffix, futureChildren, htree, hchild, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.descend_inv hcomplete
      cases hdenotes <;> simp [ctermMoveRule] at htree
      rename_i actualOperandTree actualOperand hoperand
      rcases htree with ⟨hchildEq, _⟩
      rw [← hchildEq] at hchild
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermMove_moveOperand
        (checkedLValFrontierLower_completes_of_stateCompletes
          operand_lower hchild hoperand)
  | ctermCopy_copyOperand_descend operand_lower =>
      obtain ⟨childTree, _suffix, futureChildren, htree, hchild, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.descend_inv hcomplete
      cases hdenotes <;> simp [ctermCopyRule] at htree
      rename_i actualOperandTree actualOperand hoperand
      rcases htree with ⟨hchildEq, _⟩
      rw [← hchildEq] at hchild
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermCopy_copyOperand
        (checkedLValFrontierLower_completes_of_stateCompletes
          operand_lower hchild hoperand)
  | ctermEq_termPrefix_descend lhs_lower lhs_ih =>
      obtain ⟨childTree, _suffix, futureChildren, htree, hchild, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.descend_inv hcomplete
      cases hdenotes <;> simp [ctermEqRule] at htree
      rename_i actualLhsTree actualRhsTree actualLhs actualRhs hlhs hrhs
      rcases htree with ⟨hchildEq, _⟩
      rw [← hchildEq] at hchild
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermEq_termPrefix
        (lhs_ih hchild hlhs)
  | ctermEq_eqRhs_descend lhs_denotes rhs_lower rhs_ih =>
      obtain ⟨childTree, _suffix, futureChildren, htree, hchild, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.descend_inv hcomplete
      cases hdenotes <;> simp [ctermEqRule] at htree
      rename_i actualLhsTree actualRhsTree actualLhs actualRhs hlhs hrhs
      rcases htree with ⟨hlhsTreeEq, hchildEq, _⟩
      have hlhsEq := term_eq_of_denote_eq lhs_denotes hlhs hlhsTreeEq
      subst actualLhs
      rw [← hchildEq] at hchild
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermEq_eqRhs
        (rhs_ih hchild hrhs)
  | ctermIte_iteCondition_descend condition_lower condition_ih =>
      obtain ⟨childTree, _suffix, futureChildren, htree, hchild, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.descend_inv hcomplete
      cases hdenotes <;> simp [ctermIteRule] at htree
      rename_i actualConditionTree actualTrueTree actualFalseTree actualCondition actualTrue actualFalse hcondition htrue hfalse
      rcases htree with ⟨hchildEq, _⟩
      rw [← hchildEq] at hchild
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermIte_iteCondition
        (condition_ih hchild hcondition)
  | ctermIte_iteTrueBranch_descend condition_denotes trueBranch_lower trueBranch_ih =>
      obtain ⟨childTree, _suffix, futureChildren, htree, hchild, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.descend_inv hcomplete
      cases hdenotes <;> simp [ctermIteRule] at htree
      rename_i actualConditionTree actualTrueTree actualFalseTree actualCondition actualTrue actualFalse hcondition htrue hfalse
      rcases htree with ⟨hconditionTreeEq, hchildEq, _⟩
      have hconditionEq :=
        term_eq_of_denote_eq condition_denotes hcondition hconditionTreeEq
      subst actualCondition
      rw [← hchildEq] at hchild
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermIte_iteTrueBranch
        (trueBranch_ih hchild htrue)
  | ctermIte_iteFalseBranch_descend condition_denotes trueBranch_denotes falseBranch_lower falseBranch_ih =>
      obtain ⟨childTree, _suffix, futureChildren, htree, hchild, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.descend_inv hcomplete
      cases hdenotes <;> simp [ctermIteRule] at htree
      rename_i actualConditionTree actualTrueTree actualFalseTree actualCondition actualTrue actualFalse hcondition htrue hfalse
      rcases htree with ⟨hconditionTreeEq, htrueTreeEq, hchildEq, _⟩
      have hconditionEq :=
        term_eq_of_denote_eq condition_denotes hcondition hconditionTreeEq
      have htrueEq :=
        term_eq_of_denote_eq trueBranch_denotes htrue htrueTreeEq
      subst actualCondition
      subst actualTrue
      rw [← hchildEq] at hchild
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermIte_iteFalseBranch
        (falseBranch_ih hchild hfalse)
  | ctermWhile_whileCondition_descend condition_lower condition_ih =>
      obtain ⟨childTree, _suffix, futureChildren, htree, hchild, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.descend_inv hcomplete
      cases hdenotes <;> simp [ctermWhileRule] at htree
      rename_i actualBodyLifetime actualConditionTree actualBodyTree actualCondition actualBody hcondition hbody
      rcases htree with ⟨hlifetimeEq, hchildEq, _⟩
      subst actualBodyLifetime
      rw [← hchildEq] at hchild
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermWhile_whileCondition
        (condition_ih hchild hcondition)
  | ctermWhile_whileBody_descend condition_denotes body_lower body_ih =>
      obtain ⟨childTree, _suffix, futureChildren, htree, hchild, _hfuture⟩ :=
        CheckableGrammar.CheckedFrontierStateCompletes.descend_inv hcomplete
      cases hdenotes <;> simp [ctermWhileRule] at htree
      rename_i actualBodyLifetime actualConditionTree actualBodyTree actualCondition actualBody hcondition hbody
      rcases htree with ⟨hlifetimeEq, hconditionTreeEq, hchildEq, _⟩
      subst actualBodyLifetime
      have hconditionEq :=
        term_eq_of_denote_eq condition_denotes hcondition hconditionTreeEq
      subst actualCondition
      rw [← hchildEq] at hchild
      exact _root_.ConservativeExtractor.Generated.CompletesTerm.ctermWhile_whileBody
        (body_ih hchild hbody)
""".strip("\n").splitlines()


def render_decoder_assisted_coverage_theorems() -> list[str]:
    lines: list[str] = []
    for kind, rule_name, dot, before_children, partial_constructor in [
        (
            "BorrowShared",
            "ctyBorrowSharedRule",
            3,
            "[.token .amp, .token .lbrack, targetsTree]",
            "borrowSharedTargets",
        ),
        (
            "BorrowMut",
            "ctyBorrowMutRule",
            4,
            "[.token .amp, .token .mutKw, .token .lbrack, targetsTree]",
            "borrowMutTargets",
        ),
    ]:
        theorem_name = (
            f"checkedTyFrontierLower_cty{kind}Targets_boundary_exists"
        )
        lines.extend([
            "",
            "set_option linter.unusedSimpArgs false in",
            f"theorem {theorem_name}",
            "    {targetsTree : Tree Tok}",
            "    {checkedBefore :",
            "      CheckableGrammar.checkSeq checkableGrammar",
            f"        ({{ rule := {rule_name}, dot := {dot} }} : Item Cat Terminal).before",
            f"        {before_children} = Bool.true}} :",
            "    ∃ targets : List LVal,",
            "      CheckedTyFrontierLower",
            "        (CheckableGrammar.CheckedFrontierState.boundary",
            f"          ({{ rule := {rule_name}, dot := {dot} }} : Item Cat Terminal)",
            f"          (by native_decide) {before_children}",
            "          checkedBefore)",
            f"        (_root_.ConservativeExtractor.Generated.PartialTy.{partial_constructor}",
            "          (_root_.ConservativeExtractor.Generated.PartialLVals.done targets)) := by",
            "  have htargets :",
            "      CheckableGrammar.checkTree checkableGrammar .clvals targetsTree =",
            "        Bool.true := by",
            f"    simpa [{rule_name}, Item.before, CheckableGrammar.checkSeq,",
            "      checkableGrammar, acceptsBool] using checkedBefore",
            "  obtain ⟨targets, htargetsDenote⟩ :=",
            "    checkedLValsTree_denote_exists htargets",
            "  exact ⟨targets,",
            f"    CheckedTyFrontierLower.cty{kind}_{partial_constructor}_boundary",
            "      htargetsDenote⟩",
        ])
    return lines


def all_field_binders(prod: Production) -> list[tuple[str, str]]:
    return [(name, typ) for _i, _elem, name, typ in field_elems(prod)]


def complete_term_expr_for_rule(rule: Rule) -> str:
    prod = rule.production
    return subst(prod.ast, {name: name for name, _typ in all_field_binders(prod)})


def partial_expr_for_rule(rule: Rule) -> str:
    prod = rule.production
    partial = CATS[prod.target_cat][1]
    if rule.index is None:
        fields = rule.fields
    else:
        fields = complete_field_values_for_state(prod, rule.index)
    return qualify_partial_constructors(partial_app(partial, rule.state_name, fields))


def render_completion_shape_theorem(rule: Rule, cat: str) -> list[str]:
    prod = rule.production
    theorem_base = f"{prod.name}_{rule.state_name}_boundary"
    binders = "".join(f" {{{name} : {typ}}}" for name, typ in all_field_binders(prod))
    relation_constructor = (
        f"_root_.ConservativeExtractor.Generated.{LOWER_FOR_CAT[cat][2]}."
        f"{prod.name}_{rule.state_name}"
    )
    premise = completion_premise_for_rule(rule)
    exact = relation_constructor if premise is None else f"{relation_constructor} {premise}"
    return [
        "",
        f"theorem {theorem_base}_completes{binders} :",
        f"    {LOWER_FOR_CAT[cat][2]} ({partial_expr_for_rule(rule)})",
        f"      ({complete_term_expr_for_rule(rule)}) := by",
        f"  exact {exact}",
    ]


def render_done_completion_shape_theorem(prod: Production, cat: str) -> list[str]:
    theorem_base = f"{prod.name}_done_boundary"
    complete_rel = LOWER_FOR_CAT[cat][2]
    complete_src = subst(prod.ast, {})
    return [
        "",
        f"theorem {theorem_base}_completes :",
        f"    {complete_rel} ({done_partial_expr_for_prod(prod)})",
        f"      ({complete_src}) := by",
        f"  exact _root_.ConservativeExtractor.Generated.{complete_rel}.done",
    ]


def render_boundary_gap_completion_shape_theorem(
    gap: BoundaryGap,
    cat: str,
) -> list[str]:
    prod = gap.prod
    theorem_base = f"{prod.name}_dot{gap.dot}_boundary"
    binders = "".join(f" {{{name} : {typ}}}" for name, typ in all_field_binders(prod))
    complete_src = subst(prod.ast, {name: name for name, _typ in all_field_binders(prod)})
    return [
        "",
        f"theorem {theorem_base}_completes{binders} :",
        f"    {LOWER_FOR_CAT[cat][2]} ({gap.partial_src})",
        f"      ({complete_src}) := by",
        f"  exact {gap.exact_src}",
    ]


def render_descend_completion_shape_theorem(rule: Rule, cat: str) -> list[str]:
    prod = rule.production
    assert rule.index is not None
    elem = prod.elems[rule.index]
    assert elem.kind in {"cat", "list"}
    fname = next(name for i, _elem, name, _typ in field_elems(prod) if i == rule.index)
    theorem_base = f"{prod.name}_{rule.state_name}_descend"
    binders: list[tuple[str, str]] = []
    names: dict[str, str] = {}
    child_cat, _child_relation, child_partial, child_rel, _child_denote = (
        child_lower_for_elem(elem)
    )
    for i, _elem, name, typ in field_elems(prod):
        if i < rule.index:
            binders.append((name, typ))
            names[name] = name
        elif i == rule.index:
            binders.append((fname, child_partial))
            completed = f"{fname}'"
            binders.append((completed, typ))
            names[fname] = completed
        else:
            binders.append((name, typ))
            names[name] = name
    binders_src = "".join(f" {{{name} : {typ}}}" for name, typ in binders)
    partial = LOWER_FOR_CAT[cat][1]
    partial_src = qualify_partial_constructors(
        partial_app(partial, rule.state_name, partial_field_values_for_descend(prod, rule.index)))
    complete_src = subst(prod.ast, names)
    relation_constructor = (
        f"_root_.ConservativeExtractor.Generated.{LOWER_FOR_CAT[cat][2]}."
        f"{prod.name}_{rule.state_name}"
    )
    child_rel = f"_root_.ConservativeExtractor.Generated.{child_rel}"
    return [
        "",
        f"theorem {theorem_base}_completes{binders_src}",
        f"    ({fname}_completes : {child_rel} {fname} {fname}') :",
        f"    {LOWER_FOR_CAT[cat][2]} ({partial_src})",
        f"      ({complete_src}) := by",
        f"  exact {relation_constructor} {fname}_completes",
    ]


def render_completion_shape_theorems(
    cat: str,
    done_prods: list[Production],
    boundary_gaps: list[BoundaryGap],
    rules: list[Rule],
    descend_rules: list[Rule],
) -> list[str]:
    lines: list[str] = []
    for prod in done_prods:
        lines.extend(render_done_completion_shape_theorem(prod, cat))
    for gap in boundary_gaps:
        lines.extend(render_boundary_gap_completion_shape_theorem(gap, cat))
    for rule in rules:
        lines.extend(render_completion_shape_theorem(rule, cat))
    for rule in descend_rules:
        lines.extend(render_descend_completion_shape_theorem(rule, cat))
    return lines


def fieldless_done_productions(
    productions: list[Production],
) -> dict[str, list[Production]]:
    out: dict[str, list[Production]] = {cat: [] for cat in CATS}
    for prod in productions:
        if prod.target_cat not in CATS or field_elems(prod):
            continue
        if any(elem.kind != "token" for elem in prod.elems):
            raise ValueError(
                f"{prod.name}: fieldless generated lowering only supports tokens"
            )
        out[prod.target_cat].append(prod)
    return out


def rule_lookup(
    rules: dict[str, list[Rule]],
) -> tuple[dict[tuple[str, int], Rule], dict[str, Rule]]:
    by_field: dict[tuple[str, int], Rule] = {}
    by_start: dict[str, Rule] = {}
    for cat_rules in rules.values():
        for rule in cat_rules:
            if rule.index is None:
                by_start.setdefault(rule.production.name, rule)
            else:
                by_field[(rule.production.name, rule.index)] = rule
    return by_field, by_start


def covered_boundary_dots(prod: Production, cat_rules: list[Rule]) -> set[int]:
    covered: set[int] = set()
    if not field_elems(prod):
        covered.add(len(prod.elems))
    for rule in cat_rules:
        if rule.production.name != prod.name:
            continue
        if rule.index is None:
            covered.add(1)
        else:
            covered.add(rule.index + 1)
    return covered


def first_field_at_or_after(
    prod: Production,
    dot: int,
) -> tuple[int, Elem, str, str] | None:
    for field in field_elems(prod):
        i, _elem, _name, _typ = field
        if i >= dot:
            return field
    return None


def last_field_before(
    prod: Production,
    dot: int,
) -> tuple[int, Elem, str, str] | None:
    out = None
    for field in field_elems(prod):
        i, _elem, _name, _typ = field
        if i < dot:
            out = field
    return out


def cutoff_partial_expr(cat: str) -> str:
    partial = LOWER_FOR_CAT[cat][1]
    return qualify_partial_constructors(f"{partial}.cutoff")


def cutoff_exact_expr(cat: str) -> str:
    rel = LOWER_FOR_CAT[cat][2]
    return f"_root_.ConservativeExtractor.Generated.{rel}.cutoff"


def boundary_gap_for_dot(
    prod: Production,
    cat: str,
    dot: int,
    by_field: dict[tuple[str, int], Rule],
    by_start: dict[str, Rule],
) -> BoundaryGap:
    active = first_field_at_or_after(prod, dot)
    if active is not None:
        active_index, active_elem, _active_name, active_typ = active
        active_rule = by_field.get((prod.name, active_index))
        active_cutoff = partial_cutoff(active_elem)
        active_premise = completion_cutoff_premise(active_elem)
        if (
            active_rule is not None
            and active_cutoff is not None
            and active_premise is not None
        ):
            partial = LOWER_FOR_CAT[cat][1]
            active_partial_type = active_elem.partial_type or active_typ
            fields = fields_before(prod, active_index) + [
                (active_cutoff, active_partial_type)
            ]
            partial_src = qualify_partial_constructors(
                partial_app(partial, active_rule.state_name, fields))
            exact_src = f"{relation_constructor_for_rule(active_rule, cat)} {active_premise}"
            return BoundaryGap(prod, dot, partial_src, exact_src)

    previous = last_field_before(prod, dot)
    if previous is not None:
        previous_index, _previous_elem, _previous_name, _previous_typ = previous
        previous_rule = by_field.get((prod.name, previous_index))
        if previous_rule is not None:
            premise = completion_premise_for_rule(previous_rule)
            relation_constructor = relation_constructor_for_rule(previous_rule, cat)
            exact_src = (
                relation_constructor if premise is None
                else f"{relation_constructor} {premise}"
            )
            return BoundaryGap(
                prod, dot, partial_expr_for_rule(previous_rule), exact_src)

    start_rule = by_start.get(prod.name)
    if start_rule is not None:
        return BoundaryGap(
            prod,
            dot,
            partial_expr_for_rule(start_rule),
            relation_constructor_for_rule(start_rule, cat),
        )

    return BoundaryGap(prod, dot, cutoff_partial_expr(cat), cutoff_exact_expr(cat))


def boundary_gap_lowerings(
    productions: list[Production],
    rules: dict[str, list[Rule]],
) -> dict[str, list[BoundaryGap]]:
    by_field, by_start = rule_lookup(rules)
    out: dict[str, list[BoundaryGap]] = {cat: [] for cat in CATS}
    for prod in productions:
        if prod.target_cat not in CATS:
            continue
        covered = covered_boundary_dots(prod, rules[prod.target_cat])
        for dot in range(len(prod.elems) + 1):
            if dot in covered:
                continue
            out[prod.target_cat].append(
                boundary_gap_for_dot(
                    prod, prod.target_cat, dot, by_field, by_start))
    return out


def render() -> str:
    productions = parse_syntax_rules()
    _states, rules = derive_states(productions)
    done_prods = fieldless_done_productions(productions)
    boundary_gaps = boundary_gap_lowerings(productions, rules)
    descend_rules: dict[str, list[Rule]] = {cat: [] for cat in CATS}
    for cat, cat_rules in rules.items():
        for rule in cat_rules:
            if rule.index is None:
                continue
            elem = rule.production.elems[rule.index]
            if (
                (elem.kind == "cat" and elem.cat in CATS) or
                (elem.kind == "list" and elem.cat in LIST_CATS)
            ):
                descend_rules[cat].append(rule)

    lines: list[str] = [
        "import LwRust.Extractor.FrontierSemantics",
        "",
        "/-!",
        "Generated lowering hooks from checked FW parser frontiers to the",
        "existing generated partial-program frontiers.",
        "",
        "This file is generated from the syntax declarations and checked",
        "`SyntaxSemantics` annotations in `LwRust.Extractor.CompleteProgram`.",
        "Re-generate it with `scripts/generate_frontier_lower_from_syntax.py`.",
        "-/",
        "",
        "namespace ConservativeExtractor",
        "namespace GrammarFrontier",
        "namespace FwRust",
        "namespace GeneratedFrontierLower",
        "",
    ]

    for item_cat in LIST_LOWER_FOR_CAT:
        lines.extend(render_list_lower_inductive(item_cat, tail=False))
        lines.append("")
        lines.extend(render_list_lower_inductive(item_cat, tail=True))
        lines.append("")

    for cat in CATS:
        relation, partial, _complete_rel, _denote = LOWER_FOR_CAT[cat]
        lines.extend(
            [
                f"inductive {relation} :",
                f"    CheckableGrammar.CheckedFrontierState checkableGrammar .{cat} →",
                f"    {partial} → Prop where",
                f"  | fallback",
                f"      {{state : CheckableGrammar.CheckedFrontierState checkableGrammar .{cat}}} :",
                f"      {relation}",
                f"        state",
                f"        (_root_.ConservativeExtractor.Generated.{partial}.cutoff)",
            ]
        )
        first = False
        for prod in done_prods[cat]:
            if not first:
                lines.append("")
            first = False
            lines.extend(render_done_constructor(prod, cat))
        for gap in boundary_gaps[cat]:
            if not first:
                lines.append("")
            first = False
            lines.extend(render_boundary_gap_constructor(gap, cat))
        for rule in rules[cat]:
            if rule.index is None:
                if not rule.production.elems or rule.production.elems[0].kind != "token":
                    continue
                rendered = render_start_constructor(rule, cat)
            else:
                rendered = render_boundary_constructor(rule, cat)
            if not first:
                lines.append("")
            first = False
            lines.extend(rendered)
        for rule in descend_rules[cat]:
            if not first:
                lines.append("")
            first = False
            lines.extend(render_descend_constructor(rule, cat))
        lines.append("")

    for item_cat in LIST_LOWER_FOR_CAT:
        lines.extend(render_list_soundness_theorem(item_cat, tail=False))
        lines.extend(render_list_soundness_theorem(item_cat, tail=True))

    for item_cat in LIST_LOWER_FOR_CAT:
        lines.extend(render_list_state_completion_soundness_theorem(item_cat, tail=False))
        lines.extend(render_list_state_completion_soundness_theorem(item_cat, tail=True))

    for cat in CATS:
        lines.extend(
            render_soundness_theorem(
                cat,
                done_prods[cat],
                boundary_gaps[cat],
                rules[cat],
                descend_rules[cat],
            )
        )

    lines.extend(render_ty_state_completion_soundness_theorem())
    lines.extend(render_lval_state_completion_soundness_theorem())
    lines.extend(render_term_state_completion_soundness_theorem())

    for item_cat in LIST_LOWER_FOR_CAT:
        lines.extend(render_list_coverage_theorem(item_cat, tail=False))
        lines.extend(render_list_coverage_theorem(item_cat, tail=True))

    for cat in CATS:
        lines.extend(render_coverage_theorem(cat))

    lines.extend(render_decoder_assisted_coverage_theorems())

    for cat in CATS:
        lines.extend(
            render_completion_shape_theorems(
                cat,
                done_prods[cat],
                boundary_gaps[cat],
                rules[cat],
                descend_rules[cat],
            )
        )

    lines.extend(
        [
            "",
            "end GeneratedFrontierLower",
            "end FwRust",
            "end GrammarFrontier",
            "end ConservativeExtractor",
            "",
        ]
    )
    return "\n".join(lines)


def main() -> None:
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    OUTPUT.write_text(render())


if __name__ == "__main__":
    main()
