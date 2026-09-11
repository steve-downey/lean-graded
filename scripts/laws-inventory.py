#!/usr/bin/env python3
"""Mechanical law inventory for the Lean model of graded Transpose.

Parses every `theorem <name>` declared in `Graded/*.lean`, and for each one
collects which of a small, fixed vocabulary of pomonoid-property lemma names
its declaration text (docstring + signature + proof, taken together — not
just the tactic block) mentions. Each vocabulary name is mapped to a
PROPERTY tag by reading the `/-- PROPERTY: <tag> -/` comments that precede
lemmas in `Graded/Grade.lean` and `Graded/Morphism.lean`, plus a small,
explicit, hand-checked supplement (see ORDER_SUPPLEMENT below) for the
handful of order-related lemmas in `Graded/Grade.lean` that state real
consequences of the order (`join_le`, `join_mono`, `bot_le`,
`le_join_left`, `le_join_right`) but were not given a literal PROPERTY
docstring there ([grade-pomonoid] tagged only the four defining
inequalities `le_refl'`/`le_trans'` that way).

This is deliberately a *dumb* heuristic: a theorem whose declaration text
mentions none of the vocabulary names, and is not on the small ALLOWLIST of
genuinely pure-structural theorems below, is something a human should look
at — the script names it and exits 1. It does not try to see through a
`simp only [someDef]` unfold to whatever property `someDef`'s own body
cites, and it does not distinguish two theorems that happen to share a bare
name in different namespaces (`Graded.Grade.join_le` vs the generic
`Graded.join_le` in `Graded/Obligations.lean`) — rows are kept apart by
`module`, not merged by name, but a *mention* of the bare name inside some
third theorem's proof is credited to the tag regardless of which of the two
same-named lemmas was actually meant. See `blog/letters/oracle-export.org`
for what this cost in practice.
"""

import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
GRADED_DIR = ROOT / "Graded"

# ---------------------------------------------------------------------------
# The fixed search vocabulary (from the step brief, verbatim) plus the two
# `le_*` names that are actually spelled out in `Graded/Grade.lean`.
VOCAB = [
    "join_assoc",
    "join_comm",
    "join_idem",
    "bot_join",
    "join_bot",
    "le_refl'",
    "le_trans'",
    "le_join_left",
    "le_join_right",
    "join_le",
    "join_mono",
    "bot_le",
    # Added by [grade-join-strength]'s closure: antisymmetry is a
    # separable order property, not a consequence of the other four, and
    # the `Pack` counter-instance is the first grade in the model to
    # refute it. Tagged `antisymmetry` (not `order`) by a literal
    # `/-- PROPERTY: -/` docstring on `Graded.Grade.le_antisymm`, so the
    # by-property table separates the grades that have it from the one
    # that does not.
    "le_antisymm",
    "rename_join",
    "rename_bot",
]

# Untagged consequences of the order in `Graded/Grade.lean` — no literal
# `PROPERTY:` docstring, but plainly order facts (`g ⊆ join g h`, `join g h
# ⊆ k` from two one-sided bounds, `∅ ⊆ g`), documented as "(order)" in the
# prose of every module that cites them (`Widen`, `Monad`, `Compose`,
# `Traverse`). Kept separate from the PROPERTY-tag scan below, and small
# enough to read at a glance and check against the source by hand.
ORDER_SUPPLEMENT = {
    "le_join_left": "order",
    "le_join_right": "order",
    "join_le": "order",
    "join_mono": "order",
    "bot_le": "order",
}

# Theorems the script flagged that a human (this step's worker) then looked
# at and judged safe to allow-list — every one individually, never as a
# blanket "reduction lemma" pass. Two, and only two, reasons are accepted;
# each entry says which. Neither reason is "it's inconvenient to fix" and
# neither hypothesis is ever strengthened to make a proof easier — that is
# a `blocked-`/`amendment-` situation, not an allow-list entry. Full
# reasoning for every entry is in `blog/letters/oracle-export.org`'s
# "What the checker refused" section; this dict's value is the one-line
# version, kept next to the code it excuses so the two cannot drift apart.
#
#   structural — no pomonoid property is at stake even in principle: the
#     statement never puts two grades in a `join` together (an `ok`/`ok`
#     reduction case, a naturality fact at a single fixed grade, a
#     `Finset.sort`/`Finset.image` fact with no `Grade.join`/`Grade.bot` in
#     sight, a fact about which element of a list comes first).
#   delegates — the proof's only work is `rw`/`cases`/`exact` into another
#     *already-tabulated* theorem (named in the reason) that itself cites
#     the property directly; the property is real, and it is on that row,
#     not invented here.
ALLOWLIST = {
    # --- structural -----------------------------------------------------
    # --- Graded/AccumKinds.lean ([accumulated-evidence-shape]) -----------
    # The per-kind carrier's evidence IS a `Grade`, so the laws that put
    # two pieces of evidence together cite the grade's own lemmas and need
    # no entry here; these are the ones that do not join anything.
    "Kinds.kindsOf_ok": "structural: definitional unfold",
    "Kinds.kindsOf_failed": "structural: definitional unfold",
    "Kinds.failed_eq_of_kinds_eq": "structural: proof irrelevance, the Kinds mirror of errs_eq_of_list_eq",
    "Kinds.kindsOf_map": "structural: functor law, no grade in sight",
    "Kinds.kindsOf_widen": "structural: widening moves the membership proof, not the set",
    "Kinds.kindsOf_map2K": "delegates to Kinds.kindsOf_apK (unit) and Kinds.kindsOf_map",
    "Kinds.traverseK_nil": "structural: definitional unfold",
    "Kinds.kindsOf_traverseK": "delegates to Kinds.kindsOf_map2K, folded",
    "Kinds.mem_kindsOf_traverseK": "delegates to Kinds.kindsOf_map2K and Finset.mem_union, folded",
    "Kinds.traverseK_ok": "structural: ok-only path, no evidence to join",
    "Kinds.ofAccum_ok": "structural: definitional unfold",
    "Kinds.ofAccum_errs": "structural: definitional unfold",
    "Kinds.kindsOf_ofAccum": "structural: List.toFinset of the error list, no grade in sight",
    "Kinds.ofAccum_map": "structural: functor naturality at one grade",
    "Kinds.ofAccum_widen": "structural: the projection ignores the membership proof widening changes",
    "Kinds.ofAccum_pureK": "structural: definitional unfold",
    "Kinds.ofAccum_apK": "structural: List.toFinset_append at the both-fail leaf, the list's join not the grade's",
    "Kinds.ofAccum_map2K": "delegates to Kinds.ofAccum_apK and Kinds.ofAccum_map",
    "Kinds.ofAccum_traverseK": "delegates to Kinds.ofAccum_map2K, folded",
    "Kinds.toGraded_mem": "structural: which element of the list comes first, and that it is in the list's set",
    "Kinds.toGraded_of_kindsOf_singleton": "structural: a singleton set names its element",
    "Kinds.noFirstError": "structural: a counterexample about list order against set equality, no grade in sight",
    "map_id": "structural: functor law, no grade in sight",
    "map_comp": "structural: functor law, no grade in sight",
    "cast_rfl": "structural: generic cast transport",
    "cast_cast": "structural: generic cast transport",
    "cast_ok": "structural: generic cast transport, ok case",
    "cast_err": "structural: generic cast transport, err case",
    "cast_errs": "structural: generic cast transport, Accum errs case",
    "cast_widen": "structural: cast commutes with widen, no join",
    "widen_cast": "structural: widen commutes with cast, no join",
    "widen_map": "structural: widen commutes with map, no join",
    "widen_irrel": "structural: proof-irrelevance of the inclusion witness",
    "widen_ok": "structural: widen's own ok-case reduction, no join in sight",
    "widen_err": "structural: widen's own err-case reduction; the inclusion "
        "witness it threads is not a named property, just an argument",
    "bindK_ok": "structural: bindK's own ok-case reduction, documented as "
        "such at its own definition site, same footing as bindF_ok",
    "bindK_err": "structural: bindK's own err-case reduction, same footing "
        "as bindF_err",
    "bindK_irrel": "structural: proof-irrelevance of the two threaded "
        "inclusion witnesses, the sufficient-grade mirror of widen_irrel — "
        "this is the theorem the sufficient-grade-bind step's verdict "
        "turns on",
    "Comp.map_id": "structural: functor law, no grade in sight",
    "Comp.map_comp": "structural: functor law, no grade in sight",
    "ap_ok_ok": "structural: ok/ok case, function applied, no error, no join",
    "apFlipped_ok_ok": "structural: ok/ok case, no join",
    "Comp.ap_ok_ok": "structural: ok/ok case, no join",
    "apF_ok_ok": "structural: ok/ok case; join_idem is needed only to state "
        "apF's type, not to prove this reduction (cast_ok discharges any "
        "witness of g=g alike)",
    "bindF_ok": "structural: reduction lemma, documented as such at its own "
        "definition site; unfolds to widen_refl via proof irrelevance",
    "bindF_err": "structural: reduction lemma, documented as such",
    "apF_err_left": "structural: reduction lemma; delegates to ap_err_left "
        "(order) plus cast_err, same non-need for join_idem as apF_ok_ok",
    "apF_ok_err": "structural: reduction lemma, same reasoning as apF_err_left",
    "rename_ok": "structural: rename threads a function, no grade arithmetic",
    "rename_err": "structural: rename threads a function, no grade arithmetic",
    "rename_map": "structural: naturality at one grade, no join",
    "rename_widen": "structural: naturality at one grade, no join",
    "rename_cast": "structural: naturality at one grade, no join",
    "rename_toGraded": "structural: Accum's rename naturality, no join "
        "(qualifies as Graded.Accum.rename_toGraded)",
    "toGraded_ok": "structural: definitional unfold",
    "toGraded_errs": "structural: definitional unfold",
    "toGraded_grade": "structural: which list element is first, not a "
        "pomonoid fact — the at-most-one-error hypothesis is recorded but "
        "not load-bearing here (see toGraded_grade')",
    "toGraded_grade'": "structural: same list-order fact, unconditionally",
    "sequence_nil": "structural: definitional unfold",
    "sequence_cons": "structural: definitional unfold",
    "joinAll_nil": "structural: definitional unfold",
    "joinAll_cons": "structural: definitional unfold",
    "foldGrade_nil": "structural: definitional unfold",
    "foldGrade_cons": "structural: definitional unfold",
    "foldG_nil": "structural: definitional unfold",
    "foldG_cons": "structural: definitional unfold",
    "joinAllG_nil": "structural: definitional unfold",
    "joinAllG_cons": "structural: definitional unfold",
    "pureF_eq_ok": "structural: definitional unfold",
    "fromEmpty_eq_ok": "structural: definitional unfold",
    "flatten_eq_bind_id": "structural: definitional identity between flatten and bind id",
    "flatten_map": "structural: naturality in the payload, no join",
    "canonEquiv_bot": "structural: definitional unfold at bot",
    "canonEquiv_union": "structural: Canon.union is *defined* by round-tripping "
        "through Finset union; the proof only unfolds that definition and "
        "Grade.join's own, never re-derives a join property",
    "join_eq_right_of_le": "structural: primitive order fact proved directly "
        "from Finset.union_eq_right, same footing as le_refl'/le_trans' — a "
        "defining fact does not cite itself",
    "toFinset_ofFinset": "structural: Finset.sort/Finset.toFinset round-trip, no Grade.join/bot",
    "ofFinset_toFinset": "structural: Finset.sort/Finset.toFinset round-trip, no Grade.join/bot",
    "mem_rename": "structural: Finset.image membership transport, no Grade.join/bot",
    "rename_mono": "structural: Finset.image_subset_image directly, no named Grade lemma",
    "map_emptyEquiv": "structural: naturality at grade bot only — no join is "
        "even expressible at bot",
    "errs_eq_of_list_eq": "structural: list-equality-implies-Accum-equality, not a pomonoid fact",
    "notMonad": "structural: a non-existence argument about function extensionality on an uninhabited domain",
    "nat_not_idem": "structural: 1+1≠1 on Nat, arithmetic, not a Grade fact",
    "sumEquiv_pureF": "structural: Sum correspondence at pure, no join",
    # --- delegates --------------------------------------------------------
    "canon_perm": "delegates to Graded.Tuple.joinAll_perm (commutative, associative); "
        "no independent proof content of its own",
    "traverseComp_eq": "delegates to Comp.traverseComp_cons and traverse_cons "
        "(both idempotent); the composition law's own proof only case-splits "
        "on ok/err and rewrites through those two",
    "flatten_ap": "delegates to Comp.grade_reassoc (associative, commutative) "
        "for the grade equation; the value-level case split cites no "
        "property of its own beyond that cast — the headline finding, see "
        "the letter",
    "traverse_cons_ok_ok": "delegates to traverse_cons (idempotent)",
    "traverse_map": "delegates to traverse_cons (idempotent), twice, by induction",
    "traverse_length": "delegates to the traverse_cons_* reduction lemmas, "
        "themselves delegating to traverse_cons (idempotent)",
    "traverse_nil": "delegates to fromEmpty_eq_ok (structural)",
    "traverse_rename": "the join_idem cast this needs (module docstring: "
        "\"the casts from rename_cast/rename_map2/Grade.join_idem\") is "
        "cancelled by proof irrelevance inside the induction step, not by "
        "an explicit rewrite — so the token never appears, by construction",
    "joinAll_dedup": "delegates to join_mem_eq (associative, commutative, "
        "idempotent) — that theorem's own docstring says dedup is exactly "
        "where join_idem is spent",
    "bindF_pure_left": "delegates to bindF_ok (structural)",
    "bindF_pure_right": "delegates to bindF_ok/bindF_err (structural)",
    "bindF_assoc": "delegates to bindF_ok/bindF_err (structural); at a fixed "
        "grade both sides reduce to the same term before associativity "
        "could matter — see the theorem's own docstring",
    "apF_pure_id": "delegates to apF_ok_ok/apF_ok_err (structural)",
    "apF_pure_pure": "delegates to apF_ok_ok (structural) directly",
    "apF_interchange": "delegates to apF_ok_ok/apF_err_left/apF_ok_err (structural)",
    "apF_comp": "delegates to apF_ok_ok/apF_ok_err/apF_err_left (structural)",
    "traverse_fromEmpty_map": "delegates to traverse_map and traverse_fromEmpty "
        "(both already tabulated); costs nothing beyond citing both, per its own docstring",
    "sumEquiv_bindF": "delegates to bindF_ok/bindF_err (structural)",
    # --- sufficient-grade applicative (this step) ------------------------
    "apK_ok_ok": "structural: ok/ok case, function applied, no error, no "
        "join — the sufficient-grade mirror of ap_ok_ok, same reasoning",
    "apK_err_left": "structural: err-on-the-function-side reduction; bindK's "
        "own err branch ignores the second hypothesis and the continuation "
        "entirely, same footing as bindK_err",
    "apK_ok_err": "structural: err-on-the-argument-side reduction, same "
        "footing as apK_err_left",
    "apFlippedK_ok_ok": "structural: ok/ok case, no join — the sufficient-"
        "grade mirror of apFlipped_ok_ok",
    "apFlippedK_err_right": "structural: err-on-the-argument-side reduction "
        "(apFlippedK binds its argument first), mirrors apFlipped_err_right",
    "apFlippedK_ok_err": "structural: err-on-the-function-side reduction, "
        "mirrors apFlipped_ok_err",
    "apK_flip": "structural, and this is the finding, not an oversight: the "
        "union-graded ap_flip cites Grade.join_comm by construction, "
        "comparing join g h against join h g; at a common sufficient grade "
        "both apK and apFlippedK already land in the same Graded k β, so "
        "there is nothing to compare and no property is consumed — see "
        "the letter for what this implies about where commutativity was "
        "really needed",
    "Comp.apK_ok_ok": "structural: ok/ok case, two-coordinate mirror of "
        "apK_ok_ok, no join",
    "Comp.apK_err_left": "structural: two-coordinate mirror of apK_err_left, "
        "no join",
    "Comp.apK_ok_err": "structural: two-coordinate mirror of apK_ok_err, "
        "no join",
    # --- obligation-layering ----------------------------------------------
    "traverseK_nil": "structural: pureK's own nil-case reduction, no join "
        "in sight — the sufficient-grade mirror of traverse_nil's own "
        "un-costed shape",
    # --- sufficient-grade-traverse (this step) -----------------------------
    "traverseK_irrel": "structural: proof-irrelevance of the single "
        "threaded inclusion witness, the mirror of bindK_irrel/widen_irrel "
        "— traverseK has only one witness to be irrelevant about, since it "
        "reuses Grade.le_refl' k at every position for the accumulated tail",
    "traverseK_nil_eq_fromEmpty": "structural: definitional identity — "
        "traverseK's nil case is pureK, and pureK is fromEmpty by "
        "definition; no fold and no join in sight, unlike traverse_nil's "
        "own widen/fromEmpty proof-irrelevance argument",
    "traverseK_map": "delegates to traverseK_cons (structural, this step), "
        "twice, by induction — no idempotence to cancel, unlike "
        "traverse_map's delegation to traverse_cons (idempotent)",
    "traverseK_fromEmpty": "delegates to traverseK_cons (structural, this "
        "step) — cast-free throughout, unlike traverse_fromEmpty's "
        "delegation to traverse_cons (idempotent)",
    "traverseK_cons_ok_ok": "structural: traverseK_cons's own ok/ok case "
        "reduction, no join — traverseK_cons itself carries no cast for "
        "this to delegate a property from, unlike traverse_cons_ok_ok's "
        "delegation to traverse_cons (idempotent)",
    "traverseK_cons_err_left": "structural: reduction lemma for the "
        "err-on-the-element-side case; traverseK's err branch short-"
        "circuits without computing a join, so there is no idempotence to "
        "restate here, unlike traverse_cons_err_left",
    "traverseK_cons_ok_err": "structural: reduction lemma for the "
        "err-on-the-tail-side case, same reasoning as traverseK_cons_err_left",
    "traverseK_length": "delegates to the traverseK_cons_* reduction "
        "lemmas above, all structural this step — the analogue of "
        "traverse_length, but its delegates carry no idempotence to cite "
        "since traverseK_cons pays none",
    # --- sufficient-grade-morphism ---------------------------------------
    "rename_apK": "the sufficient-grade analogue of rename_ap, needing "
        "only Grade.rename_mono (order-preservation) rather than "
        "Grade.rename_join — rename_mono is not in this script's VOCAB "
        "(only rename_join/rename_bot are), and that gap is the finding "
        "this step exists to record: the naturality law needs monotonicity, "
        "not the join-semilattice-homomorphism vocabulary the union-graded "
        "layer's rename_ap cites",
    "rename_map2K": "delegates to rename_apK and rename_map (structural), "
        "same reasoning: needs Grade.rename_mono, not Grade.rename_join",
    "traverseK_rename": "the sufficient-grade analogue of traverse_rename, "
        "needing only Grade.rename_mono — traverse_rename itself cites no "
        "VOCAB property either (its cast cancels by proof irrelevance, not "
        "a pomonoid law), and traverseK_rename needs strictly less: no "
        "cast to cancel at all, since traverseK never computes a join",
    "constHomK_not_gmap_bot": "refutes a GradedHom field for the "
        "counter-instance: a Finset non-membership fact (e₀ ∉ ∅), not a "
        "pomonoid property citation — the absence of a VOCAB mention here "
        "is exactly what the theorem is about, not an oversight",
    # --- accum-traverse ----------------------------------------------------
    # `apK_ok_ok` is not listed again: it is already allow-listed above for
    # `Graded/Sufficient.lean`, and this dict is keyed by bare name. The
    # reason transfers unchanged — an ok/ok case with no join in sight —
    # but the sharing is the script's known name-collision weakness, not a
    # judgement, and it is recorded here so a reader does not mistake the
    # absence for an oversight.
    "apK_ok_errs": "structural, and this is the finding: Accum.ap_ok_errs "
        "cites order because `ap`'s own definition inlines "
        "Grade.le_join_right into the statement; apK threads the caller's "
        "`hh` instead, so no named property is consumed at all — the same "
        "order-in, nothing-out shape apK_flip already records",
    "apK_errs_ok": "structural: same reasoning as apK_ok_errs, on the "
        "function side, threading `hg`",
    "apK_errs_errs": "structural: the both-fail case; the concatenation is "
        "List.append and the two membership proofs are the caller's `hg` "
        "and `hh`, never Grade.le_join_left/right",
    "errsOf_ok": "structural: definitional unfold",
    "errsOf_errs": "structural: definitional unfold",
    "errsOf_map": "structural: map never touches the error list, no grade "
        "in sight",
    "errsOf_apK": "structural: reads the error list off each constructor "
        "case; the concatenation is List.append, not Grade.join",
    "errsOf_traverseK": "structural, and worth stating as a finding: the "
        "accumulation-order law costs no pomonoid property whatever. It is "
        "a claim about List.append and List.flatMap, delegating to "
        "errsOf_apK/errsOf_map (both structural this step) — the grade is "
        "fixed at the caller's `k` throughout and never computed, so there "
        "is nothing for a join law to be about",
    "traverseK_ok": "structural: the all-success case never constructs an "
        "error, so no membership and no grade arithmetic arises; delegates "
        "to traverseK_cons (structural)",
    "toGraded_pureK": "delegates to fromEmpty_eq_ok (structural)",
    "toGraded_map": "structural: naturality in the payload at one grade, "
        "the Accum mirror of Graded.rename_map's reasoning, no join",
    "toGraded_apK": "structural: which element of the accumulated list "
        "comes first, not a pomonoid fact — exactly toGraded_grade''s own "
        "allow-list reason, at the sufficient grade where apK threads the "
        "caller's inclusions rather than computing a union",
    "toGraded_map2K": "delegates to toGraded_apK and toGraded_map (both "
        "structural this step)",
    "toGraded_traverseK": "structural: the list-order fact lifted through "
        "the induction, delegating to toGraded_map2K and toGraded_pureK; "
        "no grade is computed anywhere, so no property is spent",
    # --- module-split ------------------------------------------------------
    "sequenceK_nil": "structural: definitional unfold, the heterogeneous "
        "mirror of traverseK_nil which is on this list for the same reason",
    "sequenceK_irrel": "structural: proof-irrelevance of the threaded "
        "inclusion witnesses, the mirror of bindK_irrel/traverseK_irrel — "
        "and stronger than either, since what is irrelevant here is a "
        "whole family of witnesses (one per tuple slot) rather than one "
        "or two",
    # --- payload-carrier ---------------------------------------------------
    "toSum_inj": "structural: `ExpectedG` carries a success payload or a "
        "kind-tagged error payload and a proof-irrelevant membership "
        "witness; this says the first two determine the value. It is a "
        "fact about the carrier's own shape, with no grade arithmetic — "
        "the same footing as errs_eq_of_list_eq, which is on this list "
        "for the Accum analogue of exactly this reasoning",
    # --- abstract-effects --------------------------------------------------
    "widen_errs": "structural: Accum.widen's own errs-case reduction, rfl; "
        "the membership proof it threads is the caller's inclusion, not a "
        "named Grade lemma — same footing as widen_ok, which is tagged "
        "only because widen_widen's neighbour mentions le_trans'",
    "toGraded_widen": "structural: which element of the error list comes "
        "first, transported along an inclusion — the same list-order fact "
        "toGraded_ok/toGraded_grade' are allow-listed for, with no join",
    "map_pureK": "structural at this layer: proved from the LawfulGraded"
        "FunctorK fields widen_map and map_pure, which are class "
        "projections over an abstract G, not Graded.Grade lemmas. There is "
        "no pomonoid property to cite because the abstract carrier has no "
        "Grade to have one",
    "traverseGK_nil": "structural: definitional unfold, the generic mirror "
        "of traverseK_nil",
    "traverseGK_map": "structural: induction over traverseGK_cons, itself "
        "rfl; the generic mirror of traverseK_map, which is allow-listed "
        "for the same reason",
    "traverseGK_eq_traverseK": "structural: a bridge between two spellings "
        "of one recursion (traverseGK's apK-after-map cons case against "
        "traverseK's map2K), closed by induction and rfl — no grade is "
        "computed on either side",
    "traverseGK_eq_accum_traverseK": "structural: the same bridge at the "
        "accumulating carrier, same reasoning",
    "app_pureK": "structural: app_pure carried up by app_widen, both "
        "transformation fields; no grade arithmetic — the same two-step "
        "map_pureK uses",
    "app_traverseGK": "structural, and this is the finding rather than an "
        "oversight: traversal naturality over an abstract graded "
        "applicative consumes no pomonoid property whatever. The grade is "
        "the caller's nominated k throughout, the transformation's fields "
        "carry every step, and there is nothing for a join law to be "
        "about. Its concrete instance (toGraded_traverseK) is allow-listed "
        "for the matching reason one layer down",
    "toGraded_traverseK_generic": "delegates to app_traverseGK and the two "
        "traverseGK_eq_* bridges, all structural this step",
    # --- morphism-bridge ---------------------------------------------------
    "renameHomK_hom": "structural: `rfl`. GradedHom.toGradedHomK reuses "
        "H.hom unchanged, so factoring renameHomK through the lift changed "
        "no term — which is the whole content of the theorem",
    "renameHomK_gmap": "structural: `rfl`, same reasoning as "
        "renameHomK_hom for the grade map",
    # --- sufficient-grade-nested (this step) -------------------------------
    "flattenK_ok": "structural: flattenK's own ok-case reduction, "
        "delegates to bindK_ok (documented as such at flattenK's own "
        "definition site), same footing as bindK_ok itself",
    "flattenK_err": "structural: flattenK's own err-case reduction, "
        "delegates to bindK_err, same footing as bindK_err itself",
    "flattenK_map": "structural: naturality in the payload, no join — "
        "the sufficient-grade mirror of flatten_map, which is itself "
        "on this list for the same reason",
    "flattenK_comm": "structural, and this is the finding, not an "
        "oversight: flatten_comm needs Grade.join_comm to reconcile "
        "flatten's grade join g h against the swapped flatten (swap x)'s "
        "join h g; at a common sufficient grade both flattenK hg hh x and "
        "flattenK hh hg (swap x) already land in the same Graded k α, so "
        "there is no second spelling of the grade left to relate — the "
        "proof is a plain case split, no property, no cast, rfl in every "
        "branch",
    "traverseCompK_nil": "structural: Comp.pureK's own nil-case reduction "
        "(nested pureK, no join) — the two-coordinate mirror of "
        "traverseK_nil",
    "traverseCompK_irrel": "structural: proof-irrelevance of the two "
        "threaded inclusion witnesses (one per component), the "
        "two-coordinate mirror of traverseK_irrel",
    "traverseCompK_eq": "delegates to apK_ok_ok/apK_err_left/apK_ok_err "
        "(all structural, this list) via traverseCompK_cons/traverseK_cons "
        "— traverseComp_eq's own union-graded proof needed only "
        "Grade.join_idem (via traverse_cons, itself delegated), and "
        "traverseCompK_cons carries no cast to delegate a property from in "
        "the first place, so there is strictly less here, not the same "
        "amount moved",
}

PROPERTY_TAG_RE = re.compile(
    r"/--\s*PROPERTY:\s*([a-zA-Z]+)\s*-/\s*\n\s*theorem\s+([A-Za-z_][A-Za-z0-9_'.]*)"
)

THEOREM_RE = re.compile(
    r"^theorem\s+([A-Za-z_][A-Za-z0-9_'.]*)", re.MULTILINE
)

# Any line starting one of these keywords at column 0, or a free-floating
# `/-!` module-doc block, or this codebase's own `-- ----...` section
# separator, ends a declaration's text and starts the next one — used to
# carve each theorem's own signature+proof out of the whole file without
# tracking brace/tactic nesting. `/-!` and the dash separator matter
# because both are used here purely as *floating* section prose, never as
# a specific declaration's docstring (that is always `/--`, immediately
# adjacent) — without treating them as boundaries too, a floating comment
# sitting between two theorems is swallowed into the *preceding* theorem's
# scanned text and can credit it with a mention that is actually about
# something else entirely (this bit `Ungraded.apF_comp`, which otherwise
# absorbed a trailing comment's mention of `Grade.join_comm` describing a
# different theorem, `ap_flip`).
# `/--` is included too: it always opens the *next* declaration's own
# docstring (never the previous one's trailing remark), so without it here
# a theorem's chunk runs on into the following theorem's docstring and can
# credit the wrong theorem with a mention that is actually about its
# neighbour (this bit `bindF_pure_right`/`bindF_assoc`/`apF_interchange` in
# `Graded/Ungraded.lean`, each absorbing the *next* theorem's docstring).
BOUNDARY_RE = re.compile(
    r"^(theorem|def|instance|abbrev|structure|class|namespace|end|section|"
    r"variable|open|inductive)\b|^/-!|^/--|^-- -{3,}",
    re.MULTILINE,
)


# ---------------------------------------------------------------------------
# The layer a row belongs to. [module-split]'s gate asks the inventory to
# distinguish generic obligations from concrete ones, representation
# results from both, and the C++-probe obligations from all three.
#
# `generic`        — stated over an abstract grade or an abstract carrier,
#                    mentioning no `Finset` and no `Graded`. These are the
#                    obligations a *different* grade would have to meet.
# `representation` — about two spellings of one grade (`Canon` against
#                    `Finset`). Neither an operational law nor a C++ claim;
#                    `#representation`'s boundary note says why.
# `concrete`       — about `Grade Err` and its carriers. The bulk.
#
# The fourth distinction is orthogonal and already carried by the `cpp`
# column: a row with a C++ equation is a probe obligation, and the C++
# side owes a `static_assert` or a test for it. A row can be both
# `concrete` and a probe; no row is both `generic` and a probe, which is
# itself worth being able to see.
LAYER_OF = {
    "Graded/Obligations.lean": "generic",
    "Graded/EffectK.lean": "generic",
    "Graded/Canonical.lean": "representation",
}


def layer_for(module: str) -> str:
    return LAYER_OF.get(module, "concrete")


def build_property_map():
    """Read Graded/Grade.lean and Graded/Morphism.lean for literal
    `/-- PROPERTY: X -/` tags, then add the small order supplement."""
    tags = {}
    for fname in ("Grade.lean", "Morphism.lean"):
        text = (GRADED_DIR / fname).read_text()
        for m in PROPERTY_TAG_RE.finditer(text):
            prop, name = m.group(1), m.group(2)
            tags[name] = prop
    for name, prop in ORDER_SUPPLEMENT.items():
        tags.setdefault(name, prop)
    missing = [v for v in VOCAB if v not in tags]
    if missing:
        sys.exit(
            "laws-inventory: internal error — vocabulary name(s) with no "
            f"property mapping: {missing}"
        )
    return tags


def theorem_chunks(path: Path):
    """Yield (name, chunk_text) for every top-level `theorem` in `path`,
    where chunk_text runs from the `theorem` line itself up to (not
    including) the next declaration boundary — the theorem's own
    signature and full proof, deliberately *not* any preceding docstring
    (RULES.md's discipline is about what the *proof* cites, and every
    finding this script needed was already visible in the statement or
    the tactic block; see the letter for the one file-level chunking bug
    this asymmetry sidesteps)."""
    text = path.read_text()
    boundaries = [m.start() for m in BOUNDARY_RE.finditer(text)] + [len(text)]
    theorem_starts = {m.start(): m.group(1) for m in THEOREM_RE.finditer(text)}
    for i, start in enumerate(boundaries[:-1]):
        if start not in theorem_starts:
            continue
        name = theorem_starts[start]
        chunk_end = boundaries[i + 1]
        yield name, text[start:chunk_end]


# Lean identifiers here can end in `'` (`le_refl'`, `le_trans'`), which is
# not a `\w` character, so a plain `\b...\b` regex boundary never fires
# after it (both the apostrophe and whatever follows — space, `)`, `.` —
# are "non-word", and `\b` needs one side word and one side not). Treat `'`
# as part of the identifier-character class for boundary purposes instead.
_ID_CHARS = r"A-Za-z0-9_'"


def _mention_re(name: str) -> re.Pattern:
    return re.compile(
        rf"(?<![{_ID_CHARS}]){re.escape(name)}(?![{_ID_CHARS}])"
    )


def mentioned_properties(chunk: str, property_of: dict):
    found = set()
    props = set()
    for name in VOCAB:
        if _mention_re(name).search(chunk):
            found.add(name)
            props.add(property_of[name])
    return found, props


# ---------------------------------------------------------------------------
# The C++ law column: a small, hand-maintained map from theorem name to the
# `beman::transpose`-flavoured equation it corresponds to. Unmatched
# theorems get "—". Keyed by the name exactly as captured (so a
# `Comp.`/`Accum.`-qualified name is a distinct key from its bare
# counterpart in another module).
CPP_LAW = {
    # --- monad ---
    "bind_pure_left": "and_then(pure(x), f) == f(x)",
    "bind_pure_right": "and_then(x, pure) == x",
    "bind_assoc": "and_then(and_then(x, f), k) == and_then(x, [=](auto a){ return and_then(f(a), k); })",
    "bind_map": "and_then(x, [=](auto a){ return pure(f(a)); }) == transform(x, f)",
    "bind_widen": "and_then(widen<Es2>(x), f) == widen<Es2 | Fs>(and_then(x, f))",
    # --- applicative (from monad) ---
    "ap_pure_id": "apply(pure(id), x) == x",
    "ap_pure_pure": "apply(pure(f), pure(a)) == pure(f(a))",
    "ap_interchange": "apply(u, pure(a)) == apply(pure([=](auto f){ return f(a); }), u)",
    "ap_comp": "apply(apply(apply(pure(compose), u), v), w) == apply(u, apply(v, w))",
    "ap_flip": "apply(f, x) == apply_flipped(f, x)  // only when at most one side errs",
    # `Graded.Accum`'s `ap_pure_id`/`ap_pure_pure`/`ap_interchange`/`ap_comp`
    # are declared inside `namespace Accum`, so — unlike `Comp.ap_pure_id`
    # below, which dot-qualifies its name explicitly — they are captured
    # under the *same bare name* as `Graded.Applicative`'s own four laws,
    # and this table cannot key them apart (rows stay apart by `module`;
    # the C++ column does not). They share the entries above; the equation
    # shape is the same either way, only the accumulation behaviour on
    # failure differs, which the boolean `==` doesn't distinguish.
    # --- traverse (List) ---
    "traverse_nil": "traverse(f, {}) == pure({})",
    "traverse_cons": "traverse(f, x :: xs) == map2(cons, f(x), traverse(f, xs))",
    "traverse_map": "traverse(f, transform(xs, h)) == traverse(f compose h, xs)",
    "traverse_fromEmpty":
        "static_assert(!traverse_accepts<fromEmpty, xs>)  "
        "// no C++ left side: at the empty grade the carrier is bare T, which is "
        "not a context, and expected<T, error_set<>> fails applicative_object's "
        "subsumption clause at its own grade; a no-fail traversal is spelled "
        "std::ranges::transform",
    "traverse_length": "traverse(f, xs).value().size() == xs.size()  // shape preservation",
    "traverse_rename": "transform_error(traverse(f, xs), phi) == traverse(transform_error(f, phi), xs)",
    "traverse_fromEmpty_map":
        "static_assert(!traverse_accepts<fromEmpty compose f, xs>)  "
        "// the same refusal as traverse_fromEmpty; the right side, "
        "transform(xs, f), is the only spelling the C++ has",
    # --- traverse (Tuple) ---
    "joinAll_perm": "error_set<Es...> == error_set<permutation of Es...>",
    "joinAll_dedup": "error_set<Es..., duplicates removed> == error_set<Es...>",
    "sequence_cons": "transpose(x, xs...) == map2(tuple_cons, x, transpose(xs...))",
    # --- compose (flatten) ---
    "flatten_map": "transform(flatten(x), f) == flatten(transform(transform(x, f)))",
    "flatten_pure_outer": "flatten(pure(y)) == y",
    "flatten_pure_inner": "flatten(transform(x, pure)) == x",
    "flatten_flatten": "flatten(flatten(x)) == flatten(transform(x, flatten))",
    "flatten_widen_outer": "flatten(widen<Es2>(x)) == widen<Es2 | Fs>(flatten(x))",
    "flatten_widen_inner": "flatten(transform(x, widen<Fs2>)) == widen<Es | Fs2>(flatten(x))",
    "flatten_comm": "flatten(x) == flatten(swap(x))  // up to reordering the union's arguments",
    # --- compose-applicative (Comp) ---
    "Comp.ap_pure_id": "apply(pure(id), x) == x  // nested, componentwise",
    "Comp.ap_pure_pure": "apply(pure(f), pure(a)) == pure(f(a))  // nested, componentwise",
    "Comp.ap_interchange": "apply(u, pure(a)) == apply(pure([=](auto f){ return f(a); }), u)  // nested",
    "Comp.ap_comp": "apply(apply(apply(pure(compose), u), v), w) == apply(u, apply(v, w))  // nested",
    "traverseComp_eq":
        "traverse_comp(a -> transform(f(a), k), xs) == "
        "transform(traverse(f, xs), ys -> traverse(k, ys))  "
        "// traverse_comp is a hand fold over the library's two applicative "
        "objects: a composed applicative cannot be a traverse policy, because "
        "applicative_value_t reads the carrier's value_type, and for a nested "
        "expected that is the inner carrier",
    "flatten_ap": "flatten(apply(ff, xx)) == apply(flatten(ff), flatten(xx))  // one-sided condition only",
    # --- morphisms ---
    "rename_map": "transform_error(transform(x, f), phi) == transform(transform_error(x, phi), f)",
    "rename_widen": "transform_error(widen<Es2>(x), phi) == widen<image of Es2>(transform_error(x, phi))",
    "rename_cast": "transform_error(x, phi) commutes with a same-set grade cast",
    "rename_pure": "transform_error(pure(a), phi) == pure(a)",
    "rename_bind": "transform_error(and_then(x, f), phi) == and_then(transform_error(x, phi), transform_error(_, phi) compose f)",
    "rename_ap": "transform_error(apply(f, x), phi) == apply(transform_error(f, phi), transform_error(x, phi))",
    "rename_map2": "transform_error(map2(k, x, y), phi) == map2(k, transform_error(x, phi), transform_error(y, phi))",
    "Accum.rename_toGraded": "first_error(transform_error(x, phi)) == transform_error(first_error(x), phi)",
    # --- ungraded-baseline (Fixed g) ---
    "bindF_pure_left": "and_then(pure(x), f) == f(x)  // fixed grade, cast-free",
    "bindF_pure_right": "and_then(x, pure) == x  // fixed grade, cast-free",
    "bindF_assoc": "and_then(and_then(x, f), k) == and_then(x, [=](auto a){ return and_then(f(a), k); })  // fixed grade",
    "apF_pure_id": "apply(pure(id), x) == x  // fixed grade, cast-free",
    "apF_pure_pure": "apply(pure(f), pure(a)) == pure(f(a))  // fixed grade, cast-free",
    "apF_interchange": "apply(u, pure(a)) == apply(pure([=](auto f){ return f(a); }), u)  // fixed grade",
    "apF_comp": "apply(apply(apply(pure(compose), u), v), w) == apply(u, apply(v, w))  // fixed grade",
    "sumEquiv_bindF": "and_then(x, f) corresponds to std::expected/variant-style Sum::bind under the Equiv",
    # --- accum-traverse / morphism-bridge --------------------------------
    # Added by [cpp-sync]. Tranches C-G proved laws with C++ consequences
    # and none of them reached this table, so `docs/probe-harness.md` was
    # still describing the model as it stood before them. These six are
    # the ones a C++ implementation can actually be checked against.
    #
    # `apK_comp` is deliberately absent: the name is declared in both
    # `Graded/AccumTraverse.lean` and `Graded/Sufficient/ApplicativeK.lean`
    # with genuinely different C++ meanings (accumulate both sides' errors
    # versus keep the first), and this table is keyed by bare name, so one
    # entry would put the wrong equation on one of the two rows.
    # `toGraded_traverseK`, `toGraded_apK`, `errsOf_traverseK` and
    # `toGraded_widen` carry NO entry, deliberately. Each is a statement
    # about the source-ordered list and its head, and [probe-corpus] found
    # the C++ accumulating evidence has neither (`Kinds.noFirstError`
    # proves no projection from it recovers the head). What a C++
    # implementation CAN be checked against is the per-kind consequence,
    # and that is stated by the `Kinds.*` theorems below, which carry the
    # entries instead. The list-form theorems remain the model's own
    # facts; they are not obligations on an implementation that does not
    # keep the list.
    "traverseK_ok":
        "traverse(f, xs) == pure(transform(xs, f))  "
        "// when every check succeeds, the accumulating form is just transform",
    # --- accumulation, per kind (Graded/AccumKinds.lean) ---
    "Kinds.mem_kindsOf_traverseK":
        "traverse(f, xs, accumulating).error().holds<E>() == (some f(x), x in xs, "
        "failed with kind E); a succeeding position contributes nothing, a kind "
        "raised twice is present once  "
        "// the per-kind form of errsOf_traverseK -- what the C++ evidence "
        "retains; that the witness kept for E is the LEFTMOST of that kind is "
        "the payload detail this tag-only carrier cannot state",
    "Kinds.kindsOf_widen":
        "widen<Es2>(x /*accumulated*/).error().holds<E>() == x.error().holds<E>() "
        "for every kind E, witness_count preserved  "
        "// widening moves the membership proof and not the evidence; in C++ "
        "both objects share one carrier, so the conversion is the same conversion",
    "Kinds.kindsOf_apK":
        "apply(f, x, accumulating).error() holds exactly the kinds f and x raised  "
        "// the evidence of an application is the join of the evidence; unit "
        "laws where one side succeeded",
    "Kinds.toGraded_mem":
        "apply(f, x).error() is of kind E  =>  apply(f, x, accumulating).error()"
        ".holds<E>() with the same witness; likewise traverse(f, xs) against "
        "traverse(f, xs, accumulating)  "
        "// what remains of toGraded_apK / toGraded_traverseK once order is "
        "forgotten; the C++ cannot compute first_error (Kinds.noFirstError)",
    "Kinds.toGraded_of_kindsOf_singleton":
        "witness_count() == 1  =>  the accumulating result == the "
        "short-circuiting result outright  "
        "// with one kind present there is nothing left to disagree about",
    "GradedHom.hom_ok":
        "transform_error(ok(a), phi) == ok(a)  "
        "// at EVERY error set, not only the empty one where the pure law states it",
}


def cpp_law_for(name: str) -> str:
    return CPP_LAW.get(name, "—")


def compute_rows():
    property_of = build_property_map()

    rows = []
    flagged = []
    # `rglob`, not `glob`. [module-split] moved 61 theorems into
    # `Graded/Sufficient/*.lean`, and a non-recursive glob dropped every
    # one of them from this table while still reporting "0 flagged" — a
    # silent loss of a third of the inventory, from a check whose whole
    # job is to notice things. Walk the tree.
    for path in sorted(GRADED_DIR.rglob("*.lean")):
        module = f"Graded/{path.relative_to(GRADED_DIR)}"
        for name, chunk in theorem_chunks(path):
            _found, props = mentioned_properties(chunk, property_of)
            row = {
                "theorem": name,
                "module": module,
                "layer": layer_for(module),
                "properties": sorted(props),
                "cpp": cpp_law_for(name),
            }
            rows.append(row)
            if not props and name not in ALLOWLIST:
                flagged.append((module, name))
    return rows, flagged


def report_flagged(flagged):
    sys.stderr.write(
        "laws-inventory: the following theorems cite no tagged pomonoid "
        "property and are not on the allow-list — a human should look "
        "at each:\n"
    )
    for module, name in flagged:
        sys.stderr.write(f"  {module}: {name}\n")
    sys.stderr.write(f"({len(flagged)} theorem(s) flagged)\n")


def print_by_property(rows):
    """`--by-property`: the mechanical property-to-law map, read straight
    off `rows` (the same data `docs/laws.json` is generated from) rather
    than off any hand-written prose. One section per property (plus a
    final "—" section for theorems tagged with no property at all),
    theorems listed `module: theorem` in file order. This is a reporting
    mode over the existing dumb heuristic, not a second parser — it groups
    the same `properties` field `write_outputs` already writes to
    `docs/laws.json`."""
    by_prop: dict[str, list[str]] = {}
    for row in rows:
        props = row["properties"] or ["—"]
        for prop in props:
            by_prop.setdefault(prop, []).append(f'{row["module"]}: {row["theorem"]}')
    for prop in sorted(by_prop):
        entries = by_prop[prop]
        print(f"{prop} ({len(entries)}):")
        for entry in entries:
            print(f"  {entry}")


def main():
    by_property = "--by-property" in sys.argv[1:]

    rows, flagged = compute_rows()

    if flagged:
        report_flagged(flagged)
        sys.exit(1)

    if by_property:
        print_by_property(rows)
        return

    write_outputs(rows)
    print(f"laws-inventory: {len(rows)} theorems tabulated, 0 flagged.")


def write_outputs(rows):
    docs_dir = ROOT / "docs"
    docs_dir.mkdir(exist_ok=True)

    json_path = docs_dir / "laws.json"
    json_path.write_text(json.dumps(rows, indent=2) + "\n")

    md_lines = [
        "# Laws inventory",
        "",
        "Generated by `scripts/laws-inventory.py` from `Graded/*.lean`. Do "
        "not hand-edit — see `docs/design.md#laws-inventory`.",
        "",
        "| theorem | module | layer | properties | C++ law |",
        "|---|---|---|---|---|",
    ]
    for row in rows:
        props = ", ".join(row["properties"]) if row["properties"] else "—"
        theorem = row["theorem"].replace("|", "\\|")
        cpp = row["cpp"].replace("|", "\\|")
        md_lines.append(
            f"| `{theorem}` | `{row['module']}` | {row['layer']} | {props} | {cpp} |")
    md_lines.append("")
    # The layer census, so the split is visible without reading 255 rows.
    by_layer: dict[str, int] = {}
    for row in rows:
        by_layer[row["layer"]] = by_layer.get(row["layer"], 0) + 1
    probes = sum(1 for row in rows if row["cpp"] != "—")
    md_lines.append("## Obligations by layer")
    md_lines.append("")
    md_lines.append("| layer | theorems |")
    md_lines.append("|---|---|")
    for layer in sorted(by_layer):
        md_lines.append(f"| {layer} | {by_layer[layer]} |")
    md_lines.append(f"| **C++ probe** (orthogonal; see the `C++ law` column) | {probes} |")
    md_lines.append("")
    (docs_dir / "laws.md").write_text("\n".join(md_lines))

    write_probe_harness(docs_dir, rows)


def write_probe_harness(docs_dir: Path, rows):
    """The input to the C++ side: one probe per row that has a C++ law,
    against `beman::transpose` names as given in
    `docs/design.md#cpp-counterpart` (`expected<T, error_set<Es...>>`,
    `and_then`, `transform_error`, `transpose`; `apply`/`transform` for the
    applicative/functor operations `docs/design.md#cpp-counterpart` and
    `#applicative` describe but do not themselves name). Nothing here runs
    C++ — this is the equation list that the probe corpus in the vendored
    transpose tree (`cpp/transpose/tests/beman/transpose/probe_harness.test.cpp`)
    checks by example, one `TEST_CASE` per row, named after the theorem."""
    lines = [
        "# Probe harness",
        "",
        "Generated by `scripts/laws-inventory.py` from `docs/laws.json`. Do "
        "not hand-edit — see `docs/design.md#laws-inventory`.",
        "",
        "One probe per tabulated law that has a C++ equation "
        "(`docs/laws.md`'s non-`—` rows). Each is checked by example with "
        "`std` types (`std::expected`-shaped probes, per "
        "`docs/design.md#cpp-counterpart`'s decision that the CRTP "
        "machinery itself does no law-checking); equality is `==` on the "
        "carrier after conversion. Nothing here runs C++: the corpus that "
        "does is `cpp/transpose/tests/beman/transpose/probe_harness.test.cpp`, "
        "one `TEST_CASE` per row below, named `probe-harness: "
        "<Module>.<theorem>` (`make cpp-probes`).",
        "",
    ]
    for row in rows:
        if row["cpp"] == "—":
            continue
        lines.append(f"## `{row['theorem']}` ({row['module']})")
        lines.append("")
        lines.append(f"    {row['cpp']}")
        lines.append("")
        lines.append(
            "check by example with std types; equality is `==` on the "
            "carrier after conversion."
        )
        lines.append("")
    (docs_dir / "probe-harness.md").write_text("\n".join(lines))


if __name__ == "__main__":
    main()
