import json
import unittest
from pathlib import Path
from verify import ACCEPTED_BASELINE, M4_ACCEPTED_REVISION, M4A_ACCEPTED_REVISION, M3_ACCEPTED_REVISION, parse_axioms, check_promises, check_result_ids, check_inherited, check_m3_layout, check_m3_inherited, check_m4_layout, check_m4_inherited, check_m5_layout


def record(name, axioms=None):
    return {"name": name, "kind": "theorem", "root": True, "unsafe": False,
            "axioms": axioms or []}


def log(*rows):
    return "\n".join("CFDLEAN_DECL " + json.dumps(row) for row in rows)


class AuditChecks(unittest.TestCase):
    def test_qualified_namespace_collision_and_axiom_free(self):
        rows = parse_axioms(log(record("A.same"), record("B.same", ["propext"])))
        self.assertEqual(set(rows), {"A.same", "B.same"})
        self.assertEqual(rows["A.same"]["axioms"], [])

    def test_multiline_type_is_preserved(self):
        row = record("A.multiline", ["propext", "Quot.sound"])
        row["type"] = "first line\nsecond line"
        self.assertEqual(parse_axioms(log(row))["A.multiline"]["type"], row["type"])

    def test_duplicate_even_if_identical(self):
        for axioms in [[], ["Quot.sound"]]:
            with self.assertRaises(ValueError):
                parse_axioms(log(record("A.same"), record("A.same", axioms)))

    def test_forbidden_and_unsafe(self):
        with self.assertRaises(ValueError):
            parse_axioms(log(record("A.bad", ["sorryAx"])))
        row = record("A.bad")
        row["unsafe"] = True
        with self.assertRaises(ValueError):
            parse_axioms(log(row))

    def test_missing_promise(self):
        contract = {"results": [{"stage": "M2a", "declarations": ["A.required"]}]}
        with self.assertRaises(ValueError):
            check_promises({"A.other": record("A.other")}, contract, "M2a")
        self.assertEqual(check_promises({"A.required": record("A.required")}, contract, "M2a"),
                         ["A.required"])

    def test_prior_stage_and_empty_active_binding(self):
        contract = {"results": [{"stage": "M2a", "declarations": ["A.first"]},
                                {"stage": "M2b", "declarations": ["A.second"]}]}
        with self.assertRaises(ValueError):
            check_promises({"A.second": record("A.second")}, contract, "M2b")
        contract["results"][1]["declarations"] = []
        with self.assertRaises(ValueError):
            check_promises({"A.first": record("A.first")}, contract, "M2b")

    def test_frozen_result_id_coverage(self):
        text = "| M2-J | claim |\n| M2-A | claim |"
        rows = [{"id": "M2-J"}, {"id": "M2-A"}]
        check_result_ids({"results": rows}, text)
        for invalid in [rows[:1], rows + rows[:1]]:
            with self.assertRaises(ValueError):
                check_result_ids({"results": invalid}, text)

    def test_inherited_binding_and_type_are_frozen(self):
        results = [{"id": rid, "stage": stage, "declarations": [rid + ".accepted"]}
                   for rid, stage in [("M2-J", "M2a"), ("M2-A", "M2b"),
                                      ("M2-R", "M2b"), ("M2-L", "M2b"), ("M2-E", "M2c"),
                                      ("M2-D", "M2c"), ("M2-O", "M2c"), ("M2-F1", "M2d"),
                                      ("M2-F2", "M2d"), ("M2-F3", "M2d"), ("M2-F4", "M2d"), ("M2-C", "M2d")]]
        contract = {"current_stage": "M2d", "results": results}
        evidence = {"declarations": {r["declarations"][0]: {"type": "approved " + r["id"]}
                                     for r in results}}
        rows = evidence["declarations"]
        self.assertEqual(len(check_inherited(rows, contract, contract, evidence)), 12)
        for index, result in enumerate(results):
            for field, replacement in [("declarations", ["Other.safeTheorem"]), ("stage", "M3a")]:
                changed = json.loads(json.dumps(contract))
                changed["results"][index][field] = replacement
                with self.assertRaises(ValueError):
                    check_inherited(rows, changed, contract, evidence)
            weakened = dict(rows)
            weakened[result["declarations"][0]] = {"type": "a weaker proposition"}
            with self.assertRaises(ValueError):
                check_inherited(weakened, contract, contract, evidence)

    def test_m3_part_layout_is_frozen(self):
        contract = {"results": [{"id": "M3-C", "parts": [{"stage": "M3a", "declarations": []},
                                                               {"stage": "M3b", "declarations": []}]}]}
        check_m3_layout(contract, contract)
        redirected = json.loads(json.dumps(contract))
        redirected["representation_contract"] = "a different specification"
        with self.assertRaises(ValueError):
            check_m3_layout(redirected, contract)
        changed = json.loads(json.dumps(contract))
        changed["results"][0]["parts"].pop()
        with self.assertRaises(ValueError):
            check_m3_layout(changed, contract)
        changed["results"][0]["parts"][0]["stage"] = "M3b"
        with self.assertRaises(ValueError):
            check_m3_layout(changed, contract)

    def test_m3_conditional_and_concrete_are_separate(self):
        contract = {"results": [{"stage": "M3a", "declarations": ["A.conditional"]},
                                {"stage": "M3b", "declarations": []}]}
        rows = {"A.conditional": record("A.conditional")}
        self.assertEqual(check_promises(rows, contract, "M3a", ("M3a", "M3b")), ["A.conditional"])
        with self.assertRaises(ValueError):
            check_promises(rows, contract, "M3b", ("M3a", "M3b"))
        check_result_ids({"results": [{"id": "M3-C"}]}, "| M3-C | conditional and concrete |", "M3")

    def test_m3a_inheritance_freezes_active_parts_and_types(self):
        accepted = {"current_stage": "M3a", "results": [
            {"id": rid, "parts": [{"stage": "M3a", "declarations": [rid + ".old"]}]} for rid in
            ["M3-I", "M3-R", "M3-O", "M3-C"]]}
        accepted["results"][-1]["parts"].append({"stage": "M3b", "declarations": []})
        rows = {rid + ".old": {"type": "approved " + rid} for rid in ["M3-I", "M3-R", "M3-O", "M3-C"]}
        evidence = {"declarations": rows}
        self.assertEqual(len(check_m3_inherited(rows, accepted, accepted, evidence)), 4)
        for i, rid in enumerate(["M3-I", "M3-R", "M3-O", "M3-C"]):
            for key, value in [("declarations", ["Other.safe"]), ("stage", "M3b")]:
                changed = json.loads(json.dumps(accepted))
                changed["results"][i]["parts"][0][key] = value
                with self.assertRaises(ValueError):
                    check_m3_inherited(rows, changed, accepted, evidence)
            weakened = dict(rows)
            weakened[rid + ".old"] = {"type": "weakened"}
            with self.assertRaises(ValueError):
                check_m3_inherited(weakened, accepted, accepted, evidence)
        future = json.loads(json.dumps(accepted))
        future["results"][-1]["parts"][-1]["declarations"] = ["New.concrete"]
        check_m3_inherited(rows, future, accepted, evidence)

    def test_full_m3_inheritance_freezes_every_accepted_part_and_type(self):
        root = Path(__file__).resolve().parents[1]
        accepted = json.loads((root / "specifications/M3-results.json").read_text())
        pin = json.loads((root / "specifications/accepted-M3.json").read_text())
        self.assertEqual(M3_ACCEPTED_REVISION, pin["mathematical_commit"])
        self.assertEqual(accepted["current_stage"], "M3b")
        names = [name for r in accepted["results"] for p in r["parts"] for name in p["declarations"]]
        rows = {name: {"type": "accepted type of " + name} for name in names}
        evidence = {"declarations": rows}
        self.assertEqual(len(check_m3_inherited(rows, accepted, accepted, evidence)), 51)
        for i, result in enumerate(accepted["results"]):
            for j, part in enumerate(result["parts"]):
                for key, value in [("declarations", ["Other.safe"]),
                                   ("stage", "M3b" if part["stage"] == "M3a" else "M3a")]:
                    changed = json.loads(json.dumps(accepted))
                    changed["results"][i]["parts"][j][key] = value
                    with self.assertRaises(ValueError):
                        check_m3_inherited(rows, changed, accepted, evidence)
        for name in names:
            weakened = dict(rows)
            weakened[name] = {"type": "weakened"}
            with self.assertRaises(ValueError):
                check_m3_inherited(weakened, accepted, accepted, evidence)

    def test_m4_frozen_algorithm_metadata_and_stage_layout(self):
        root = Path(__file__).resolve().parents[1]
        contract = json.loads((root / "specifications/M4-results.json").read_text())
        check_m4_layout(contract, contract)
        for field in ["contract", "contract_sha256", "precision_contract", "precision_sha256",
                      "reviewed_proposal_revision", "approval_record"]:
            changed = json.loads(json.dumps(contract))
            changed[field] = "redirected"
            with self.assertRaises(ValueError):
                check_m4_layout(changed, contract)
        for i, result in enumerate(contract["results"]):
            changed = json.loads(json.dumps(contract))
            changed["results"][i]["stage"] = "M4b" if result["stage"] == "M4a" else "M4a"
            with self.assertRaises(ValueError):
                check_m4_layout(changed, contract)
        check_result_ids(contract, (root / contract["contract"]).read_text(), "M4")

    def test_m4_deferred_composition_cannot_be_claimed_complete(self):
        contract = {"results": [{"id": "M4-W", "stage": "M4a", "declarations": ["W.local"]},
                                {"id": "M4-C", "stage": "M4b", "declarations": []}]}
        rows = {"W.local": record("W.local")}
        self.assertEqual(check_promises(rows, contract, "M4a", ("M4a", "M4b")), ["W.local"])
        with self.assertRaises(ValueError):
            check_promises(rows, contract, "M4b", ("M4a", "M4b"))

    def test_m4a_accepted_records_types_and_future_stage(self):
        root = Path(__file__).resolve().parents[1]
        accepted = json.loads((root / "specifications/M4-results.json").read_text())
        accepted["current_stage"] = "M4a"
        pin = json.loads((root / "specifications/accepted-M4a.json").read_text())
        self.assertEqual(M4A_ACCEPTED_REVISION, pin["mathematical_commit"])
        active = [r for r in accepted["results"] if r["stage"] == "M4a"]
        rows = {name: {"type": "accepted type " + name} for r in active for name in r["declarations"]}
        evidence = {"declarations": rows}
        self.assertEqual(len(check_m4_inherited(rows, accepted, accepted, evidence)), 23)
        for i, result in enumerate(accepted["results"]):
            if result["stage"] != "M4a":
                continue
            for key, value in [("stage", "M4b"), ("declarations", ["Other.safe"])]:
                changed = json.loads(json.dumps(accepted))
                changed["results"][i][key] = value
                with self.assertRaises(ValueError):
                    check_m4_inherited(rows, changed, accepted, evidence)
        for name in rows:
            weakened = dict(rows)
            weakened[name] = {"type": "weakened"}
            with self.assertRaises(ValueError):
                check_m4_inherited(weakened, accepted, accepted, evidence)
        future = json.loads(json.dumps(accepted))
        future["current_stage"] = "M4b"
        for r in future["results"]:
            if r["stage"] == "M4b":
                r["declarations"] = ["New." + r["id"]]
        check_m4_inherited(rows, future, accepted, evidence)

    def test_full_m4_preserves_all_records_ordered_bindings_types_and_stage(self):
        root = Path(__file__).resolve().parents[1]
        accepted = json.loads((root / "specifications/M4-results.json").read_text())
        pin = json.loads((root / "specifications/accepted-M4.json").read_text())
        self.assertEqual(ACCEPTED_BASELINE, pin["mathematical_commit"])
        self.assertEqual(M4_ACCEPTED_REVISION, pin["mathematical_commit"])
        self.assertEqual(accepted["current_stage"], "M4b")
        names = [name for r in accepted["results"] for name in r["declarations"]]
        rows = {name: {"type": "accepted type " + name} for name in names}
        evidence = {"declarations": rows}
        self.assertEqual(len(check_m4_inherited(rows, accepted, accepted, evidence)), 39)
        for i, result in enumerate(accepted["results"]):
            for key, value in [("stage", "M4b" if result["stage"] == "M4a" else "M4a"),
                               ("declarations", ["Other.safe"]),
                               ("declarations", result["declarations"][::-1])]:
                changed = json.loads(json.dumps(accepted))
                changed["results"][i][key] = value
                with self.assertRaises(ValueError):
                    check_m4_inherited(rows, changed, accepted, evidence)
        for name in names:
            weakened = dict(rows)
            weakened[name] = {"type": "weakened"}
            with self.assertRaises(ValueError):
                check_m4_inherited(weakened, accepted, accepted, evidence)
        rollback = json.loads(json.dumps(accepted))
        rollback["current_stage"] = "M4a"
        with self.assertRaises(ValueError):
            check_m4_inherited(rows, rollback, accepted, evidence)

    def test_m5_frozen_metadata_and_exact_stage_layout(self):
        root = Path(__file__).resolve().parents[1]
        contract = json.loads((root / "specifications/M5-results.json").read_text())
        check_m5_layout(contract, contract)
        for field in ["contract", "contract_sha256", "reviewed_proposal_revision", "approval_record", "current_stage"]:
            changed = json.loads(json.dumps(contract))
            changed[field] = "redirected"
            with self.assertRaises(ValueError):
                check_m5_layout(changed, contract)
        for i in range(len(contract["results"])):
            changed = json.loads(json.dumps(contract))
            changed["results"][i]["stage"] = "M4b"
            with self.assertRaises(ValueError):
                check_m5_layout(changed, contract)
        check_result_ids(contract, (root / contract["contract"]).read_text(), "M5")

    def test_m5_all_six_active_ids_require_real_theorems(self):
        results = [{"id": "M5-" + k, "stage": "M5", "declarations": ["Proof." + k]}
                   for k in ["U", "V", "B", "L", "C", "O"]]
        contract = {"results": results}
        rows = {r["declarations"][0]: record(r["declarations"][0]) for r in results}
        self.assertEqual(len(check_promises(rows, contract, "M5", ("M5",))), 6)
        for i, result in enumerate(results):
            changed = json.loads(json.dumps(contract))
            changed["results"][i]["declarations"] = []
            with self.assertRaises(ValueError):
                check_promises(rows, changed, "M5", ("M5",))
            invalid = dict(rows)
            name = result["declarations"][0]
            invalid[name] = dict(rows[name], kind="definition")
            with self.assertRaises(ValueError):
                check_promises(invalid, contract, "M5", ("M5",))

    def test_empty_or_malformed_inventory(self):
        for output in ["", "CFDLEAN_DECL {bad}"]:
            with self.assertRaises(ValueError):
                parse_axioms(output)



import verify


class PortMapTests(unittest.TestCase):
    def test_pinned_map_loads(self):
        data = (verify.ROOT / verify.MC_PORT_MAP).read_bytes()
        mapping = verify.load_port_map(data)
        self.assertEqual(len(mapping), verify.MC_PORT_COUNT)

    def test_tampered_map_rejected(self):
        data = (verify.ROOT / verify.MC_PORT_MAP).read_bytes() + b" "
        with self.assertRaises(ValueError):
            verify.load_port_map(data)

    def test_type_guard(self):
        mapping = {"a": {"classification": "notation", "accepted_type": "old", "current_type": "new"},
                   "b": {"classification": "other", "accepted_type": "old", "current_type": "new"}}
        self.assertTrue(verify.same_or_ported_type("x", "t", "t", mapping))
        self.assertTrue(verify.same_or_ported_type("a", "old", "new", mapping))
        self.assertFalse(verify.same_or_ported_type("a", "old", "forged", mapping))
        self.assertFalse(verify.same_or_ported_type("b", "old", "new", mapping))
        self.assertFalse(verify.same_or_ported_type("c", "old", "new", mapping))


class MCNTests(unittest.TestCase):
    SPEC = " ".join(f"`{name}`" for name in
                    ["Basic", "LogMean", "Simplex", "Mesh", "Boundary", "PairFlux", "Galerkin", "Production", "Bridge"])

    def setUp(self):
        self.results = [{"id": f"MC-N.X-{i}", "theorem": f"CFDLean.Num.t{i}", "module": "CFDLean.Discrete.Mesh"}
                        for i in range(verify.MC_N_COUNT)]
        self.rows = {}
        for r in self.results:
            row = record(r["theorem"], ["propext"])
            row["module"] = r["module"]
            self.rows[r["theorem"]] = row

    def check(self, results=None, rows=None, other=()):
        return verify.check_mc_n(self.rows if rows is None else rows,
                                 {"results": self.results if results is None else results}, list(other), self.SPEC)

    def test_all_promised_theorems_accepted(self):
        self.assertEqual(len(self.check()), verify.MC_N_COUNT)

    def test_missing_wrong_kind_or_axiom_rejected(self):
        for mutate in [lambda rows, n: rows.pop(n),
                       lambda rows, n: rows[n].update(kind="definition"),
                       lambda rows, n: rows[n].update(root=False),
                       lambda rows, n: rows[n].update(axioms=["sorryAx"]),
                       lambda rows, n: rows[n].update(module="CFDLean.Geometry.MedianDualBridge")]:
            rows = json.loads(json.dumps(self.rows))
            mutate(rows, "CFDLean.Num.t0")
            with self.assertRaises(ValueError):
                self.check(rows=rows)

    def test_scope_count_ids_and_namespace_frozen(self):
        for results in [self.results[1:], self.results[:-1] + self.results[:1],
                        [dict(self.results[0], theorem="CFDLean.Time.t0")] + self.results[1:],
                        [dict(self.results[0], module="CFDLean.Time.Controls")] + self.results[1:],
                        [dict(self.results[0], module="CFDLean.Num.Mesh")] + self.results[1:],
                        [dict(self.results[0], id="M5-X")] + self.results[1:]]:
            with self.assertRaises(ValueError):
                self.check(results=results)

    def test_cannot_rebind_m1_m5_theorem(self):
        with self.assertRaises(ValueError):
            self.check(other=["CFDLean.Num.t3"])

    def test_m1_m5_sources_frozen(self):
        base = {"CFDLean/Core/State.lean": b"a", "CFDLean/Time/Controls.lean": b"b"}
        current = dict(base, **{"CFDLean/Num/Mesh.lean": b"new", "CFDLean/Num.lean": b"new"})
        paths = sorted(current)

        def blob(path):
            if path not in base:
                raise verify.subprocess.CalledProcessError(128, "git")
            return base[path]
        self.assertEqual(verify.check_mc_n_sources(paths, current.__getitem__, blob), 2)
        current["CFDLean/Time/Controls.lean"] = b"weakened"
        with self.assertRaises(ValueError):
            verify.check_mc_n_sources(paths, current.__getitem__, blob)
        with self.assertRaises(ValueError):
            verify.check_mc_n_sources(["CFDLean/Num/Mesh.lean"], current.__getitem__, blob)


class CatalogTests(unittest.TestCase):
    INTEGRITY = "import CFDLean\n#print axioms m1_a\n#print axioms m1_b\n"

    def setUp(self):
        self.expected = verify.m1_accepted_theorems(self.INTEGRITY)
        self.expected.update(verify.catalog_index("M2", {"results": [
            {"id": "M2-J", "stage": "M2a", "declarations": ["CFDLean.R.j"]}]}))
        self.expected.update(verify.catalog_index("M3", {"results": [
            {"id": "M3-G", "parts": [{"stage": "M3b", "declarations": ["CFDLean.G.g"]}]}]}))
        self.expected.update(verify.catalog_index("M5", {"results": [
            {"id": "M5-U", "stage": "M5", "declarations": ["CFDLean.Time.u"]}]}))
        self.expected.update(verify.catalog_index("MC-N", {"results": [
            {"id": "MC-N.P1-2.4", "theorem": "CFDLean.Num.n", "module": "CFDLean.Foundations.LogMean"}]}))
        self.expected.update(verify.jst1_catalog_index([{"bindings": {"P1-2.4": {"theorem": "CFDLean.JST1.Proofs.p"}}}]))
        self.rows, entries = {}, []
        for name, (milestone, result_id) in self.expected.items():
            row = record(name)
            row["module"] = "Mod." + name
            self.rows[name] = row
            entries.append({"name": name, "id": result_id or "M1-1", "milestone": milestone,
                            "module": row["module"], "status": verify.CATALOG_STATUS[milestone],
                            "layer": "Geometry", "methods": ["FVM"], "summary": "s.", "source": "spec ID"})
        self.catalog = {"theorems": entries}

    def mutated(self, index, **change):
        entries = [dict(entry) for entry in self.catalog["theorems"]]
        entries[index].update(change)
        return {"theorems": entries}

    def test_m1_list_and_index(self):
        self.assertEqual(set(verify.m1_accepted_theorems(self.INTEGRITY)), {"CFDLean.m1_a", "CFDLean.m1_b"})
        for text in ["import CFDLean\n", self.INTEGRITY + "#print axioms m1_a\n"]:
            with self.assertRaises(ValueError):
                verify.m1_accepted_theorems(text)
        with self.assertRaises(ValueError):
            verify.catalog_index("M2", {"results": [{"id": "M2-J", "stage": "M2a", "declarations": ["A.x", "A.x"]}]})

    def test_exact_cover_accepted(self):
        self.assertEqual(verify.check_catalog(self.catalog, self.expected, self.rows), 7)

    def test_missing_extra_or_duplicate_rejected(self):
        entries = self.catalog["theorems"]
        extra = dict(entries[0], name="CFDLean.extra")
        for bad in [entries[1:], entries + [extra], entries + entries[:1]]:
            with self.assertRaises(ValueError):
                verify.check_catalog({"theorems": bad}, self.expected, self.rows)

    def test_invalid_values_rejected(self):
        m2 = next(i for i, e in enumerate(self.catalog["theorems"]) if e["milestone"] == "M2")
        m1 = next(i for i, e in enumerate(self.catalog["theorems"]) if e["milestone"] == "M1")
        mcn = next(i for i, e in enumerate(self.catalog["theorems"]) if e["milestone"] == "MC-N")
        jst1 = next(i for i, e in enumerate(self.catalog["theorems"]) if e["milestone"] == "JST1")
        for index, change in [(m2, {"layer": "Numerics"}), (m2, {"methods": []}), (m2, {"methods": ["FVM", "FEM"]}),
                              (m2, {"methods": ["FEM", "method-free"]}), (m2, {"methods": "FVM"}),
                              (m2, {"status": "pending"}), (mcn, {"status": "accepted"}),
                              (jst1, {"status": "accepted"}), (jst1, {"id": "P1-2.5"}), (jst1, {"milestone": "MC-N"}), (m2, {"milestone": "M3"}),
                              (m2, {"id": "M2-A"}), (m1, {"id": "M2-J"}), (m2, {"summary": " "}),
                              (m2, {"module": "Other"}), (m2, {"extra": 1})]:
            with self.assertRaises(ValueError, msg=str(change)):
                verify.check_catalog(self.mutated(index, **change), self.expected, self.rows)
        name = self.catalog["theorems"][m2]["name"]
        for kind, root in [("definition", True), ("theorem", False)]:
            rows = dict(self.rows, **{name: dict(self.rows[name], kind=kind, root=root)})
            with self.assertRaises(ValueError):
                verify.check_catalog(self.catalog, self.expected, rows)

    def test_both_methods_and_method_free_accepted(self):
        catalog = self.mutated(0, methods=["FEM", "FVM"])
        catalog["theorems"][1]["methods"] = ["method-free"]
        self.assertEqual(verify.check_catalog(catalog, self.expected, self.rows), 7)

    def test_readme_must_equal_generated_text(self):
        render = verify.load_catalog_renderer()
        text = render(self.catalog)
        self.assertIn("## Geometry (7)", text)
        verify.check_catalog_readme(self.catalog, text, render)
        with self.assertRaises(ValueError):
            verify.check_catalog_readme(self.catalog, text + "edit\n", render)

    def test_committed_catalog_covers_result_maps(self):
        root = verify.ROOT
        expected = verify.m1_accepted_theorems((root / "Integrity.lean").read_text())
        for milestone, path in [("M2", "specifications/M2-results.json"), ("M3", "specifications/M3-results.json"),
                                ("M4", "specifications/M4-results.json"), ("M5", "specifications/M5-results.json"),
                                ("MC-N", verify.MC_N_RESULTS)] + [
                                    (m, stem + "-results.json") for m, stem, _ in verify.FV_CONTRACTS] + [
                                    (m, pins["results"]) for m, pins in verify.BURGERS.items()]:
            expected.update(verify.catalog_index(milestone, json.loads((root / path).read_text())))
        expected.update(verify.jst1_catalog_index([json.loads((root / path).read_text())
                                                   for path, _ in verify.JST1_RESULTS]))
        catalog = json.loads((root / verify.CATALOG).read_text(encoding="utf-8"))
        fv1d_claims = {"FV1D-B", "FV1D-F", "FV1D-K", "FV1D-C"}
        self.assertCountEqual([rid for milestone, rid in expected.values() if milestone == "FV1D"], fv1d_claims)
        self.assertCountEqual([rid for m, rid in expected.values() if m == "FVP"], ['FVP-P'])
        self.assertEqual(len(expected), 15 + verify.MC_PORT_COUNT + verify.MC_N_COUNT + len(fv1d_claims) + 1
                         + sum(pins["count"] for pins in verify.BURGERS.values()) + verify.JST1_COUNT)
        rows = json.loads((root / "evidence/verification.json").read_text())["declarations"]
        self.assertEqual(verify.check_catalog(catalog, expected, rows), len(expected))
        verify.check_catalog_readme(catalog, (root / verify.CATALOG_README).read_text(encoding="utf-8"),
                                    verify.load_catalog_renderer())


class JST1Tests(unittest.TestCase):
    def setUp(self):
        self.records, self.rows, lines = [], {}, []
        for paper, count in [("P1", 36), ("P2", 36), ("P3", 20), ("P4", 13), ("P5", 7), ("P6", 3), ("P7", 4), ("P8", 2)]:
            bindings = {}
            for i in range(count):
                rid = f"{paper}-{i // 10 + 1}.{i % 10}"
                suffix = rid.replace("-", "_").replace(".", "_")
                module = "CFDLean.Papers.JST1.Proofs.Item" + paper
                binding = {"statement": f"CFDLean.JST1.Spec.{suffix}", "theorem": f"CFDLean.JST1.Proofs.p{suffix}",
                           "file": module.replace(".", "/") + ".lean", "module": module}
                row = record(binding["theorem"], ["propext"])
                row.update(module=module, direct=[], type=binding["statement"])
                if paper == "P1" and i < 5:
                    binding["core_theorem"] = f"CFDLean.Num.c{i}"
                    row["direct"] = [binding["core_theorem"]]
                self.rows[binding["theorem"]] = row
                self.rows[binding["statement"]] = dict(record(binding["statement"]), kind="definition", root=True)
                bindings[rid] = binding
                lines.append(f"example : {binding['statement']} := {binding['theorem']}")
            self.records.append({"bindings": bindings})
        self.audit = "import Integrity\n" + "\n".join(lines) + "\n"
        self.core = [f"CFDLean.Num.c{i}" for i in range(5)]
        self.ids = {rid for record in self.records for rid in record["bindings"]}

    def check(self, records=None, rows=None, audit=None, ids=None):
        return verify.check_jst1(self.rows if rows is None else rows, self.records if records is None else records,
                                 self.audit if audit is None else audit, self.core, self.ids if ids is None else ids)

    def mutated_binding(self, **change):
        records = json.loads(json.dumps(self.records))
        records[0]["bindings"]["P1-1.0"].update(change)
        return records

    def test_all_bindings_accepted(self):
        names, delegated = self.check()
        self.assertEqual((len(names), len(delegated)), (verify.JST1_COUNT, 5))

    def test_binding_must_be_in_audit(self):
        line = "example : CFDLean.JST1.Spec.P1_1_0 := CFDLean.JST1.Proofs.pP1_1_0\n"
        self.assertIn(line, self.audit)
        for audit in [self.audit.replace(line, ""), self.audit.replace(line, "-- " + line),
                      self.audit.replace(line, "/-\n" + line + "-/\n"),
                      self.audit.replace(line, "/- outer /- inner -/\n" + line + "-/\n"),
                      self.audit.replace(line, line.replace("pP1_1_0", "pP1_1_1"))]:
            with self.assertRaises(ValueError):
                self.check(audit=audit)
        self.check(audit=self.audit.replace(line, '#eval "-- /-"\n' + line))

    def test_comment_stripping(self):
        text = 'a -- x\nb /- c /- d -/ e -/ f "g -- /- h" i\n'
        self.assertEqual(verify.strip_lean_comments(text), 'a \nb  f "g -- /- h" i\n')

    def test_ids_are_the_frozen_statements(self):
        spec = "def P1_1_0 : Prop :=\n  True\n/-- P1-1.1 -/\ndef P1_1_1 : Prop := True\ndef other : Prop := True\n"
        self.assertEqual(verify.jst1_frozen_ids([spec] + [f"def P2_{i}_0 : Prop :=" for i in range(119)]),
                         {"P1-1.0", "P1-1.1"} | {f"P2-{i}.0" for i in range(119)})
        with self.assertRaises(ValueError):
            verify.jst1_frozen_ids([spec])
        with self.assertRaises(ValueError):
            self.check(ids=(self.ids - {"P1-1.0"}) | {"P1-9.9"})
        moved = json.loads(json.dumps(self.records))
        moved[1]["bindings"]["P1-1.0"] = moved[0]["bindings"].pop("P1-1.0")
        with self.assertRaises(ValueError):
            self.check(records=moved)
        rebound = json.loads(json.dumps(self.records))
        b = rebound[0]["bindings"]
        b["P1-1.0"]["statement"], b["P1-1.1"]["statement"] = b["P1-1.1"]["statement"], b["P1-1.0"]["statement"]
        with self.assertRaises(ValueError):
            self.check(records=rebound)

    def test_eight_result_maps(self):
        """P8 (MR-4 extension): exactly the eight maps P1-P8; a P4-P8 ID only in its own map; P9 statements are not
        IDs."""
        for short in (self.records[:3], self.records[:4], self.records[:5], self.records[:6], self.records[:7]):
            with self.assertRaises(ValueError):
                self.check(records=short)
        for src, dst, rid in ((3, 2, "P4-1.0"), (4, 3, "P5-1.0"), (5, 4, "P6-1.0"), (6, 5, "P7-1.0"), (7, 6, "P8-1.1")):
            moved = json.loads(json.dumps(self.records))
            moved[dst]["bindings"][rid] = moved[src]["bindings"].pop(rid)
            with self.assertRaises(ValueError):
                self.check(records=moved)
        names, _ = self.check()
        for name in ("pP4_1_2", "pP5_1_6", "pP6_1_2", "pP7_1_3", "pP8_1_1"):
            self.assertIn("CFDLean.JST1.Proofs." + name, names)
        spec = "\n".join(f"def P8_{i}_0 : Prop :=" for i in range(121))
        self.assertEqual(len(verify.jst1_frozen_ids([spec])), 121)
        with self.assertRaises(ValueError):
            verify.jst1_frozen_ids([spec.replace("def P8_0_0", "def P9_0_0")])

    def test_theorem_type_is_its_statement(self):
        rows = json.loads(json.dumps(self.rows))
        rows["CFDLean.JST1.Proofs.pP2_1_0"]["type"] = "CFDLean.JST1.Spec.P2_1_1"
        with self.assertRaises(ValueError):
            self.check(rows=rows)

    def test_theorem_kind_axioms_module_and_statement(self):
        name, statement = "CFDLean.JST1.Proofs.pP1_1_7", "CFDLean.JST1.Spec.P1_1_7"
        for mutate in [lambda rows: rows.pop(name), lambda rows: rows[name].update(kind="definition"),
                       lambda rows: rows[name].update(root=False), lambda rows: rows[name].update(unsafe=True),
                       lambda rows: rows[name].update(axioms=["sorryAx"]),
                       lambda rows: rows[name].update(axioms=["propext", "CFDLean.myAxiom"]),
                       lambda rows: rows[name].update(module="CFDLean.Papers.JST1.Proofs.Other"),
                       lambda rows: rows[statement].update(kind="theorem"), lambda rows: rows.pop(statement)]:
            rows = json.loads(json.dumps(self.rows))
            mutate(rows)
            with self.assertRaises(ValueError):
                self.check(rows=rows)
        rows = json.loads(json.dumps(self.rows))
        rows[name]["axioms"] = ["Quot.sound", "Classical.choice", "propext"]
        self.check(rows=rows)

    def test_delegation_must_use_core_theorem(self):
        rows = json.loads(json.dumps(self.rows))
        rows["CFDLean.JST1.Proofs.pP1_1_0"]["direct"] = []
        with self.assertRaises(ValueError):
            self.check(rows=rows)
        with self.assertRaises(ValueError):
            self.check(records=self.mutated_binding(core_theorem="CFDLean.Num.other"))

    def test_scope_ids_and_namespace(self):
        records = json.loads(json.dumps(self.records))
        del records[2]["bindings"]["P3-1.0"]
        bad = [records, self.records + [{"bindings": {"P8-1.0": self.records[0]["bindings"]["P1-1.0"]}}],
               self.mutated_binding(theorem="CFDLean.JST1.Proofs.pP1_1_1"),
               self.mutated_binding(statement="Paper1.Spec.P1_1_0"),
               self.mutated_binding(file="CFDLean/Papers/JST1/Proofs/Other.lean")]
        renamed = json.loads(json.dumps(self.records))
        renamed[0]["bindings"]["P1-x"] = renamed[0]["bindings"].pop("P1-1.0")
        for records in bad + [renamed]:
            with self.assertRaises(ValueError):
                self.check(records=records)

    def test_frozen_list_pinned_and_well_formed(self):
        data = (verify.ROOT / verify.JST1_FROZEN).read_bytes()
        entries = verify.load_jst1_frozen(data)
        self.assertIn("CFDLean/Papers/JST1/Spec/Item1.lean", entries)
        self.assertTrue(all(not path.startswith("CFDLean/Papers/JST1/Proofs/") for path in entries))
        with self.assertRaises(ValueError):
            verify.load_jst1_frozen(data + b"0" * 64 + b"  CFDLean/Papers/JST1/Spec/New.lean\n")
        original = verify.JST1_FROZEN_SHA256
        try:
            for bad in [b"", b"abc  CFDLean/A.lean\n", b"0" * 64 + b" CFDLean/A.lean\n",
                        b"0" * 64 + b"  scripts/A.py\n", (b"0" * 64 + b"  CFDLean/A.lean\n") * 2]:
                verify.JST1_FROZEN_SHA256 = verify.hashlib.sha256(bad).hexdigest()
                with self.assertRaises(ValueError, msg=bad):
                    verify.load_jst1_frozen(bad)
        finally:
            verify.JST1_FROZEN_SHA256 = original

    def test_frozen_hashes_and_coverage(self):
        files = {"CFDLean/Papers/JST1/Spec/A.lean": b"def P : Prop := True\n",
                 "CFDLean/Papers/JST1/Proofs/A.lean": b"theorem p : P := trivial\n",
                 "CFDLean/Geometry/Simplex.lean": b"def cross3 := 0\n"}
        entries = {path: verify.hashlib.sha256(data).hexdigest() for path, data in files.items() if "Proofs" not in path}
        self.assertEqual(verify.check_jst1_frozen(entries, files.__getitem__, sorted(files)), 2)
        for changed in [dict(files, **{"CFDLean/Papers/JST1/Spec/A.lean": b"def P : Prop := False\n"}),
                        dict(files, **{"CFDLean/Geometry/Simplex.lean": b"def cross3 := 1\n"}),
                        {k: v for k, v in files.items() if k != "CFDLean/Geometry/Simplex.lean"}]:
            with self.assertRaises(ValueError):
                verify.check_jst1_frozen(entries, changed.__getitem__, sorted(changed))
        extra = dict(files, **{"CFDLean/Papers/JST1/Euler/New.lean": b"def x := 0\n"})
        with self.assertRaises(ValueError):
            verify.check_jst1_frozen(entries, extra.__getitem__, sorted(extra))

    def test_forbidden_tokens(self):
        clean = {"CFDLean/Papers/JST1/A.lean": b"theorem t : True := trivial -- the axioms are printed\n"}
        self.assertEqual(verify.check_forbidden_tokens(sorted(clean), clean.__getitem__), 1)
        for text in [b"theorem t : False := sorry\n", b"theorem t : False := by admit\n", b"axiom bad : False\n",
                     b"  private axiom bad : False\n", b"@[simp] axiom bad : False\n",
                     b"noncomputable section\nprotected axiom bad : False\n", b"set_option debug.skipKernelTC true\n", b"example : 2 = 2 := by native_decide\n",
                     b"@[implemented_by f] def g := 0\n", b"unsafe def g := 0\n", b"opaque g : Nat\n",
                     b"@[extern \"c\"] def g := 0\n"]:
            files = dict(clean, **{"CFDLean/Papers/JST1/B.lean": text})
            with self.assertRaises(ValueError, msg=text):
                verify.check_forbidden_tokens(sorted(files), files.__getitem__)
        with self.assertRaises(ValueError):
            verify.check_forbidden_tokens([], clean.__getitem__)

    def test_committed_results_and_audit(self):
        root = verify.ROOT
        records = []
        for path, count in verify.JST1_RESULTS:
            record = json.loads((root / path).read_text())
            self.assertEqual((len(record["bindings"]), record["frozen_hashes"]), (count, verify.JST1_FROZEN))
            records.append(record)
        audit = (root / "KernelAudit.lean").read_text()
        rows = json.loads((root / "evidence/verification.json").read_text())["declarations"]
        mcn = [r["theorem"] for r in json.loads((root / verify.MC_N_RESULTS).read_text())["results"]]
        spec = [p.read_text() for p in (root / verify.JST1_ROOT / "Spec").glob("*.lean")]
        names, delegated = verify.check_jst1(rows, records, audit, mcn, verify.jst1_frozen_ids(spec))
        self.assertEqual((len(names), len(delegated)), (121, 37))
        sources = sorted(str(p.relative_to(root)) for p in (root / "CFDLean").rglob("*.lean"))
        verify.check_jst1_frozen(verify.load_jst1_frozen((root / verify.JST1_FROZEN).read_bytes()),
                                 verify.read_source, sources)
        papers = [p for p in sources if p.startswith(verify.FORBIDDEN_ROOT + "/")]
        self.assertEqual(verify.check_forbidden_tokens(papers, verify.read_source), len(papers))


# The three per-milestone inherited-type checks as they were before MR-3 (verbatim, renamed), kept as the oracle that
# the table-driven verify.check_inherited_milestone must match on every input.
def legacy_check_inherited(rows, contract, accepted_contract, accepted_evidence):
    stages = ["M2a", "M2b", "M2c", "M2d"]
    active = [r for r in accepted_contract["results"]
              if stages.index(r["stage"]) <= stages.index(accepted_contract["current_stage"])]
    current = {r["id"]: r for r in contract["results"]}
    comparison = {}
    for inherited in active:
        if not inherited["declarations"] or current.get(inherited["id"]) != inherited:
            raise ValueError(f"Accepted {inherited['id']} binding or stage changed")
        for name in inherited["declarations"]:
            before = accepted_evidence["declarations"][name]["type"]
            after = rows[name]["type"]
            comparison[name] = {"accepted_type": before, "current_type": after}
            if not verify.same_or_ported_type(name, before, after):
                raise ValueError(f"Accepted theorem type changed: {name}")
    return comparison

def legacy_check_m3_inherited(rows, contract, accepted, evidence):
    stages = ("M3a", "M3b")
    current = {(r["id"], p["stage"]): p for r in contract["results"] for p in r["parts"]}
    comparisons = {}
    for result in accepted["results"]:
        for part in result["parts"]:
            if stages.index(part["stage"]) > stages.index(accepted["current_stage"]):
                continue
            if not part["declarations"] or current.get((result["id"], part["stage"])) != part:
                raise ValueError(f"Accepted {result['id']} part/bindings changed")
            for name in part["declarations"]:
                before, after = evidence["declarations"][name]["type"], rows[name]["type"]
                if not verify.same_or_ported_type(name, before, after):
                    raise ValueError(f"Accepted M3 type changed: {name}")
                comparisons[name] = {"accepted_type": before, "current_type": after}
    return comparisons

def legacy_check_m4_inherited(rows, contract, accepted, evidence):
    stages = ("M4a", "M4b")
    if stages.index(contract["current_stage"]) < stages.index(accepted["current_stage"]):
        raise ValueError("Accepted M4 current stage rolled back")
    current = {r["id"]: r for r in contract["results"]}
    comparisons = {}
    for result in accepted["results"]:
        if stages.index(result["stage"]) > stages.index(accepted["current_stage"]):
            continue
        if not result["declarations"] or current.get(result["id"]) != result:
            raise ValueError(f"Accepted {result['id']} binding/stage changed")
        for name in result["declarations"]:
            before, after = evidence["declarations"][name]["type"], rows[name]["type"]
            if not verify.same_or_ported_type(name, before, after):
                raise ValueError(f"Accepted M4 type changed: {name}")
            comparisons[name] = {"accepted_type": before, "current_type": after}
    return comparisons


LEGACY_INHERITED = {"M2": legacy_check_inherited, "M3": legacy_check_m3_inherited, "M4": legacy_check_m4_inherited}


def outcome(function, *args):
    try:
        return "ok", list(function(*args).items())
    except Exception as error:  # the exact exception type and message are part of the behaviour
        return type(error).__name__, str(error)


class InheritedTableTests(unittest.TestCase):
    """MR-3: the table-driven inherited check behaves exactly as the former M2/M3/M4 functions, on the committed
    accepted records (ACCEPTED_BASELINE) and current records, and on mutations of them."""

    @classmethod
    def setUpClass(cls):
        root = verify.ROOT
        show = lambda path: json.loads(verify.git_blob(verify.ACCEPTED_BASELINE, path))
        cls.evidence = show("evidence/verification.json")
        cls.accepted = {m: show(f"specifications/{m}-results.json") for m in ("M2", "M3", "M4")}
        cls.current = {m: json.loads((root / f"specifications/{m}-results.json").read_text()) for m in ("M2", "M3", "M4")}
        cls.rows = json.loads((root / "evidence/verification.json").read_text())["declarations"]

    def same(self, milestone, rows=None, current=None, accepted=None, evidence=None):
        args = (self.rows if rows is None else rows, self.current[milestone] if current is None else current,
                self.accepted[milestone] if accepted is None else accepted,
                self.evidence if evidence is None else evidence)
        new = outcome(verify.check_inherited_milestone, milestone, *args)
        self.assertEqual(new, outcome(LEGACY_INHERITED[milestone], *args), msg=milestone)
        return new

    def declarations(self, milestone):
        units = [p for r in self.accepted[milestone]["results"] for p in r["parts"]] if milestone == "M3" else \
            self.accepted[milestone]["results"]
        return [name for unit in units for name in unit["declarations"]]

    def test_table_covers_the_accepted_milestones(self):
        self.assertEqual(set(verify.INHERITED), {"M2", "M3", "M4"})

    def test_committed_records_pass_with_identical_comparisons(self):
        counts = {m: len(self.same(m)[1]) for m in ("M2", "M3", "M4")}
        self.assertEqual(counts, {"M2": 66, "M3": 51, "M4": 39})

    def test_one_promised_type_changed_per_milestone(self):
        messages = {"M2": "Accepted theorem type changed: {}", "M3": "Accepted M3 type changed: {}",
                    "M4": "Accepted M4 type changed: {}"}
        for milestone, message in messages.items():
            for name in (self.declarations(milestone)[0], self.declarations(milestone)[-1]):
                rows = json.loads(json.dumps(self.rows))
                rows[name]["type"] += " ∧ True"
                self.assertEqual(self.same(milestone, rows=rows), ("ValueError", message.format(name)))

    def test_binding_stage_and_record_mutations(self):
        for milestone in ("M2", "M3", "M4"):
            first = self.accepted[milestone]["results"][0]
            mutations = []
            for field, value in [("declarations", []), ("stage", "X"), ("id", "Z-9")]:
                current = json.loads(json.dumps(self.current[milestone]))
                unit = current["results"][0]["parts"][0] if milestone == "M3" else current["results"][0]
                unit[field] = value
                mutations.append(current)
            current = json.loads(json.dumps(self.current[milestone]))
            del current["results"][-1]
            mutations.append(current)
            for current in mutations:
                result = self.same(milestone, current=current)
                self.assertNotEqual(result[0], "ok", msg=(milestone, first["id"]))
            # A repeated identical binding is accepted by both (the former functions keyed the current results).
            current = json.loads(json.dumps(self.current[milestone]))
            current["results"].append(json.loads(json.dumps(current["results"][0])))
            self.assertEqual(self.same(milestone, current=current)[0], "ok")
            accepted = json.loads(json.dumps(self.accepted[milestone]))
            unit = accepted["results"][1]["parts"][0] if milestone == "M3" else accepted["results"][1]
            unit["stage"] = "bogus"
            self.same(milestone, accepted=accepted)
            accepted = json.loads(json.dumps(self.accepted[milestone]))
            accepted["current_stage"] = "bogus"
            self.same(milestone, accepted=accepted)
            rows = dict(self.rows)
            del rows[self.declarations(milestone)[0]]
            self.assertEqual(self.same(milestone, rows=rows)[0], "KeyError")
            evidence = json.loads(json.dumps(self.evidence))
            evidence["declarations"][self.declarations(milestone)[0]]["type"] = "forged"
            self.assertEqual(self.same(milestone, evidence=evidence)[0], "ValueError")

    def test_m2_filters_all_stages_before_checking_bindings(self):
        accepted = json.loads(json.dumps(self.accepted["M2"]))
        current = json.loads(json.dumps(self.current["M2"]))
        current["results"][0]["declarations"] = []
        accepted["results"][-1]["stage"] = "bogus"
        self.assertEqual(self.same("M2", current=current, accepted=accepted)[0], "ValueError")

    def test_m2_reviewer_case_bogus_stage_before_missing_id(self):
        accepted = json.loads(json.dumps(self.accepted["M2"]))
        accepted["results"][0]["stage"] = "bogus"
        current = json.loads(json.dumps(self.current["M2"]))
        del current["results"][0]["id"]
        # The message of `list.index` depends on the Python version ("'bogus' is not in list" or
        # "list.index(x): x not in list"); the exception type shows that the stage is checked before the ID.
        result = self.same("M2", current=current, accepted=accepted)
        self.assertEqual(result[0], "ValueError")
        self.assertIn("not in list", result[1])
        accepted = json.loads(json.dumps(self.accepted["M3"]))
        del accepted["results"][-1]["id"]
        accepted["current_stage"] = "M3a"
        self.same("M3", accepted=accepted)

    def test_m4_rollback_and_unaccepted_future_stage(self):
        current = json.loads(json.dumps(self.current["M4"]))
        current["current_stage"] = "M4a"
        self.assertEqual(self.same("M4", current=current), ("ValueError", "Accepted M4 current stage rolled back"))
        accepted = json.loads(json.dumps(self.accepted["M4"]))
        accepted["current_stage"] = "M4a"
        self.assertEqual(self.same("M4", accepted=accepted)[0], "ok")


class RawTypeTests(unittest.TestCase):
    def setUp(self):
        self.rows = {name: dict(record(name), type=f"T {name}", raw_type=f"R {name}") for name in ("A.x", "A.y")}
        self.types = verify.promised_types(self.rows, ["A.y", "A.x"])
        self.data = verify.raw_types_record(self.types).encode()
        self.original = verify.RAW_TYPES_SHA256
        verify.RAW_TYPES_SHA256 = verify.hashlib.sha256(self.data).hexdigest()

    def tearDown(self):
        verify.RAW_TYPES_SHA256 = self.original

    def test_pin_accepts_unchanged_types(self):
        self.assertEqual(list(self.types), ["A.x", "A.y"])
        self.assertEqual(verify.check_raw_types(self.types, self.data), 2)

    def test_changed_raw_or_pretty_type_rejected(self):
        for field in ("raw_type", "type"):
            types = json.loads(json.dumps(self.types))
            types["A.x"][field] += " "
            with self.assertRaises(ValueError, msg=field):
                verify.check_raw_types(types, self.data)

    def test_cover_and_file_pin(self):
        with self.assertRaises(ValueError):
            verify.check_raw_types({"A.x": self.types["A.x"]}, self.data)
        with self.assertRaises(ValueError):
            verify.check_raw_types(dict(self.types, **{"A.z": self.types["A.x"]}), self.data)
        forged = self.data.replace(b"R A.x", b"R A.z")
        with self.assertRaises(ValueError):
            verify.check_raw_types(self.types, forged)

    def test_promised_theorem_needs_a_raw_type(self):
        for change in [{"raw_type": None}, {"kind": "definition"}]:
            rows = dict(self.rows, **{"A.x": dict(self.rows["A.x"], **change)})
            with self.assertRaises(ValueError):
                verify.promised_types(rows, ["A.x"])
        with self.assertRaises(ValueError):
            verify.promised_types(self.rows, ["A.missing"])

    def test_committed_pin_covers_the_catalog(self):
        root = verify.ROOT
        verify.RAW_TYPES_SHA256 = self.original
        rows = json.loads((root / "evidence/verification.json").read_text())["declarations"]
        names = [entry["name"] for entry in json.loads((root / verify.CATALOG).read_text(encoding="utf-8"))["theorems"]]
        types = verify.promised_types(rows, names)
        self.assertEqual(verify.check_raw_types(types, (root / verify.RAW_TYPES).read_bytes()), len(names))


class JST1ComparatorTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        root = verify.ROOT
        cls.records = [json.loads((root / path).read_text()) for path, _ in verify.JST1_RESULTS]
        cls.rows = json.loads((root / "evidence/verification.json").read_text())["declarations"]
        cls.files = {path: (root / path).read_bytes() for path in (verify.JST1_CHALLENGE, verify.JST1_COMPARATOR)}

    def check(self, rows=None, files=None):
        files = self.files if files is None else files
        return verify.check_jst1_comparator(self.rows if rows is None else rows, self.records, files.__getitem__)

    def test_committed_files_pass(self):
        self.assertEqual(self.check(), 121)

    def test_challenge_and_configuration_pinned(self):
        challenge = self.files[verify.JST1_CHALLENGE]
        config = json.loads(self.files[verify.JST1_COMPARATOR])
        bad_configs = [dict(config, theorem_names=config["theorem_names"][1:]),
                       dict(config, permitted_axioms=["propext", "sorryAx"]), dict(config, solution_module="X")]
        for files in [dict(self.files, **{verify.JST1_CHALLENGE: challenge.replace(b"P1_1_1", b"P1_1_2", 1)})] + [
                dict(self.files, **{verify.JST1_COMPARATOR: json.dumps(c).encode()}) for c in bad_configs]:
            with self.assertRaises(ValueError):
                self.check(files=files)

    def test_solution_theorem_type_axioms_and_proof(self):
        name = verify.JST1_SOLUTION + ".p2_6_1"
        for change in [{"type": "CFDLean.JST1.Spec.P2_6_2"}, {"axioms": ["sorryAx"]}, {"direct": []},
                       {"kind": "definition"}, {"module": "CFDLean.Other"}]:
            rows = dict(self.rows, **{name: dict(self.rows[name], **change)})
            with self.assertRaises(ValueError, msg=str(change)):
                self.check(rows=rows)


class MRLayoutTests(unittest.TestCase):
    """MR-1: moved files are found only through the pinned path map and may differ only in their `import` header."""
    OLD = b"import CFDLean.Core.State\nimport Mathlib.Tactic\n\nnamespace CFDLean\ntheorem t : True := trivial\nend CFDLean\n"
    NEW = b"import CFDLean.Physics.Euler.State\nimport Mathlib.Tactic\n\nnamespace CFDLean\ntheorem t : True := trivial\nend CFDLean\n"
    MOVES = {"CFDLean/Core/Flux.lean": "CFDLean/Physics/Euler/Flux.lean",
             "CFDLean/Time/Step.lean": "CFDLean/Time/Step.lean"}

    def blob(self, refs):
        def get(revision, path):
            if (revision, path) not in refs:
                raise verify.subprocess.CalledProcessError(128, "git")
            return refs[(revision, path)]
        return get

    def test_strip_imports(self):
        self.assertEqual(verify.strip_imports(self.OLD), verify.strip_imports(self.NEW))
        self.assertEqual(verify.strip_imports(self.NEW), b"\nnamespace CFDLean\ntheorem t : True := trivial\nend CFDLean\n")
        self.assertEqual(verify.strip_imports(b"import A"), b"")
        self.assertEqual(verify.strip_imports(b"theorem t : True := trivial\n"), b"theorem t : True := trivial\n")
        # Only the leading header is removed: a later `import` line, or a changed body, is still a difference.
        later = self.NEW + b"import CFDLean.Other\n"
        self.assertNotEqual(verify.strip_imports(later), verify.strip_imports(self.OLD))
        changed = self.NEW.replace(b"True", b"False")
        self.assertNotEqual(verify.strip_imports(changed), verify.strip_imports(self.OLD))
        self.assertNotEqual(verify.strip_imports(b"-- c\nimport A\nx\n"), b"x\n")

    def test_pinned_map_loads_and_matches_mr_table(self):
        moves = verify.load_mr_paths((verify.ROOT / verify.MR_PATHS).read_bytes())
        self.assertEqual(sum(old != new for old, new in moves.items()), 22)
        self.assertEqual(moves["CFDLean/Core/State.lean"], "CFDLean/Physics/Euler/State.lean")
        self.assertEqual(moves["CFDLean/Num/Bridge.lean"], "CFDLean/Geometry/MedianDualBridge.lean")
        self.assertTrue(all(not old.startswith(("CFDLean/Geometry/MedianDual/", "CFDLean/Time/")) or old == new
                            for old, new in moves.items()))
        verify.check_mc_n_module_paths(moves)
        for name in ["Bridge", "Mesh"]:
            wrong = dict(moves, **{f"CFDLean/Num/{name}.lean": "CFDLean/Discrete/Other.lean"})
            with self.assertRaises(ValueError):
                verify.check_mc_n_module_paths(wrong)

    def test_tampered_map_rejected(self):
        data = (verify.ROOT / verify.MR_PATHS).read_bytes()
        for tampered in [data + b" ", data.replace(b"CFDLean/Physics/Euler/State.lean", b"CFDLean/Physics/Euler/Stat.lean")]:
            with self.assertRaises(ValueError):
                verify.load_mr_paths(tampered)

    def test_malformed_map_rejected_even_if_pinned(self):
        bad_maps = [[], [{"old_path": "CFDLean/A.lean"}], [{"old_path": "A.lean", "new_path": "CFDLean/A.lean"}],
                    [{"old_path": "CFDLean/A.lean", "new_path": "CFDLean/B.lean"}] * 2,
                    [{"old_path": "CFDLean/A.lean", "new_path": "CFDLean/C.lean"},
                     {"old_path": "CFDLean/B.lean", "new_path": "CFDLean/C.lean"}],
                    [{"old_path": "CFDLean/A.lean", "new_path": "CFDLean/B.lean"},
                     {"old_path": "CFDLean/B.lean", "new_path": "CFDLean/C.lean"}]]
        original = verify.MR_PATHS_SHA256
        try:
            for entries in bad_maps:
                data = json.dumps(entries).encode()
                verify.MR_PATHS_SHA256 = verify.hashlib.sha256(data).hexdigest()
                with self.assertRaises(ValueError, msg=str(entries)):
                    verify.load_mr_paths(data)
        finally:
            verify.MR_PATHS_SHA256 = original

    def test_accepted_source_found_only_through_map(self):
        old, new = "CFDLean/Core/Flux.lean", "CFDLean/Physics/Euler/Flux.lean"
        accepted = verify.hashlib.sha256(self.OLD).hexdigest()
        refs = {("accepted", old): self.OLD}
        files = {new: self.NEW}
        check = lambda moves, files, refs=refs, sha=accepted: verify.same_or_ported_source(
            old, sha, moves, files.__getitem__, self.blob(refs), "accepted")
        self.assertTrue(check(self.MOVES, files))
        # Without the map the moved file is not found; with a wrong target it is not accepted either.
        self.assertFalse(check({}, files))
        self.assertFalse(check({old: "CFDLean/Physics/Euler/Other.lean"}, dict(files, **{
            "CFDLean/Physics/Euler/Other.lean": b"import X\ntheorem t : False := sorry\n"})))
        # A non-import change at the new path is rejected.
        self.assertFalse(check(self.MOVES, {new: self.NEW.replace(b"trivial", b"by trivial")}))
        self.assertFalse(check(self.MOVES, {new: self.NEW + b"import CFDLean.Other\n"}))
        # The accepted reference counts only if its bytes have the accepted hash; the MC-T port bytes also count.
        self.assertFalse(check(self.MOVES, files, sha="0" * 64))
        port = {(verify.MC_PORT_REVISION, old): self.OLD}
        self.assertTrue(check(self.MOVES, files, refs=port, sha="0" * 64))
        # Unmapped files keep the exact rule: same hash, or byte-identical to the port.
        self.assertTrue(verify.same_or_ported_source(old, accepted, {}, {old: self.OLD}.__getitem__,
                                                     self.blob({}), "accepted"))
        self.assertFalse(verify.same_or_ported_source(old, accepted, {}, {old: self.NEW}.__getitem__,
                                                      self.blob({}), "accepted"))

    def test_mr_sources_only_imports_changed(self):
        base = {"CFDLean/Core/Flux.lean": self.OLD, "CFDLean/Time/Step.lean": b"import CFDLean.Core.Flux\nx\n"}
        files = {"CFDLean/Physics/Euler/Flux.lean": self.NEW, "CFDLean/Time/Step.lean": b"import CFDLean.Physics.Euler.Flux\nx\n"}
        run = lambda files, moves=self.MOVES: verify.check_mr_sources(
            moves, files.__getitem__, lambda p: base[p] if p in base else (_ for _ in ()).throw(
                verify.subprocess.CalledProcessError(128, "git")), files.__contains__)
        self.assertEqual(run(files), 2)
        for bad in [dict(files, **{"CFDLean/Time/Step.lean": b"import CFDLean.Physics.Euler.Flux\ny\n"}),
                    dict(files, **{"CFDLean/Physics/Euler/Flux.lean": self.NEW.replace(b"True", b"False")}),
                    dict(files, **{"CFDLean/Core/Flux.lean": self.OLD}),
                    dict(files, **{"CFDLean/Num.lean": b""}),
                    {"CFDLean/Time/Step.lean": files["CFDLean/Time/Step.lean"]}]:
            with self.assertRaises(ValueError):
                run(bad)
        with self.assertRaises(ValueError):
            run(files, dict(self.MOVES, **{"CFDLean/Core/New.lean": "CFDLean/Physics/Euler/Flux2.lean"}))

    def test_mc_n_sources_follow_map(self):
        base = {"CFDLean/Core/Flux.lean": self.OLD, "CFDLean/Time/Step.lean": b"import CFDLean.Core.Flux\nx\n"}
        moves = dict(self.MOVES, **{"CFDLean/Num/Mesh.lean": "CFDLean/Discrete/Mesh.lean"})
        files = {"CFDLean/Physics/Euler/Flux.lean": self.NEW, "CFDLean/Time/Step.lean": b"import CFDLean.Physics.Euler.Flux\nx\n",
                 "CFDLean/Discrete/Mesh.lean": b"new MC-N file"}
        blob = lambda p: base[p] if p in base else (_ for _ in ()).throw(verify.subprocess.CalledProcessError(128, "git"))
        self.assertEqual(verify.check_mc_n_sources(sorted(files), files.__getitem__, blob, moves), 2)
        with self.assertRaises(ValueError):
            verify.check_mc_n_sources(sorted(files), files.__getitem__, blob)
        changed = dict(files, **{"CFDLean/Physics/Euler/Flux.lean": self.NEW.replace(b"trivial", b"by trivial")})
        with self.assertRaises(ValueError):
            verify.check_mc_n_sources(sorted(changed), changed.__getitem__, blob, moves)


class BurgersTests(unittest.TestCase):
    STATEMENTS = b"import Mathlib.Basic.Real.Basic\n\ndef S.Claim : Prop := True\n"
    CHALLENGE = b"import S\n\nnamespace V\ntheorem claim : S.Claim := sorry\nend V\n"

    def fixture(self):
        import hashlib

        def row(name, module, kind="theorem", direct=(), type_=""):
            return {"name": name, "kind": kind, "root": True, "unsafe": False, "axioms": ["propext"],
                    "module": module, "direct": list(direct), "type": type_}
        rows = {r["name"]: r for r in [
            row("A.flux", "M.Flux", "definition"), row("A.Law", "M.Flux", "inductive"),
            row("A.helper", "M.Flux"), row("A.result", "M.Scheme"),
            row("S.Claim", "S", "definition"),
            row("V.claim", "V", direct=["A.result", "S.Claim"], type_="∀ {I : Type u_1}, S.Claim I")]}
        pins = {"statements": "S.lean", "statements_sha256": hashlib.sha256(self.STATEMENTS).hexdigest(),
                "challenge": "C.lean", "challenge_sha256": hashlib.sha256(self.CHALLENGE).hexdigest(),
                "count": 1, "bridges": 1}
        record = {
            "results": [{"id": "B9-P", "definitions": ["A.flux", "A.Law"], "supporting": [], "declarations": []},
                        {"id": "B9-F", "definitions": [], "supporting": ["A.helper"], "declarations": ["A.result"]}],
            "modules": {"A.flux": "M.Flux", "A.Law": "M.Flux", "A.helper": "M.Flux", "A.result": "M.Scheme"},
            "trusted": {
                "statements": "S.lean", "statements_module": "S",
                "statements_sha256": pins["statements_sha256"], "bridge_module": "V",
                "comparator_challenge": "C.lean", "comparator_challenge_module": "C",
                "comparator_challenge_sha256": pins["challenge_sha256"], "comparator_config": "config.json",
                "bindings": [{"id": "B9-F", "statement": "S.Claim", "theorem": "V.claim",
                              "type": "∀ {I : Type u_1}, S.Claim I", "uses": "A.result"}]}}
        files = {"S.lean": self.STATEMENTS, "C.lean": self.CHALLENGE,
                 "config.json": json.dumps({
                     "challenge_module": "C", "solution_module": "V", "theorem_names": ["V.claim"],
                     "definition_names": [], "permitted_axioms": sorted(verify.ALLOWED)}).encode()}
        return rows, record, files, pins

    def check(self, rows, record, files, pins):
        return verify.check_burgers("B9", rows, record, "| B9-P | claim |\n| B9-F | claim |", files.__getitem__, pins)

    def rejects(self, mutations, errors=(ValueError,)):
        for mutate in mutations:
            rows, record, files, pins = self.fixture()
            mutate(rows, record, files, pins)
            with self.assertRaises(errors):
                self.check(rows, record, files, pins)

    def test_valid_map(self):
        self.assertEqual(self.check(*self.fixture()), (["A.result"], ["V.claim"]))

    def test_result_ids_modules_and_axioms(self):
        self.rejects([
            lambda rows, record, files, pins: record["results"].pop(0),
            lambda rows, record, files, pins: record["results"][0].update(definitions=[]),
            lambda rows, record, files, pins: record["modules"].update({"A.result": "M.Other"}),
            lambda rows, record, files, pins: record["modules"].pop("A.helper"),
            lambda rows, record, files, pins: rows.pop("A.result"),
            lambda rows, record, files, pins: rows["A.result"].update(axioms=["sorryAx"]),
            lambda rows, record, files, pins: rows["A.helper"].update(kind="definition"),
            lambda rows, record, files, pins: rows["A.flux"].update(module="M.Other"),
            lambda rows, record, files, pins: rows["A.result"].update(unsafe=True),
            lambda rows, record, files, pins: pins.update(count=2)], (ValueError, KeyError))

    def test_trusted_files_are_pinned_and_independent(self):
        import hashlib
        dependent = b"import Mathlib.Basic.Real.Basic\nimport CFDLean.Schemes.Burgers.Rusanov\n"
        self.rejects([
            lambda rows, record, files, pins: record["trusted"].update(statements_sha256="0" * 64),
            lambda rows, record, files, pins: record["trusted"].update(comparator_challenge_sha256="0" * 64),
            lambda rows, record, files, pins: record["trusted"].update(statements="CFDLean/Other.lean"),
            lambda rows, record, files, pins: files.update({"S.lean": self.STATEMENTS + b"-- edit\n"}),
            lambda rows, record, files, pins: files.update({"C.lean": self.CHALLENGE + b"-- edit\n"}),
            # a statement file with an implementation import is rejected even when every pin follows it
            lambda rows, record, files, pins: (
                files.update({"S.lean": dependent}),
                pins.update(statements_sha256=hashlib.sha256(dependent).hexdigest()),
                record["trusted"].update(statements_sha256=hashlib.sha256(dependent).hexdigest())),
            lambda rows, record, files, pins: self.repin(files, pins, record, "S.lean", b"def S.Claim : Prop := True\n"),
            lambda rows, record, files, pins: self.repin(
                files, pins, record, "C.lean", b"import S\nimport V\ntheorem claim : S.Claim := sorry\n"),
            lambda rows, record, files, pins: self.repin(
                files, pins, record, "C.lean", b"import S\ntheorem other : S.Claim := sorry\n")])

    @staticmethod
    def repin(files, pins, record, path, data):
        import hashlib
        digest = hashlib.sha256(data).hexdigest()
        files[path] = data
        key = "statements_sha256" if path == "S.lean" else "challenge_sha256"
        pins[key] = digest
        record["trusted"]["statements_sha256" if path == "S.lean" else "comparator_challenge_sha256"] = digest

    def test_bridge_states_its_statement_and_uses_its_theorem(self):
        def config(**changes):
            base = {"challenge_module": "C", "solution_module": "V", "theorem_names": ["V.claim"],
                    "definition_names": [], "permitted_axioms": sorted(verify.ALLOWED)}
            base.update(changes)
            return {"config.json": json.dumps(base).encode()}
        self.rejects([
            lambda rows, record, files, pins: rows["V.claim"].update(type="∀ {I : Type u_1}, S.Other I"),
            lambda rows, record, files, pins: (rows["V.claim"].update(type="∀ {I : Type u_1}, S.Claim I → False"),
                                               record["trusted"]["bindings"][0].update(
                                                   type="∀ {I : Type u_1}, S.Claim I → False")),
            lambda rows, record, files, pins: (rows["V.claim"].update(type="True"),
                                               record["trusted"]["bindings"][0].update(type="True")),
            lambda rows, record, files, pins: rows["V.claim"].update(direct=["S.Claim"]),
            lambda rows, record, files, pins: record["trusted"]["bindings"][0].update(uses="A.helper"),
            lambda rows, record, files, pins: record["trusted"]["bindings"][0].update(id="B9-P"),
            lambda rows, record, files, pins: rows["V.claim"].update(module="M.Scheme"),
            lambda rows, record, files, pins: rows["V.claim"].update(axioms=["sorryAx"]),
            lambda rows, record, files, pins: rows["S.Claim"].update(module="M.Scheme"),
            lambda rows, record, files, pins: record["trusted"].update(bindings=[]),
            lambda rows, record, files, pins: files.update(config(theorem_names=[])),
            lambda rows, record, files, pins: files.update(
                config(permitted_axioms=sorted(verify.ALLOWED) + ["sorryAx"])),
            lambda rows, record, files, pins: files.update(config(definition_names=["S.Claim"])),
            lambda rows, record, files, pins: files.update(config(solution_module="C"))])

    def test_trusted_inputs_are_pinned_and_closed(self):
        import hashlib
        kernel = b"def K.step (x : Nat) : Nat := x\n"
        statements = b"import Mathlib.Basic.Real.Basic\nimport K.Kernel\n\ndef S.Claim : Prop := True\n"

        def with_input(rows, record, files, pins, kernel=kernel, statements=statements, path="K/Kernel.lean"):
            files[path] = kernel
            pins["trusted_inputs"] = {"K.Kernel": {"path": path, "sha256": hashlib.sha256(kernel).hexdigest()}}
            self.repin(files, pins, record, "S.lean", statements)
        rows, record, files, pins = self.fixture()
        with_input(rows, record, files, pins)
        self.assertEqual(self.check(rows, record, files, pins), (["A.result"], ["V.claim"]))
        self.rejects([
            # the statements import the kernel but no input is pinned
            lambda rows, record, files, pins: self.repin(files, pins, record, "S.lean", statements),
            # the pinned kernel changed
            lambda rows, record, files, pins: (with_input(rows, record, files, pins),
                                               files.update({"K/Kernel.lean": kernel + b"-- edit\n"})),
            # the pinned kernel imports an unpinned project module
            lambda rows, record, files, pins: with_input(
                rows, record, files, pins, kernel=b"import CFDLean.Schemes.Burgers.Rusanov\n" + kernel),
            # the path of an input is not the path of its module
            lambda rows, record, files, pins: with_input(rows, record, files, pins, path="Other.lean"),
            # the statements import one more project module than the pinned inputs
            lambda rows, record, files, pins: with_input(
                rows, record, files, pins, statements=statements + b"import CFDLean.Exec.Refinement\n")])

    def test_committed_maps_follow_the_pinned_table(self):
        for milestone, pins in verify.BURGERS.items():
            record = json.loads((verify.ROOT / pins["results"]).read_text())
            self.assertEqual(record["approved_revision"], pins["approved"])
            self.assertEqual(len(record["trusted"]["bindings"]), pins["bridges"])
            self.assertEqual(sum(len(r["declarations"]) for r in record["results"]), pins["count"])
            self.assertTrue(all(r["id"].startswith(milestone + "-") for r in record["results"]))


if __name__ == "__main__":
    unittest.main()
