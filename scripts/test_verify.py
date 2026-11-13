import json
import unittest
from verify import parse_axioms, check_promises, check_result_ids, check_inherited


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
        contract = {"results": [{"id": "M2-J", "stage": "M2a", "declarations": ["A.accepted"]}]}
        evidence = {"declarations": {"A.accepted": {"type": "the approved proposition"}}}
        rows = evidence["declarations"]
        self.assertEqual(len(check_inherited(rows, contract, contract, evidence)), 1)
        substituted = {"results": [{"id": "M2-J", "stage": "M2a", "declarations": ["A.other"]}]}
        with self.assertRaises(ValueError):
            check_inherited(rows, substituted, contract, evidence)
        with self.assertRaises(ValueError):
            check_inherited({"A.accepted": {"type": "a weaker proposition"}}, contract, contract, evidence)

    def test_empty_or_malformed_inventory(self):
        for output in ["", "CFDLEAN_DECL {bad}"]:
            with self.assertRaises(ValueError):
                parse_axioms(output)


if __name__ == "__main__":
    unittest.main()
