"""Pure acceptance rules for the current Lean proof repository."""

import re
from pathlib import Path

MAIN_TARGETS = (
    "HierarchicalLaminates.composite_counterexample",
    "HierarchicalLaminates.two_well_energy_gap",
)
SUPPORTING_TARGETS = (
    # Weak trials, nonlinear energy continuity and the period-2π statement.
    "HierarchicalLaminates.TwoWell.quasiconvex_h1_trial_inequality32_weak",
    "HierarchicalLaminates.TwoWell.twoWellIntegral_continuous",
    "HierarchicalLaminates.two_well_energy_gap_manuscript",
    # Actual centered minimizers, stream potentials and the exact paired trial.
    "HierarchicalLaminates.Periodic.gradientSpace_existsUnique_potential",
    "HierarchicalLaminates.Periodic.sobolevCellEnergy_isLeast",
    "HierarchicalLaminates.Periodic.cellPotential_unique",
    "HierarchicalLaminates.GClosure.dimensionPeriodCellEnergy_isLeast",
    "HierarchicalLaminates.TwoWell.streamPotential_representation",
    "HierarchicalLaminates.TwoWell.exactPair_selected_energy",
    "HierarchicalLaminates.TwoWell.quasiconvex_upper_via_exact_h1",
    "HierarchicalLaminates.TwoWell.quantitative_gap_via_exact_h1",
    # Parameter-dependent physical response and its fifth-order expansion.
    "HierarchicalLaminates.Contrast.physicalGap_asymptotic",
    "HierarchicalLaminates.Contrast.physicalGap_eventually_positive",
    "HierarchicalLaminates.Contrast.effectiveMatrix_eq_materialTensor",
    "HierarchicalLaminates.Contrast.meanResponse_tail_five",
    # Constitutive algebra, rational data and closure topology.
    "HierarchicalLaminates.Binary.binaryIndicator_mean_half",
    "HierarchicalLaminates.parameterSpace_inv_mem_of_isUnit",
    "HierarchicalLaminates.Lamination.laminateClosure_mem_materialFamily",
    "HierarchicalLaminates.Corrector.meanResponseMatrix_isHermitian",
    "HierarchicalLaminates.Corrector.smooth_effectiveMatrix_eq_materialTensor",
    "HierarchicalLaminates.quadratic_branches_rational",
    "HierarchicalLaminates.dimension_constituents_rational",
    "HierarchicalLaminates.dimension_constituent_energy_order",
    "HierarchicalLaminates.Lamination.matrix_mem_closure_iff_operator",
    "HierarchicalLaminates.Lamination.matrix_mem_closure_iff_frobenius",
    # Joint smoothness, including the variable-contrast fields.
    "HierarchicalLaminates.Fourier.reducedResponse_smooth",
    "HierarchicalLaminates.Corrector.smoothCorrector_potential_smooth",
    "HierarchicalLaminates.Corrector.smoothCorrector_gradient_smooth",
    "HierarchicalLaminates.Contrast.response_smooth",
    "HierarchicalLaminates.Contrast.potential_smooth",
    "HierarchicalLaminates.Contrast.gradient_smooth",
    "HierarchicalLaminates.Contrast.meanResponseMatrix_isHermitian",
    # The full real-valued minorant classes and full 32-component envelopes.
    "HierarchicalLaminates.TwoWell.PeriodicQuasiconvex.rankOneConvex_of_le_continuous",
    "HierarchicalLaminates.TwoWell.twoWell_periodicQuasiconvex_rankOneConvex",
    "HierarchicalLaminates.TwoWell.quasiconvexEnvelope_isGreatest",
    "HierarchicalLaminates.TwoWell.twoWell_quasiconvexEnvelope_isGreatest",
    "HierarchicalLaminates.TwoWell.twoWell_quasiconvexEnvelope_le_rankOneEnvelope",
    "HierarchicalLaminates.TwoWell.twoWell_periodicQuasiconvex32_rankOneConvex32",
    "HierarchicalLaminates.TwoWell.twoWell_quasiconvexEnvelope32_isGreatest",
    "HierarchicalLaminates.TwoWell.twoWell_quasiconvexEnvelope32_le_rankOneEnvelope32",
    # Smooth trials and Jensen equivalence under continuity hypotheses.
    "HierarchicalLaminates.TwoWell.smoothGradients_closure_eq",
    "HierarchicalLaminates.TwoWell.smoothPeriodicQuasiconvex_iff",
    "HierarchicalLaminates.TwoWell.twoWell32_smoothPeriodicQuasiconvex_iff",
    "HierarchicalLaminates.TwoWell.exists_smooth_trial32_lt",
)
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
REVIEW_KINDS = ("mathematical", "statement", "code")
REQUIRED_DEPENDENCIES = {
    MAIN_TARGETS[0]: (
        "HierarchicalLaminates.GClosure.all_m_strict_inclusion",
        "HierarchicalLaminates.GClosure.all_m_counterexample_manuscript",
        "HierarchicalLaminates.GClosure.genericPeriodCellEnergy_transport",
        "HierarchicalLaminates.GClosure.genericCellEnergy_extend_actual",
        "HierarchicalLaminates.GClosure.actual_layer_realization",
        "HierarchicalLaminates.half_fraction_counterexample",
    ),
    MAIN_TARGETS[1]: (
        "HierarchicalLaminates.TwoWell.minorant_rankOneConvex",
        "HierarchicalLaminates.TwoWell.minorant_lower_bound",
        "HierarchicalLaminates.TwoWell.periodic_minorant_upper",
        "HierarchicalLaminates.TwoWell.dual_isLayerTensor",
        "HierarchicalLaminates.half_fraction_counterexample",
    ),
    SUPPORTING_TARGETS[0]: (
        "HierarchicalLaminates.TwoWell.twoWellIntegral_continuous",
        "HierarchicalLaminates.Composition.regularGradients_closure_eq",
        "HierarchicalLaminates.TwoWell.weakTrial32_components",
    ),
    SUPPORTING_TARGETS[1]: (
        "HierarchicalLaminates.TwoWell.twoWellDensity_continuous",
        "HierarchicalLaminates.TwoWell.quadraticDensity_continuous",
    ),
    "HierarchicalLaminates.two_well_energy_gap_manuscript": (
        "HierarchicalLaminates.two_well_energy_gap",
        "HierarchicalLaminates.TwoWell.periodQuasiconvexEnvelope32_eq",
        "HierarchicalLaminates.TwoWell.periodQuasiconvex32_iff",
    ),
    "HierarchicalLaminates.Periodic.sobolevCellEnergy_isLeast": (
        "HierarchicalLaminates.Periodic.gradientSpace_exact_potential",
        "HierarchicalLaminates.Periodic.weak_poincare",
        "HierarchicalLaminates.Periodic.cellPotential_minimizes",
    ),
    "HierarchicalLaminates.GClosure.dimensionPeriodCellEnergy_isLeast": (
        "HierarchicalLaminates.GClosure.dimensionPeriodCellEnergy_attained",
        "HierarchicalLaminates.Periodic.cellPotential_energy",
        "HierarchicalLaminates.GClosure.genericPeriodFieldEnergy_pull",
    ),
    "HierarchicalLaminates.TwoWell.quantitative_gap_via_exact_h1": (
        "HierarchicalLaminates.TwoWell.streamPotential_representation",
        "HierarchicalLaminates.TwoWell.exactPairPotential32_energy_upper",
        "HierarchicalLaminates.TwoWell.quasiconvex_h1_trial_inequality32_weak",
        "HierarchicalLaminates.TwoWell.minorant_lower_bound",
    ),
    "HierarchicalLaminates.Contrast.physicalGap_asymptotic": (
        "HierarchicalLaminates.Contrast.physicalGap_eq_sequence",
        "HierarchicalLaminates.Contrast.sequenceLoading_first_five",
        "HierarchicalLaminates.Contrast.solution_equation",
        "HierarchicalLaminates.loading_coefficient_five",
    ),
    "HierarchicalLaminates.TwoWell.twoWell_quasiconvexEnvelope_isGreatest": (
        "HierarchicalLaminates.TwoWell.quasiconvexEnvelope_isGreatest",
        "HierarchicalLaminates.TwoWell.quasiconvexEnvelope_eq_nonnegative_sup",
    ),
    "HierarchicalLaminates.TwoWell.twoWell_periodicQuasiconvex_rankOneConvex": (
        "HierarchicalLaminates.TwoWell.PeriodicQuasiconvex.rankOneConvex_of_le_continuous",
    ),
    "HierarchicalLaminates.TwoWell.twoWell32_smoothPeriodicQuasiconvex_iff": (
        "HierarchicalLaminates.TwoWell.smoothPeriodicQuasiconvex_iff",
        "HierarchicalLaminates.TwoWell.smoothGradients_closure_eq",
        "HierarchicalLaminates.TwoWell.twoWellIntegral_continuous",
    ),
    "HierarchicalLaminates.TwoWell.exists_smooth_trial32_lt": (
        "HierarchicalLaminates.TwoWell.smoothGradients_closure_eq",
        "HierarchicalLaminates.TwoWell.selectedPairEnergy_exact_fields",
        "HierarchicalLaminates.TwoWell.exactCellFlux_rotation_admissible",
    ),
}
SNAPSHOT_KEYS = (
    "main_targets", "supporting_targets", "source_sha256",
    "configuration_sha256", "dependency_lock_sha256",
)


def lean_imports(source):
    """Parse unquoted Lean imports outside nested comments and strings.

    Unsupported import syntax raises ValueError.
    """
    out, i, depth, string = [], 0, 0, False
    while i < len(source):
        pair = source[i:i + 2]
        char = source[i]
        if depth:
            if pair == "/-":
                depth += 1
                i += 2
            elif pair == "-/":
                depth -= 1
                i += 2
            else:
                out.append("\n" if char == "\n" else " ")
                i += 1
        elif string:
            if char == "\\":
                out.extend("  ")
                i += 2
            elif char == '"':
                string = False
                out.append(" ")
                i += 1
            else:
                out.append("\n" if char == "\n" else " ")
                i += 1
        elif pair == "/-":
            depth = 1
            out.extend("  ")
            i += 2
        elif pair == "--":
            end = source.find("\n", i)
            if end < 0:
                break
            out.extend(" " * (end - i))
            i = end
        elif char == '"':
            string = True
            out.append(" ")
            i += 1
        else:
            out.append(char)
            i += 1
    imports = []
    for line in "".join(out).splitlines():
        found = re.match(r"^\s*(?:public\s+)?import\s+(.+?)\s*$", line)
        if found:
            for name in found[1].split():
                if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_'.]*", name):
                    raise ValueError("unsupported import syntax: " + line.strip())
                imports.append(name)
    return imports



def import_graph_errors(modules, root):
    """Check imports against the project tree and pinned Mathlib/Lean modules."""
    root = Path(root).resolve()
    canonical = root / "HierarchicalLaminates"
    seen, errors = set(), []

    def visit(module):
        if module in seen:
            return
        seen.add(module)
        if module == "HierarchicalLaminates":
            path = root / "HierarchicalLaminates.lean"
        elif module.startswith("HierarchicalLaminates."):
            path = root / (module.replace(".", "/") + ".lean")
            if not path.resolve().is_relative_to(canonical):
                errors.append("project source outside canonical tree: " + module)
                return
        elif module in {"Mathlib", "Lean"} or module.startswith(("Mathlib.", "Lean.")):
            return
        else:
            errors.append("noncanonical import: " + module)
            return
        if not path.is_file():
            errors.append("missing project module: " + module)
            return
        try:
            imports = lean_imports(path.read_text())
        except ValueError as exc:
            errors.append(module + ": " + str(exc))
            return
        for imported in imports:
            visit(imported)

    for module in ["HierarchicalLaminates", *modules]:
        visit(module)
    return sorted(set(errors))


def render_audit(modules):
    """Audit project theorems and record their kernel proof dependencies."""
    # Include declarations written directly in the aggregate module.
    audited_modules = dict.fromkeys(("HierarchicalLaminates", *modules))
    return "\n".join("import " + module for module in audited_modules) + r"""
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Lean.Elab.Command

open Lean in
run_cmd do
  let env ← getEnv
  for (name, info) in env.constants.toList do
    let sourceModule := match env.getModuleIdxFor? name with
      | some idx => env.allImportedModuleNames[idx.toNat]!
      | none => Name.anonymous
    let inProjectModule := sourceModule.toString == "HierarchicalLaminates" ||
      sourceModule.toString.startsWith "HierarchicalLaminates."
    if inProjectModule || name.toString.startsWith "HierarchicalLaminates." ||
        name.toString.startsWith "_private.HierarchicalLaminates." then
      let deps := info.getUsedConstantsAsSet.toList.map Lean.Name.toString
      logInfo m!"LEAN_GRAPH {(Lean.Json.mkObj [
        ("name", toJson name.toString), ("module", toJson sourceModule.toString),
        ("deps", toJson deps)]).compress}"
      if info.isTheorem then
        let axioms ← Lean.collectAxioms name
        logInfo m!"LEAN_AUDIT {(Lean.Json.mkObj [
          ("name", toJson name.toString), ("module", toJson sourceModule.toString),
          ("axioms", toJson (axioms.map Lean.Name.toString))]).compress}"
"""


def reachable(name, graph):
    seen, todo = set(), [name]
    while todo:
        item = todo.pop()
        if item in seen:
            continue
        seen.add(item)
        todo.extend(dep for dep in graph.get(item, []) if dep in graph)
    return sorted(seen)


def route_dependencies_match(dependencies, requirements=REQUIRED_DEPENDENCIES):
    return bool(requirements) and all(
        set(needed) <= set(dependencies.get(target, ()))
        for target, needed in requirements.items()
    )


def review_matches(review, snapshot):
    """Require a literal approval and every field of the exact current snapshot."""
    if not isinstance(review, dict) or not isinstance(snapshot, dict):
        return False
    return (
        review.get("approved") is True
        and all(key in review and key in snapshot for key in SNAPSHOT_KEYS)
        and all(review[key] == snapshot[key] for key in SNAPSHOT_KEYS)
    )


def proof_checks_pass(report):
    required_flags = (
        "environment_passed", "tests_passed", "build_passed",
        "axiom_audit_passed", "import_graph_passed",
        "route_dependencies_passed", "snapshots_stable",
    )
    targets = (*MAIN_TARGETS, *SUPPORTING_TARGETS)
    return (
        all(report.get(flag) is True for flag in required_flags)
        and report.get("main_targets") == list(MAIN_TARGETS)
        and report.get("supporting_targets") == list(SUPPORTING_TARGETS)
        and set(report.get("targets_present", {})) == set(targets)
        and all(value is True for value in report["targets_present"].values())
        and not report.get("unexpected_axioms")
        and not report.get("import_graph_errors")
    )


def certification_passes(report):
    return (
        proof_checks_pass(report)
        and set(report.get("reviews_match", {})) == set(REVIEW_KINDS)
        and all(value is True for value in report["reviews_match"].values())
    )
