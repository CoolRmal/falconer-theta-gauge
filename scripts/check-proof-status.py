#!/usr/bin/env python3
"""Audit Lean's actual axiom dependencies, including the unfinished main theorem.

Run after building Solution. The independent Challenge is deliberately excluded:
its statement hole is permitted, whereas the proved theorem must be axiom-clean.
This is a development gate, not a substitute for sandboxed Comparator replay.
"""

import argparse
import json
import re
import subprocess
import sys
import tempfile
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
MAIN_THEOREM = "FalconerThetaGauge.theorem_one_one"
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
FOUNDATIONS = (
    "FalconerThetaGauge.realGauge",
    "FalconerThetaGauge.thetaGauge",
    "FalconerThetaGauge.gaugeMeasure",
    "FalconerThetaGauge.distanceSet",
    "FalconerThetaGauge.thetaGauge_zero",
    "FalconerThetaGauge.thetaGauge_pos",
    "FalconerThetaGauge.thetaGauge_le",
    "FalconerThetaGauge.measurableSet_distanceSet",
    "FalconerThetaGauge.gaugeMeasure_le_hausdorffMeasure_one",
    "FalconerThetaGauge.eventually_log_le_mul_rpow",
    "FalconerThetaGauge.summable_exp_neg_mul_nat_rpow",
    "FalconerThetaGauge.summable_filter_power",
    "FalconerThetaGauge.gain_eq_mul_rpow",
    "FalconerThetaGauge.realGauge_double_le",
    "FalconerThetaGauge.gaugeContent_pos_of_gaugeMeasure_pos",
    "FalconerThetaGauge.GaugeFrostman.exists_finite_gauge_weights",
    "FalconerThetaGauge.summable_l2_of_dyadicFrequencyShell_support",
    "FalconerThetaGauge.reconstruction_of_summable_errors_and_square_bound",
    "FalconerThetaGauge.exists_gauge_frostman_probabilityMeasure",
    "FalconerThetaGauge.exists_probabilityMeasure_finite_logCriticalEnergy",
    "FalconerThetaGauge.dyadicGaussianKernel_le_log",
    "FalconerThetaGauge.summable_rounded_filter_error",
    "FalconerThetaGauge.eventually_log_le_blockParameter_cube_mul_scale",
    "FalconerThetaGauge.absolutelyContinuous_of_l1_fourier_l2_schwartz_pairing",
    "FalconerThetaGauge.tendsto_integral_reconstructionLowpass_schwartz",
    "FalconerThetaGauge.exists_parameter_threshold",
    "FalconerThetaGauge.summable_reconstruction",
    "FalconerThetaGauge.absolutelyContinuous_of_summable_dyadic_reconstruction",
    "FalconerThetaGauge.exists_prepared_probabilityMeasures_finite_logCriticalEnergy",
    "FalconerThetaGauge.volume_distanceSet_affineMap_image_pos_iff",
    "FalconerThetaGauge.logarithmicFourierEnergy_le",
    "FalconerThetaGauge.logarithmicFourierEnergy_ne_top",
    "FalconerThetaGauge.volume_distanceSet_pos_of_crossDistanceMeasure_absolutelyContinuous",
    "FalconerThetaGauge.summable_filterMassError",
    "FalconerThetaGauge.regularDyadicPartMeasure_isRegularThrough",
    "FalconerThetaGauge.regular_decomposition",
    "FalconerThetaGauge.ae_orthogonalProjectionDensity_L2",
    "FalconerThetaGauge.compProd_orthogonalProjectionKernel_eq_withDensity",
    "FalconerThetaGauge.integral_canonical_density_level_le_charFun_tail",
    "FalconerThetaGauge.logarithmic_amplitude_layer_le",
    "FalconerThetaGauge.lintegral_orliczQuadratic_canonical_le",
    "FalconerThetaGauge.map_inverse_distance_radialProjection_withDensity_eq",
    "FalconerThetaGauge.continuousOn_radialProjection_of_separated",
    "FalconerThetaGauge.absolutelyContinuous_of_tendsto_of_uniform_orlicz",
    "FalconerThetaGauge.lintegral_orliczQuadratic_orthogonalProjectionDensity_le",
    "FalconerThetaGauge.lintegral_circle_lineLogFourierEnergy_eq",
    "FalconerThetaGauge.measure_rnDeriv_tail_le",
    "FalconerThetaGauge.weak_limit_orlicz_density",
    "FalconerThetaGauge.regularMeasureExcess_normalizedRestrict_properties",
    "FalconerThetaGauge.occupiedCellDescendants_count_le",
    "FalconerThetaGauge.regularDyadicPartMeasure_excess_properties",
    "FalconerThetaGauge.regularDyadicPart_entry_properties",
    "FalconerThetaGauge.profileSplitPoint_right_budget_gain",
    "FalconerThetaGauge.profileSplitPoint_left_budget_gain",
    "FalconerThetaGauge.profileScheduledTests_card_le_scale_sq",
    "FalconerThetaGauge.lintegral_orliczPhi_angularLineDensity_pinProjection_le",
    "FalconerThetaGauge.ae_radialProjection_orlicz_density_of_approximating_sources",
    "FalconerThetaGauge.ae_radialProjection_orlicz_density_prepared",
    "FalconerThetaGauge.exists_prepared_probabilityMeasures_uniform_radial_orlicz",
    "FalconerThetaGauge.withDensity_filter_bad_directions_of_budget",
    "FalconerThetaGauge.norm_iteratedDeriv_reciprocal_le",
    "FalconerThetaGauge.nonstationary_phase",
    "FalconerThetaGauge.nonstationary_phase_periodic",
    "FalconerThetaGauge.linear_phase",
    "FalconerThetaGauge.integral_norm_iteratedDeriv_explicitBump_le",
)
DECLARATION_NAME = re.compile(r"[A-Za-z_][A-Za-z_0-9']*(?:\.[A-Za-z_][A-Za-z_0-9']*)*")
AXIOM_REPORT = re.compile(
    r"^'(?P<name>[^']+)' (?:does not depend on any axioms|"
    r"depends on axioms: \[(?P<axioms>[^\]]*)\])$"
)


def audit():
    config = json.loads((ROOT / "comparator.json").read_text(encoding="utf-8"))
    if not isinstance(config, dict):
        raise ValueError("comparator.json must contain one JSON object")
    targets = config.get("theorem_names")
    if not isinstance(targets, list) or MAIN_THEOREM not in targets:
        raise ValueError(f"comparator.json must select {MAIN_THEOREM}")
    if not all(isinstance(name, str) and DECLARATION_NAME.fullmatch(name) for name in targets):
        raise ValueError("comparator.json contains an invalid theorem name")
    axioms = config.get("permitted_axioms")
    if not isinstance(axioms, list) or not all(isinstance(name, str) for name in axioms):
        raise ValueError("comparator.json must contain a list of permitted axiom names")
    if set(axioms) != STANDARD_AXIOMS:
        raise ValueError("comparator.json must permit exactly the three standard Lean axioms")
    declarations = list(dict.fromkeys([*FOUNDATIONS, *targets]))

    # Lean emits structured diagnostic messages. Parse these rather than looking
    # for source words: a proof can hide sorryAx in a transitive dependency.
    with tempfile.TemporaryDirectory(prefix="theta-gauge-proof-status-") as directory:
        source = Path(directory) / "Audit.lean"
        source.write_text(
            "import Solution\n" + "".join(f"#print axioms {name}\n" for name in declarations),
            encoding="utf-8",
        )
        process = subprocess.run(
            ["lake", "env", "lean", "--json", str(source)],
            cwd=ROOT,
            capture_output=True,
            text=True,
            timeout=180,
            check=False,
        )

    reports = {}
    diagnostics = []
    for line in process.stdout.splitlines():
        if not line.strip():
            continue
        try:
            message = json.loads(line)
        except json.JSONDecodeError as error:
            raise ValueError(f"Lean emitted an unrecognized diagnostic: {line}") from error
        if not isinstance(message, dict):
            raise ValueError("Lean emitted a non-object diagnostic")
        data = message.get("data", "")
        if not isinstance(data, str):
            raise ValueError("Lean emitted a non-text diagnostic")
        if message.get("severity") == "error":
            diagnostics.append(data)
        match = AXIOM_REPORT.fullmatch(data.strip())
        if match is None:
            continue
        name = match.group("name")
        if name in reports:
            raise ValueError(f"Lean emitted duplicate axiom reports for {name}")
        axioms = sorted(
            axiom.strip() for axiom in (match.group("axioms") or "").split(",") if axiom.strip()
        )
        reports[name] = {
            "axioms": axioms,
            "forbidden_axioms": sorted(set(axioms) - STANDARD_AXIOMS),
        }
    if process.returncode != 0 or diagnostics:
        details = "\n".join(diagnostics) or process.stderr.strip() or process.stdout.strip()
        raise ValueError(f"Lean could not complete the axiom audit (exit {process.returncode}): {details}")
    missing = set(declarations) - reports.keys()
    unexpected = reports.keys() - set(declarations)
    if missing or unexpected:
        raise ValueError(f"Incomplete axiom audit; missing={sorted(missing)}, unexpected={sorted(unexpected)}")

    failures = {name: report for name, report in reports.items() if report["forbidden_axioms"]}
    return {
        "status": "fail" if failures else "pass",
        "method": "Lean #print axioms on declarations imported through Solution",
        "toolchain": (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip(),
        "permitted_axioms": sorted(STANDARD_AXIOMS),
        "main_theorem": MAIN_THEOREM,
        "challenge_imported": False,
        "declarations": reports,
        "scope_note": "Axiom-dependency audit only; full sandboxed Comparator verification is separate.",
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", action="store_true", help="Emit the structured audit report")
    arguments = parser.parse_args()
    try:
        report = audit()
    except (OSError, ValueError, subprocess.TimeoutExpired) as error:
        if arguments.json:
            print(json.dumps({"status": "error", "error": str(error)}, indent=2))
        else:
            print(f"Proof-status audit failed: {error}", file=sys.stderr)
        return 2
    if arguments.json:
        print(json.dumps(report, indent=2))
    else:
        for name, declaration in report["declarations"].items():
            forbidden = declaration["forbidden_axioms"]
            if forbidden:
                print(f"FAIL {name}: forbidden axioms {', '.join(forbidden)}")
            else:
                print(f"PASS {name}: standard axioms only")
        if report["status"] == "fail":
            print("The proof development is incomplete; the Challenge's deliberate hole is excluded.")
        else:
            print("Axiom dependencies pass; sandboxed Comparator remains the independent proof check.")
    return 1 if report["status"] == "fail" else 0


if __name__ == "__main__":
    sys.exit(main())
