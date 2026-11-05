"""Adversarial independent replay of the bounded M3/eq.(11) finite contract."""

from copy import deepcopy
from fractions import Fraction as Q
from itertools import permutations
import os
from pathlib import Path
import sys
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT / "oracles/python"))
import c4_finite_cylinder_overlap as c


class CylinderVerifierTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.packet = c.reference_packet()
        cls.report = c.verify_packet(cls.packet)

    def refused(self, packet, text=None):
        with self.assertRaises(c.InvalidCertificate) as failure:
            c.verify_packet(packet)
        if text:
            self.assertIn(text,str(failure.exception))

    def test_independent_calibration_has_complete_finite_scope(self):
        self.assertEqual(self.report["verified_occurrences"],1002)
        self.assertEqual(self.report["verified_slices"],283)
        self.assertEqual(self.report["verified_pair_bounds"],18)
        self.assertFalse(self.report["equation_11_certificate"])
        self.assertEqual(c.verify_packet(c.parse_packet(c.serialize_packet(self.packet))),self.report)

    def test_chart_algebra_and_pisot_hypotheses_are_bound_to_the_incidence(self):
        for sigma in c.CONTROLS:
            matrix = tuple(tuple(w.count(str(a)) for w in sigma) for a in range(3))
            self.assertEqual(matrix,c.M)
        self.assertTrue(all(x > 0 for row in c.matrix_power(2) for x in row))
        self.assertTrue(all(c.polynomial_at(Q(x)) != 0 for x in (-2,-1,1,2)))
        aa,bb,cc = -1,-2,-2
        self.assertEqual(aa*aa*bb*bb - 4*bb**3 - 4*aa**3*cc - 27*cc*cc + 18*aa*bb*cc,-152)
        ell = (c.ONE,c.BETA,c.C)
        w = ((c.ONE,c.scale(c.A,-1),c.ZERO),(c.ZERO,c.scale(c.INV_BETA,-1),c.ONE))
        for col in range(3):
            actual = c.ZERO
            for row in range(3): actual = c.add(actual,c.scale(ell[row],c.M[row][col]))
            self.assertEqual(actual,c.mul(c.BETA,ell[col]))
            for row in range(2):
                wm = c.ZERO
                for index in range(3): wm = c.add(wm,c.scale(w[row][index],c.M[index][col]))
                bw = c.add(c.mul(c.B[row][0],w[0][col]),c.mul(c.B[row][1],w[1][col]))
                self.assertEqual(wm,bw)
        phi = (ell,)+w
        determinant = c.ZERO
        for p in permutations(range(3)):
            parity = sum(p[i] > p[j] for i in range(3) for j in range(i+1,3))
            term = c.ONE
            for row in range(3): term = c.mul(term,phi[row][p[row]])
            determinant = c.add(determinant,c.scale(term,(-1)**parity))
        self.assertEqual(c.scale(determinant,-1),c.KAPPA)
        self.assertEqual(c.KAPPA,(Q(0),Q(4),Q(-1)))
        self.assertGreater(c.sign_at_beta(c.KAPPA),0)

    @unittest.skipUnless(os.environ.get("PSC_CYLINDER_NATIVE_OUTPUT"),
                         "native output absent: finite native parity not credited")
    def test_full_native_certificate_independently_verified(self):
        native = c.parse_packet(Path(os.environ["PSC_CYLINDER_NATIVE_OUTPUT"]).read_text())
        report = c.verify_packet(native)
        self.assertEqual(report["verified_occurrences"],1002)
        self.assertEqual(report["verified_slices"],283)
        self.assertEqual(report["verified_pair_bounds"],18)
        self.assertFalse(report["equation_11_certificate"])
        # Occurrences and their two residue levels must agree independently;
        # sound native boxes need not equal the oracle's separate enclosures.
        self.assertEqual({k:v[:4] for k,v in native["occurrences"].items()},
                         {k:v[:4] for k,v in self.packet["occurrences"].items()})

    def test_missing_occurrence_refuses_even_if_summed_bound_unchanged(self):
        packet = deepcopy(self.packet)
        packet["occurrences"].pop((0,2,0,0))
        self.refused(packet,"missing literal occurrence")

    def test_duplicate_occurrence_refuses_in_parser(self):
        text = c.serialize_packet(self.packet)
        occurrence = next(x for x in text.splitlines() if x.startswith("occurrence "))
        with self.assertRaisesRegex(c.InvalidCertificate,"duplicate"):
            c.parse_packet(text+occurrence+"\n")

    def test_same_count_relabeling_is_not_complete_occurrence_evidence(self):
        packet = deepcopy(self.packet)
        key = (0,2,0,0)
        value = list(packet["occurrences"][key])
        value[1] = (1,0,0)
        packet["occurrences"][key] = tuple(value)
        self.refused(packet,"relabeled literal occurrence")

    def test_extra_occurrence_refuses(self):
        packet = deepcopy(self.packet)
        packet["occurrences"][0,2,0,100] = packet["occurrences"][0,2,0,0]
        self.refused(packet,"extra occurrences")

    def test_coordinatewise_residue_is_not_the_matrix_quotient(self):
        packet = deepcopy(self.packet)
        key = next(k for k,v in packet["occurrences"].items()
                   if tuple(x % (2**k[1]) for x in v[1]) != v[2])
        value = list(packet["occurrences"][key])
        value[2] = tuple(x % (2**key[1]) for x in value[1])
        packet["occurrences"][key] = tuple(value)
        self.refused(packet,"incorrect residue class")

    def test_coordinatewise_key_reduction_is_not_the_bonding_map(self):
        packet = deepcopy(self.packet)
        key = next(k for k,v in packet["occurrences"].items() if k[1] > 2
                   and tuple(x % (2**(k[1]-2)) for x in v[2]) != v[3])
        value = list(packet["occurrences"][key])
        value[3] = tuple(x % (2**(key[1]-2)) for x in value[2])
        packet["occurrences"][key] = tuple(value)
        self.refused(packet,"incorrect residue refinement")

    def test_exact_quotient_orders_and_four_to_one_refinement(self):
        for q in c.DEPTHS:
            reps = c.quotient_representatives(q)
            self.assertEqual(len(reps),2**q)
            counts = {}
            for representative in reps.values():
                parent = c.residue_key(q-2,representative)
                counts[parent] = counts.get(parent,0)+1
            self.assertEqual(set(counts.values()),{4})

    def test_actual_fine_supports_refine_the_correct_coarse_letter_slice(self):
        for (fixture,q,source,position),(letter,prefix,residue,parent,rect) in self.packet["occurrences"].items():
            if q > 2:
                self.assertIn((fixture,q-2,letter)+parent,self.packet["slices"])

    def test_small_radius_is_not_a_certified_outer_enclosure(self):
        packet = deepcopy(self.packet)
        chart = list(packet["charts"][0]); chart[2] = 1
        packet["charts"][0] = tuple(chart)
        self.refused(packet,"invalid invariant outer radius")

    def test_explicit_common_tail_constants_are_rationally_certified(self):
        for fixture,sigma in enumerate(c.CONTROLS):
            result = c.validate_chart(sigma,self.packet["charts"][fixture])
            self.assertLess(Q(result["rho_upper"]),Q(7,8))
            self.assertLess(Q(result["digit_upper"]),Q(5))
            self.assertEqual(Q(7,8)*40+5,40)

    def test_noncontracting_matrix_power_cannot_certify_the_tail(self):
        packet = deepcopy(self.packet)
        chart = list(packet["charts"][0]); chart[3] = 2
        packet["charts"][0] = tuple(chart)
        self.refused(packet,"contracting block")

    def test_sample_point_box_omits_the_certified_tail(self):
        packet = deepcopy(self.packet)
        key = (0,2,0,0)
        value = list(packet["occurrences"][key]); value[4] = (Q(0),)*4
        packet["occurrences"][key] = tuple(value)
        self.refused(packet,"affine corner")

    def test_slice_hull_must_contain_every_occurrence(self):
        packet = deepcopy(self.packet)
        packet["slices"][0,2,0,0,0,0] = (Q(0),)*4
        self.refused(packet,"complete occurrence coverage")

    def test_missing_zero_slice_is_different_from_missing_nonempty_slice(self):
        packet = deepcopy(self.packet)
        packet["slices"].pop((0,2,2,0,2,2))
        self.refused(packet,"complete occurrence coverage")

    def test_reversed_box_refuses(self):
        packet = deepcopy(self.packet)
        key = (0,2,0,0)
        value = list(packet["occurrences"][key]); value[4] = (Q(1),Q(0),Q(0),Q(1))
        packet["occurrences"][key] = tuple(value)
        self.refused(packet,"reversed rectangle")

    def test_wrong_covolume_cannot_strengthen_the_density_side(self):
        packet = deepcopy(self.packet)
        chart = list(packet["charts"][0]); chart[4] *= 2; chart[5] *= 2
        packet["charts"][0] = tuple(chart)
        self.refused(packet,"mismatched chart covolume")

    def test_wrong_haar_weight_refuses(self):
        packet = deepcopy(self.packet)
        key = (0,2,0,1)
        raw,upper = packet["uppers"][key]
        packet["uppers"][key] = raw,raw/16
        self.assertNotEqual(raw/16,upper)
        self.refused(packet,"Haar-weighted")

    def test_period_and_unsupported_substitutions_refuse(self):
        for fixture in ((c.CONTROLS[0],1),(("10","102","211"),2)):
            packet = deepcopy(self.packet); packet["fixtures"][0] = fixture
            self.refused(packet,"substitution/period mismatch")

    def test_invalid_perron_data_refuse(self):
        packet = deepcopy(self.packet)
        chart = list(packet["charts"][0]); chart[0] = Q(23,10); chart[1] = Q(24,10)
        packet["charts"][0] = tuple(chart)
        self.refused(packet,"wrong Perron root")

    def test_density_label_is_not_density_evidence(self):
        packet = deepcopy(self.packet); packet["status"][0] = "strict_density_1/100"
        self.refused(packet,"unsupported density claim")
        with self.assertRaisesRegex(c.InvalidCertificate,"unknown record"):
            c.parse_packet(c.serialize_packet(self.packet)+"density 0 1/100\n")
        packet = deepcopy(self.packet); packet["assume_strict"] = True
        self.refused(packet,"unsupported certificate fields")

    def test_zero_upper_plus_arbitrary_positive_density_is_not_a_contradiction(self):
        self.assertEqual(self.packet["uppers"][0,2,0,2][1],0)
        with self.assertRaisesRegex(c.InvalidCertificate,"state count"):
            c.compare_equation_11(self.packet,0,2,(0,2),[],1,Q(1,100))

    def test_reproducible_cli_density_refusal_survives_python_optimization(self):
        density_path = ROOT / "evidence/c4-finite-cylinder-overlap-2026-11-04/rejected-empty-strict-component.json"
        c.parse_density_input(density_path.read_text())  # Valid syntax, false mathematical premise.
        with tempfile.TemporaryDirectory() as directory:
            packet_path = Path(directory) / "packet.txt"
            packet_path.write_text(c.serialize_packet(self.packet))
            result = subprocess.run([sys.executable,"-O",str(ROOT / "oracles/python/c4_finite_cylinder_overlap.py"),
                                     str(packet_path),"--density-input",str(density_path)],
                                    text=True,capture_output=True,timeout=30)
        self.assertNotEqual(result.returncode,0)
        self.assertEqual(result.stdout,"")
        self.assertIn("strict state count cap",result.stderr)

    def test_false_strict_state_and_omitted_child_refuse(self):
        for states in ((('0','0'),),(('01','10'),),(('012','120'),)):
            with self.assertRaises(c.InvalidCertificate):
                c.literal_strict_system(c.CONTROLS[0],states)
        sigma = ("012","120","201")
        with self.assertRaisesRegex(c.InvalidCertificate,"omitted literal child"):
            c.literal_strict_system(sigma,(("012","120"),))

    def test_actual_strict_non_pisot_control_only_checks_density_combinatorics(self):
        sigma = ("012","120","201")
        states,children = c.literal_strict_system(sigma,(("012","120"),("120","201"),("201","012")))
        for pair in ((0,1),(0,2),(1,2)):
            c.all_column_pair_cover(states,children,pair,1)
        # Here beta=3 and every physical state length=3, literally, so
        # 1/(beta^1 Lmax)=1/9. This singular non-Pisot matrix cannot enter M3.
        self.assertEqual(Q(1,3*3),Q(1,9))
        with self.assertRaisesRegex(c.InvalidCertificate,"unsupported geometric"):
            c.words(sigma,2)

    def test_phase_sensitive_cover_refuses_wrong_phase_without_inference(self):
        # Synthetic matrix-only unit test; never a literal PIP component.
        states = (("01","10"),("02","20"))
        children = ((1,1),(0,0))
        for depth in range(5):
            with self.assertRaisesRegex(c.InvalidCertificate,"common-depth cover"):
                c.all_column_pair_cover(states,children,(0,1),depth)

    def test_mismatched_density_units_refuse_before_claim_admission(self):
        with self.assertRaisesRegex(c.InvalidCertificate,"normalization"):
            c.verify_normalized_density(self.packet,0,(0,1),[],1,Q(1,100),"per_letter")

    def test_strict_inequality_is_not_nonstrict(self):
        with self.assertRaisesRegex(c.InvalidCertificate,"strict inequality"):
            c.strict_arithmetic_gap(Q(1),Q(2),Q(1,2))
        with self.assertRaisesRegex(c.InvalidCertificate,"positive lower"):
            c.strict_arithmetic_gap(Q(0),Q(2),Q(0))
        self.assertEqual(c.strict_arithmetic_gap(Q(0),Q(1),Q(1,100)),Q(1,100))
        with self.assertRaisesRegex(c.InvalidCertificate,"exact rational"):
            c.strict_arithmetic_gap(0.0,Q(1),Q(1,100))
        # The last scalar fact still needs all word/density premises; previous
        # test covers the real false-certificate path with U=0.

    def test_control_separation_and_persistent_zero_residue(self):
        for q in c.DEPTHS:
            self.assertEqual(self.packet["uppers"][0,q,0,2][1],0)
            self.assertEqual(self.packet["uppers"][0,q,1,2][1],0)
            self.assertGreater(self.packet["uppers"][0,q,0,1][1],0)
            for fixture in (0,1):
                for source in (0,1):
                    letter,prefix,key,parent,_ = self.packet["occurrences"][fixture,q,source,0]
                    self.assertEqual((letter,prefix,key),(source,(0,0,0),(0,0,0)))

    def test_same_incidence_word_order_changes_the_cylinder_support(self):
        original = {k[2:]:v[2] for k,v in self.packet["occurrences"].items() if k[:2] == (0,2)}
        changed = {k[2:]:v[2] for k,v in self.packet["occurrences"].items() if k[:2] == (1,2)}
        self.assertNotEqual(original,changed)
        self.assertGreater(self.packet["uppers"][1,2,0,2][1],0)

    def test_hull_upper_bounds_need_not_be_monotone_like_exact_m3_sets(self):
        self.assertGreater(self.packet["uppers"][1,6,0,1][1],self.packet["uppers"][1,4,0,1][1])
        # A safe nonincreasing scalar bound is min of independently valid U's.
        self.assertEqual(min(self.packet["uppers"][1,q,0,1][1] for q in c.DEPTHS),
                         self.packet["uppers"][1,4,0,1][1])

    def test_current_positive_hulls_fail_the_necessary_density_range(self):
        self.assertGreater(c.sign_at_beta(c.add(c.BETA,c.scale(c.ONE,-2))),0)
        self.assertGreater(c.sign_at_beta(c.add(c.C,c.scale(c.ONE,-1))),0)
        self.assertGreater(c.sign_at_beta(c.add(c.scale(c.ONE,4),c.scale(c.KAPPA,-1))),0)
        # Every noncoincident balanced factor has >=2 letters, each with ell>=1,
        # so its count density <=1/2 and kappa*delta_lower<2. This is a
        # necessary screen, not a strict-component or positive-density claim.
        for raw,upper in self.packet["uppers"].values():
            self.assertTrue(upper == 0 or upper > 2)
        self.assertFalse(self.report["equation_11_certificate"])

    def test_false_coincidence_and_missing_control_witness_refuse(self):
        packet = deepcopy(self.packet)
        witness = list(packet["sc"][0,0,1]); witness[1] = 0
        packet["sc"][0,0,1] = tuple(witness)
        self.refused(packet,"coincidence")
        packet = deepcopy(self.packet); packet["sc"].pop((1,0,2))
        self.refused(packet,"missing productive-control witness")

    def test_caps_and_nonfinite_or_malformed_numbers_refuse(self):
        for q in (-1,13):
            with self.assertRaises(c.InvalidCertificate): c.words(c.CONTROLS[0],q)
        with self.assertRaises(c.InvalidCertificate): c.words(c.CONTROLS[0],6,cap=10)
        for token in ("NaN","inf","1e99999999","1/0"):
            with self.assertRaises(c.InvalidCertificate): c.parse_rational(token)
        with self.assertRaises(c.InvalidCertificate): c.parse_packet("x"*2000001)


if __name__ == "__main__":
    unittest.main()
