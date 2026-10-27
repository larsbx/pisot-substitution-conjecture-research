"""Boundary hitting on class B's top-layer residue rays: uniform certificate and finite replay.

  mojo run -I . class_b_ray_certificate.mojo certify I       # ray I of ray_specs(): every q >= q0
  mojo run -I . class_b_ray_certificate.mojo replay I Q      # native graph = carrier, potential descends
  mojo run -I . class_b_ray_certificate.mojo below I         # exact complete graphs of the line below q0
  mojo run -I . class_b_ray_certificate.mojo all             # every tabulated ray: certify, two replays, below

Source note: docs/class-b-ray-certificate-2026-10-27.md.
"""
from std.sys import argv
from class_b_top_layer_profile import profile
from psc.class_b_ray_line import BRay
from psc.class_b_ray_certificate import certify_ray_rows, replay_finite
from psc.class_b_ray_tables import ray_specs, ray_rows, ray_potentials


def ray_of(i: Int) raises -> BRay:
    var specs = ray_specs()
    if i < 0 or i >= len(specs):
        raise Error("ray index outside ray_specs()")
    return BRay(specs[i][0], specs[i][1], specs[i][2])


def certify(i: Int) raises:
    _ = certify_ray_rows(ray_of(i), ray_specs()[i][3], ray_rows(i), ray_potentials(i))


def replay(i: Int, q: Int) raises:
    var ray = ray_of(i)
    var spec = ray_specs()[i].copy()
    if q < spec[3]:
        raise Error("replay below the ray floor")
    var n = replay_finite(ray, q, ray_rows(i), ray_potentials(i))
    print("CLASS_B_RAY_REPLAY " + ray.name() + " q=" + String(q), "vertices", n, "carrier_equal true descent true")


def below(i: Int) raises:
    """Every PIP top-layer member of the ray's residue class below its floor is an
    exact uncapped graph in which every vertex hits offset zero (raises otherwise)."""
    var ray = ray_of(i)
    var q0 = ray_specs()[i][3]
    var members = 0
    for pt in profile(ray.eps == 1, ray.g - 1, q0 - 1):
        if pt.q % ray.g == ray.r:
            members += 1
    print("CLASS_B_RAY_BELOW " + ray.name() + " q<" + String(q0), "pip_members", members, "all_hit true")


def main() raises:
    var args = argv()
    if len(args) == 3 and args[1] == "certify":
        certify(Int(args[2]))
        return
    if len(args) == 4 and args[1] == "replay":
        replay(Int(args[2]), Int(args[3]))
        return
    if len(args) == 3 and args[1] == "below":
        below(Int(args[2]))
        return
    if len(args) == 2 and args[1] == "all":
        for i in range(len(ray_specs())):
            certify(i)
            var spec = ray_specs()[i].copy()
            replay(i, spec[3])
            replay(i, spec[3] + spec[1])
            below(i)
        print("CLASS_B_RAY_CERTIFICATES_COMPLETE rays", len(ray_specs()))
        return
    raise Error("usage: certify I | replay I Q | below I | all")
