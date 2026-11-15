"""Export exact raw-pair, local-lift, represented-set and profile controls.

Every line describes the supplied finite cyclic models.  No count is a
compact Pisot overlap measure, and no mask authenticates a Pisot residue
enclosure.
"""

from psc.c4_bounded_cover import forward_leak_control
from psc.c4_local_admissibility import (
    CyclicModel, local_fixture, local_summary, singular_fixture_model,
    singular_lift_control,
)


def _values(kind: String, fixture: Int, values: List[Int]) -> String:
    var result = kind+String(" ")+String(fixture)
    for value in values:
        result += String(" ")+String(value)
    return result^


def _record(kind: String, fixture: Int, identity: Int, values: List[Int]) -> String:
    return _values(kind+String(" ")+String(fixture),identity,values)


def _model_inputs(fixture: Int, model: CyclicModel):
    for parent in range(3):
        var word: List[Int] = [len(model.images[parent])]
        for letter in model.images[parent]:
            word.append(letter)
        print(_record("image",fixture,parent,word))
    print(_values("star",fixture,model.star))
    print(_values("tiles",fixture,model.tiles))
    print(_values("profiles",fixture,model.profiles))
    for source in range(len(model.sources)):
        print(_record("source",fixture,source,model.sources[source]))
    for state in range(len(model.domain)):
        print(_record("domain",fixture,state,model.domain[state]))


def main() raises:
    print("schema c4-local-admissibility-v1")
    print("limits",15,64,27,64,4096,20000,200000,100000)
    var sources = 0
    var pairs = 0
    for fixture in range(6):
        var inventory = local_fixture(fixture)
        var model = inventory.model.copy()
        print("model",fixture,model.modulus,model.action,inventory.determinant,model.profile_modulus)
        _model_inputs(fixture,model)
        for digit in range(len(inventory.digits)):
            print(_record("digit",fixture,digit,inventory.digits[digit]))
        for pair in range(len(inventory.pairs)):
            print(_record("pair",fixture,pair,inventory.pairs[pair]))
        for source in range(len(inventory.rows)):
            print(_record("row",fixture,source,inventory.rows[source]))
        for axis in range(len(inventory.basis)):
            print(_record("basis",fixture,axis,inventory.basis[axis]))
        print(_values("summary",fixture,local_summary(inventory)))
        sources += len(inventory.rows)
        pairs += len(inventory.pairs)
    var singular = singular_fixture_model()
    print("singular_model",6,singular.modulus,singular.action,0,singular.profile_modulus)
    _model_inputs(6,singular)
    var lifts = singular_lift_control()
    for witness in range(len(lifts)):
        print(_record("singular_lift",6,witness,lifts[witness]))
    print("singular_summary",6,1,len(lifts),1)
    var leak = forward_leak_control()
    print("control forward_leak",leak[0],leak[1],leak[2])
    print("total",6,sources,pairs)
