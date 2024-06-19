import pdg

api = pdg.connect("sqlite:///calculator/pdgall-2024-v0.1.0.sqlite", pedantic=True)
editions = [2024, 2022, 2020]

METER_GEV = 5.0677307e15
SECOND_GEV = 1.5192674e24
METER_PER_SECOND = 3.335641e-09


def _find_by_class(cls, pid_list=None):
    if not pid_list:  # look up all
        for i in api.get_all(edition=editions[0]):
            if isinstance(i, cls):
                if s := i.summary_values(summary_table_only=True):
                    print(s[0].pdgid, s[0].description)
        return
    for pid in pid_list:
        for e in editions:
            p = api.get_particle_by_mcid(pid, edition=e)
            for i in p.properties():
                if isinstance(i, cls):
                    if s := i.summary_values(summary_table_only=True):
                        print(
                            "{:5d} {:5d} {:10s} {:20s} {:10s} {:10s} {:s}".format(
                                pid,
                                e,
                                s[0].pdgid,
                                s[0].display_value_text,
                                s[0].get("unit_text", "[No Unit]"),
                                str(s[0].get("confidence_level")),
                                s[0].description,
                            )
                        )
                        if cls == pdg.data.PdgLifetime:
                            print(
                                convert_sec_to_meter(
                                    s[0].value,
                                    s[0]["unit_text"],
                                    s[0].error_positive,
                                    s[0].error_negative,
                                ),
                                "meter",
                            )


def find(key_list):
    for key in key_list:
        for e in editions:
            if s := api.get(key, edition=e).summary_values():
                print(
                    "{:10s} {:5d} {:10s} {:20s} {:10s} {:10s} {:s}".format(
                        key,
                        e,
                        s[0].pdgid,
                        s[0].display_value_text,
                        s[0].get("unit_text", "[No Unit]"),
                        str(s[0].get("confidence_level")),
                        s[0].description,
                    )
                )


def find_masses(pid_list=None):
    return _find_by_class(pdg.data.PdgMass, pid_list)


def find_gammas(pid_list=None):
    return _find_by_class(pdg.data.PdgWidth, pid_list)


def find_taus(pid_list=None):
    return _find_by_class(pdg.data.PdgLifetime, pid_list)


def get_mass(particle_name):
    mass_list = {
        e: api.get_particle_by_name(particle_name, edition=e).mass for e in editions
    }
    print(mass_list)
    for i in mass_list:
        print(i)


def get(key):
    result = {}
    for e in editions:
        v = api.get(key, edition=e).summary_values(summary_table_only=True)
        assert len(v) == 1, f"Unexpected number of values: {v}"
        result[e] = v[0]
    return result


def invert_to_GeV_inverse(value, unit, ep, em=None):
    em = ep if em is None else em
    if unit == "GeV":
        pass
    elif unit == "MeV":
        value, ep, em = [v * 1e-3 for v in [value, ep, em]]
        unit = "GeV"
    elif unit == "years":
        return 0, 0, 0
    else:
        raise ValueError(f"Unknown unit: {unit}")
    v_inv = 1 / value
    ep_inv = 1 / (value - abs(em)) - v_inv
    em_inv = 1 / (value + abs(ep)) - v_inv  # [/GeV]
    return v_inv, ep_inv, em_inv


def convert_mass_to_meter(value, unit, ep, em=None):
    return [v / METER_GEV for v in invert_to_GeV_inverse(value, unit, ep, em)]


def convert_mass_to_second(value, unit, ep, em=None):
    return [v / SECOND_GEV for v in invert_to_GeV_inverse(value, unit, ep, em)]


def convert_sec_to_meter(value, unit, ep, em=None):
    if unit == "s":
        pass
    elif unit == "years":
        return 0, 0, 0
    else:
        raise ValueError(f"Unknown unit: {unit}")
    return [None if v is None else v / METER_PER_SECOND for v in [value, ep, em]]


find_masses([11, 13, 15, 6, 23, 24, 25])
find_gammas([6, 23, 24, 25])
find_taus([13, 15, 111, 211, 321, 130, 310, 2212, 2112])
find_masses([1, 2, 3, 4, 5])
find_masses([211, 213, 221, 223, 111, 113, 311, 313, 321, 323, 331, 333])
find_masses([411, 421, 431, 441, 443, 511, 521, 531, 541, 551])
find_masses([553, 100553, 200553, 300553, 2212, 2112])
find(
    [
        "Q123UM",
        "Q123DM",
        "Q123MR4",
        "Q123MR0",
        "Q123SM",
        "Q123MR1",
        "Q123MR5",
        "Q123MR3",
    ]
)

find(
    [
        "S003MM",
        "S004MM",
        "S035MM",
        "S016MM",
        "S017MM",
        "S003EDM",
        "S004EDM",
        "S016EDM",
        "S017EDM",
        "S044.7",
        "S044.6",
        "S044.9",
        "S043.8",
    ]
)
exit(0)
targets = [("Q011M",)]
"""

S000M gamma MASS
S043M W MASS
S044M Z MASS
S126M H MASS
S003M e MASS
S004M mu MASS
S035M tau MASS
Q123UM u-QUARK MASS
Q123DM d-QUARK MASS
Q123SM s-QUARK MASS
Q004M c-QUARK MASS
Q005M b-QUARK MASS
Q007TP t-Quark Mass (Direct Measurements)
Q007TP2 t-Quark Mass from Cross-Section Measurements
Q007TP4 t-Quark Pole Mass from Cross-Section Measurements
S008M pi+- MASS
S009M pi0 MASS
S014M eta MASS

for k, v in get("Q005M").items():
    print(k, v)
exit(0)
get_mass("b")


exit(0)
for edition in [2024, 2022, 2020]:
    m = api.get("Q007TP", edition=edition)
    for i in api.get_all(edition=edition):
        if isinstance(i, pdg.data.PdgMass):
            print(i.summary_values())

#    print(m.summary_values())
#    particle = api.get_particle_by_name("t", edition=edition)
#    for p in particle.properties():
#        print(p)
"""
