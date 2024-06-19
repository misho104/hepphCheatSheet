import re

import jinja2
import pathlib


class EditionValue:
    #    colors_tex = {"2020": "\\GREEN", "2022": "\\BLUE", "2024": "\\PINK"}
    colors_tex = {"2020": "\\BLUE", "2022": "\\PINK", "2024": "\\GREEN"}
    units_tex = {
        "m": "\\unit{m}",
        "us": "\\unit{\\mu s}",
        "um": "\\unit{\\mu m}",
        "ns": "\\unit{ns}",
        "nm": "\\unit{nm}",
        "mm": "\\unit{mm}",
        "s": "\\unit{s}",
        "years": "\\unit{yr}",
        "ecm": "\\ech\\unit{cm}",
        "mu(N)": "\\mu_N",
    }

    @classmethod
    def source(cls):
        return ", ".join(
            f"{v}{{\\textbf{{PDG{k}}}}}" for k, v in cls.colors_tex.items()
        )

    def __init__(self, edition, value, unit, cl):
        self.edition = edition
        self.value = value
        self.unit = unit.replace("@", "")
        self.cl = cl
        if m := re.match(r"^(\w+)-(\d+)$", self.unit):
            self.unit = m.group(1)
            self.value = f"{self.value})\\EE{{-{m.group(2)}}}".replace(
                "((", "("
            ).replace("))", ")")

    def suffix(self, unit=True):
        if self.cl == "None":
            cl = ""
        elif (f := int(float(self.cl) + 0.1)) in [68, 90, 95]:
            cl = f"\\bound{{{f}}}{{}}"
        else:
            raise ValueError(f"Unknown cl: {self.cl}")
        if unit and self.unit:
            u = self.units_tex.get(self.unit, "\\" + self.unit)
            return cl + u
        else:
            return cl

    def wrap_by_edition(self, text):
        color = self.colors_tex[self.edition]
        if text.startswith(">"):
            return ">" + color + "{" + text[1:] + "}"
        elif text.startswith("<"):
            return "<" + color + "{" + text[1:] + "}"
        else:
            return color + "{" + text + "}"

    def __str__(self):
        v = self.value.replace(" ", "#")
        return self.wrap_by_edition(v) + self.suffix()

    def str_no_unit(self):
        v = self.value.replace(" ", "#")
        return self.wrap_by_edition(v) + self.suffix(False)


class DictWrapper:
    def __init__(self, data):
        self.data = data

    def __call__(self, key):
        return self.data[str(key)]

    def sm(self, key):
        return str(self(key)) + "=" + str(self(str(key) + "m"))

    def nu(self, key):
        return self(key).str_no_unit()


def insert_spaces(*args):
    return [" ".join(s[i : i + 3] for i in range(0, len(s), 3)) for s in args]


def lstrip_zero_spaces(*args):
    values = [re.sub(r"^[0 ]+", "", s) for s in args]
    return values[0] if len(values) == 1 else values


def remove_rightmost_space(s):
    if (index := s.rfind(" ")) >= 0:
        return s[:index] + s[index + 1 :]
    return s


def remove_extra_spaces(*args):
    values = args
    while values[0].rfind(" ") >= 0:
        values = [remove_rightmost_space(v) for v in values]
    return values


def convert_data(data_raw):
    data = {}
    for d in data_raw.splitlines():
        d = d.replace("to", "--")
        v = re.sub(r"\s*([+-]+)\s+", r"\1", d).split()
        if not v:
            continue
        assert v[0] not in data
        key, edition, value, unit, cl = v[0], v[1], v[3], v[4], v[5]
        if m := re.match(r"^\((.*)\)[eE]([-+\d]+)$", value):
            value = m.group(1)
            unit = unit + m.group(2)
        if m := re.match(r"^(-?\d+)\.(\d+)\+-(\d+)\.(\d+)$", value):
            xi, xd, ei, ed = m.groups()
            xd, ed = insert_spaces(xd, ed)
            if int(ei) == 0 and len(xd) == len(ed):
                ed, xd = remove_extra_spaces(lstrip_zero_spaces(ed), xd)
                value = f"{xi}.{xd}({ed})"
            elif len(xd) == len(ed):
                value = f"{xi}.{xd}({ei}.{ed})"
        elif m := re.match(r"^(-?\d+)\.(\d+)\+(\d+)\.(\d+)-(\d+)\.(\d+)$", value):
            print(m)
            xi, xd, ei, ed, mi, md = m.groups()
            xd, ed, md = insert_spaces(xd, ed, md)
            if int(ei) == int(mi) == 0 and len(xd) == len(ed) == len(md):
                ed, xd, md = remove_extra_spaces(lstrip_zero_spaces(ed), xd, md)
                value = f"{xi}.{xd}\\unc{{({ed})}}{{({md})}}"
            else:
                value = f"{xi}.{xd}\\unc{{+{ei}.{ed}}}{{-{mi}.{md}}}"
        elif m := re.match(r"^(>|<)([.\d]+)[eE]([-+\d]+)$", value):
            value = f"{m.group(1)}{m.group(2)}\\EE{{{m.group(3)}}}"
        value = value.replace("+-", "\\pm")
        data[key] = EditionValue(edition, value, unit, cl)
    return data


masses = convert_data(
    """
   11  2022 S003M      0.51099895000+-0.00000000015 MeV   None          e MASS
   13  2022 S004M      105.6583755+-0.0000023 MeV         None    mu MASS
   15  2024 S035M      1776.93+-0.09        MeV           None  tau MASS
   6p  2024 Q007TP     172.57+-0.29         GeV           None  t-Quark Mass (Direct Measurements)
   6x  2022 Q007TP2    162.5+2.1-1.5        GeV           None  t-Quark Mass from Cross-Section Measurements
   6i  2024 Q007TP4    172.4+-0.7           GeV           None  t-Quark Pole Mass from Cross-Section Measurements
   23  2024 S044M      91.1880+-0.0020      GeV           None  Z MASS
   24  2024 S043M      80.3692 +- 0.0133    GeV           None  W MASS
   25  2024 S126M      125.20+-0.11         GeV           None  H MASS

Q123UM      2024 Q123UM     2.16+-0.07           MeV        90.0       u-QUARK MASS
Q123DM      2024 Q123DM     4.70+-0.07           MeV        90.0       d-QUARK MASS
Q123SM      2024 Q123SM     93.5+-0.8            MeV        90.0       s-QUARK MASS
Q123MR4     2024 Q123MR4    3.49+-0.07           MeV        90.0       mbar = (mass(u)+mass(d))/2
Q123MR0     2024 Q123MR0    0.462+-0.020         @          90.0       mass(u)/mass(d) MASS RATIO
Q123MR1     2020 Q123MR1    17 -- 22             @          None       mass(s)/mass(d) MASS RATIO
Q123MR5     2024 Q123MR5    27.33+0.18-0.14      @          90.0       mass(s)/mbar MASS RATIO
    4m 2024 Q004M      1.2730+-0.0046       GeV        90.0       c-QUARK MASS
    4p 2024 Q004M@     1.67+-0.07           GeV        90.0       c-QUARK MASS
    5m 2024 Q005M      4.183+-0.007         GeV        90.0       b-QUARK MASS
    5p 2024 Q005M@     4.78+-0.06           GeV        90.0       b-QUARK MASS

  211  2020 S008M      139.57039+-0.00018   MeV        None       pi+- MASS
  213  2020 M009M5     775.11+-0.34         MeV        None       CHARGED ONLY, tau DECAYS and --> e+ e-
  221  2020 S014M      547.862+-0.017       MeV        None       eta MASS
  223  2022 M001M      782.66+-0.13         MeV        None       omega(782) MASS
  111  2024 S009M      134.9768+-0.0005     MeV        None       pi0 MASS
  113  2022 M009M0     775.26+-0.23         MeV        None       NEUTRAL ONLY, e+ e-
  311  2024 S011M      497.611+-0.013       MeV        None       K0 MASS
  313  2020 M018M2     895.55+-0.20         MeV        None       NEUTRAL ONLY
  321  2024 S010M      493.677+-0.015       MeV        None       K+- MASS
  323  2022 M018M1     891.67+-0.26         MeV        None       CHARGED ONLY, HADROPRODUCED
  331  2020 M002M      957.78+-0.06         MeV        None       eta'(958) MASS
  333  2020 M004M      1019.461+-0.016      MeV        None       phi(1020) MASS
  411  2020 S031M      1869.65+-0.05        MeV        None       D+- MASS
  421  2022 S032M      1864.84+-0.05        MeV        None       D0 MASS
  431  2022 S034M      1968.35+-0.07        MeV        None       D_s+- MASS
  441  2024 M026M      2984.1+-0.4          MeV        None       eta_c(1S) MASS
  443  2020 M070M      3096.900+-0.006      MeV        None       J/psi(1S) MASS
  511  2024 S042M      5279.72+-0.08        MeV        None       B0 MASS
  521  2024 S041M      5279.41+-0.07        MeV        None       B+- MASS
  531  2024 S086M      5366.93+-0.10        MeV        None       B_s0 MASS
  541  2022 S091M      6274.47+-0.32        MeV        None       B_c+ MASS
  551  2020 M171M      9398.7+-2.0          MeV        None       eta_b(1S) MASS
  553  2024 M049M      9460.40+-0.10        MeV        None       Upsilon(1S) MASS
100553  2024 M052M      10023.4+-0.5         MeV        None       Upsilon(2S) MASS
200553  2024 M048M      10355.1+-0.5         MeV        None       Upsilon(3S) MASS
300553  2020 M047M      10579.4+-1.2         MeV        None       Upsilon(4S) MASS
 2212  2022 S016M      938.27208816+-0.00000029 MeV        None       p MASS (MeV)
 2112  2022 S017M      939.5654205+-0.0000005 MeV        None       n MASS (MeV)

S003MM    2024   S003MM     0.00115965218062+-0.00000000000012  @  None       mu_e/mu_B - 1 = (g-2)/2
S004MM    2024   S004MM     0.00116592059+-0.00000000022        @  None       mu_mu/(ehbar/2m_mu)-1 = (g_mu-2)/2
S035MM    2024   S035MM     -0.057to0.024                       @  95.0       mu_tau/(ehbar/2m_tau)-1 = (g_tau-2)/2
S016MM    2020   S016MM     2.7928473446+-0.0000000008  mu(N)      None       p MAGNETIC MOMENT
S017MM    2020   S017MM     -1.9130427+-0.0000005       mu(N)      None       n MAGNETIC MOMENT
S003EDM   2024   S003EDM    <4.1E-30                    ecm        90.0       e ELECTRIC DIPOLE MOMENT (d)
S004EDM   2020   S004EDM    <1.8E-19                    ecm        95.0       mu ELECTRIC DIPOLE MOMENT (d)
S016EDM   2020   S016EDM    <2.1E-25                    ecm        None       p ELECTRIC DIPOLE MOMENT
S017EDM   2020   S017EDM    <1.8E-26                    ecm        90.0       n ELECTRIC DIPOLE MOMENT
S044.7      2020 S044.7     69.911+-0.056 %               None       Z --> hadrons
S044.6      2020 S044.6     15.12+-0.05    %                  None       Z --> b bbar
S044.9      2020 S044.9     20.000+-0.055 %               None       Z --> invisible
S043.8      2020 S043.8     67.41+-0.27    %                  None       W+ --> hadrons
"""
)
gammas = convert_data(
    """
    6  2020 Q007W      1.42+0.19-0.15       GeV     None   t-quark DECAY WIDTH
   23  2024 S044W      2.4955+-0.0023       GeV     None   Z WIDTH
   24  2020 S043W      2.085 +- 0.042       GeV     None   W WIDTH
   25  2024 S126W      3.7+1.9-1.4          MeV     None   H DECAY WIDTH
   13  2020 S004T      2.1969811+-0.0000022 us      None   mu MEAN LIFE
   13m 2020 S004T@     659                  m       None   mu MEAN LIFE
   15  2020 S035T      (2.903+-0.005)E-13   s       None   tau MEAN LIFE
   15m 2020 S035T@     87.0                 um      None   tau MEAN LIFE
  111  2022 S009T      (8.43+-0.13)E-17     s       None   pi0 MEAN LIFE
  111m 2022 S009T@     25.3            nm      None   pi0 MEAN LIFE
  211  2020 S008T      26.033+-0.005        ns      None   pi+- MEAN LIFE
  211m 2020 S008T@     7.81           m       None   pi+- MEAN LIFE
  321  2020 S010T      (1.2380+-0.0020)E-8  s          None       K+- MEAN LIFE
  130  2020 S013T      (5.116+-0.021)E-8    s          None       K(L)0 MEAN LIFE
  310  2020 S012T      (8.954+-0.004)E-11   s          None       tau_s
  321m 2020 S010T@     3.71           m       None   ...
  130m 2020 S013T@     15.3 m None ...
  310m 2020 S012T@     26.8 mm None ...
 2212  2024 S016T      >9E29                years      90.0       p MEAN LIFE
 2112  2022 S017T      878.4+-0.5           s          None       n MEAN LIFE
"""
)
for k, v in masses.items():
    print(k, v)
for k, v in gammas.items():
    print(k, v)

environment = jinja2.Environment(
    loader=jinja2.FileSystemLoader("."),
    block_start_string="@@@",
    block_end_string="@@@",
    variable_start_string="<<",
    variable_end_string=">>",
)
template = environment.get_template("calculator/pdg_values.template")
pathlib.Path("calculator/pdg_values.output").write_text(
    template.render(
        m=DictWrapper(masses), g=DictWrapper(gammas), source=EditionValue.source()
    )
)
