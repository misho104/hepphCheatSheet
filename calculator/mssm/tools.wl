(* ::Package:: *)

SumToList[exp_]  := Module[{tmp = Expand[exp]}, If[Head[tmp] === Plus, List@@tmp, {tmp}]];

OrderInTerm[exp_] := Which[
  Head[exp] === String, {-1, exp},
  NumericQ[exp], {0, exp},
  Head[exp] === \[Epsilon], {1, 0},
  Head[exp] === \[Epsilon]3, {1, 1},
  MemberQ[{P, PC, P2}, Head[exp]], {1, exp[[1]]/.{\[Mu]->0, yu->1, yd->2, ye->3, \[Kappa]->4, \[Lambda]->5, \[Lambda]p->6, \[Lambda]pp->7}},
  MemberQ[{S, SC, S2, S4}, Head[exp]], {2, exp[[1]]/.{Hu->1, Hd->2, bU->11, bD->12, bE->13, Q->21, L->22}},
  MemberQ[{F, FC}, Head[exp]], {3, exp[[1]]/.{Hu->1, Hd->2, bU->11, bD->12, bE->13, Q->21, L->22}},
  True, {4, exp}];

TermOrder[exp_] := DeleteDuplicates[Cases[exp, (P|PC)[a_, ___] :> a, All]]/.{\[Mu]->0, yu->1, yd->2, ye->3, \[Kappa]->4, \[Lambda]->5, \[Lambda]p->6, \[Lambda]pp->7};

ToTeXString[(type:S|P|SC|PC|S2|S4|P2|F|FC)[name_, rules___]] := Module[{r = {rules}, gen, su2, su3},
  gen = Cases[r, (Gen->a_) :> TextString[a]]//StringJoin;
  su2 = Cases[r, (SU2->a_) :> TextString[a]]//StringJoin;
  su3 = Cases[r, (SU3->a_) :> TextString[a]]//StringJoin;
  StringJoin[{"@", TextString[type], ":", TextString[name], ":", gen, ":", su2, su3, "@"}]
];

ToTeXString[(type:\[Epsilon]3|\[Epsilon])[rules___]] := Module[{r = {rules}, name, gen, su2, su3},
  name = <|\[Epsilon]->"\\epsilon", \[Epsilon]3->"\\epsilon"|>[type];
  gen = Cases[r, (Gen->a_) :> TextString[a]]//StringJoin;
  su2 = Cases[r, (SU2->a_) :> TextString[a]]//StringJoin;
  su3 = Cases[r, (SU3->a_) :> TextString[a]]//StringJoin;
  StringJoin[{"@", name, ":", gen, ":", su2, su3, "@"}]
];

JoinIndices[exp_] := ( exp //. {
    (func:P|PC)[any1___, typ_->a1_, typ_->a2_, any2___](f1:S|SC)[any3___, typ_->a1_, any4___](f2:S|SC)[any5___, typ_->a2_, any6___] :> f1[any3, typ->"", any4].func[any1, typ->"", any2].f2[any5, typ->"", any6]/;FreeQ[{any1, any2}, typ]
});

ToTeXString[exp_] := Module[{result = Expand[exp]},
  (*ordering*)
  result = RewriteIndices[result];
  result = ToOrder[result];
  result = SortBy[OrderInTerm][#/.Times->List]& /@ SumToList[result];
  result = Expand[result]//.{
    a_Rational :> ToString[TeXForm[a]],
    a_Integer :> "("<>ToString[TeXForm[a]]<>")"
  };

  (*Factorize*)
  result = Total[Times@@#& /@ result]//Factor;
  result = result//.{Times->TIMES, Plus->PLUS}/.{
    TIMES[a__] :> TIMES@@SortBy[OrderInTerm][{a}],
    PLUS[a__] :> PLUS@@SortBy[TermOrder][{a}]
  };
  result = result//.{
    term:(_S|_P|_SC|_PC|_S2|_S4|_P2|_\[Epsilon]|_\[Epsilon]3|_F|_FC) :> ToTeXString[term],
    PLUS[a__] :> {"\\left( ", Sequence@@(Riffle[{a}, " + "]), " \\right)"},
    List[a__String] :> StringJoin[{a}],
    (TIMES|Dot)[a__String] :> StringJoin[{a}]
  };
  result
];

RewriteIndicesOrder[exp_] := Which[
  NumericQ[exp], {0, exp},
  Head[exp] === \[Epsilon], {2, 0},
  Head[exp] === \[Epsilon]3, {2, 1},
  MemberQ[{P, PC, P2}, Head[exp]], {1, exp[[1]]/.{\[Mu]->0, yu->1, yd->2, ye->3, \[Kappa]->4, \[Lambda]->5, \[Lambda]p->6, \[Lambda]pp->7}},
  MemberQ[{S, SC, S2, S4}, Head[exp]], {0, exp[[1]]/.{Hu->1, Hd->2, bU->11, bD->12, bE->13, Q->21, L->22}},
  MemberQ[{F, FC}, Head[exp]], {3, exp[[1]]/.{Hu->1, Hd->2, bU->11, bD->12, bE->13, Q->21, L->22}},
  Not[FreeQ[exp, (S|SC|S2|S4|F|FC)[__]]], {0, 100},
  True, {4, exp}];

RewriteIndices[exp_, code_, indices_] :=
  Module[{tmp, old, nottoreplace, toreplace, new, rule},
    tmp = If[Head[exp] == Times, List @@ exp, {exp}];
    tmp = SortBy[RewriteIndicesOrder][tmp];
    old = Cases[tmp, (code -> a_) :> a, All];
    nottoreplace = Counts[old] /. Association -> List // Cases[#, (p_ -> 1) :> p] &;
    toreplace = Counts[old] /. Association -> List // Cases[#, (p_ -> 2) :> p] &;
    new = Select[indices, FreeQ[nottoreplace, #] &];
    rule = (#[[1]] -> #[[2]]) & /@ Transpose[{toreplace, new[[1 ;; Length[toreplace]]]}];
    exp /. rule];

RewriteIndices[exp_] := Module[{result},
  result = SumToList[exp];
  result = RewriteIndices[#, Gen, {"i", "j", "k", "l", "m", "n", "o"}] & /@ result;
  result = RewriteIndices[#, SU2, {"a", "b", "c", "d", "e", "f", "g"}] & /@ result;
  result = RewriteIndices[#, SU3, {"x", "y", "z", "w", "v", "u", "s"}] & /@ result;
  Total[result]
];


ToOrder[exp_] := exp;


ToFile[filename_String, exp_String] := Module[{filehandle, path},
  filehandle = OpenWrite[];
  WriteString[filehandle, exp];
  path = Close[filehandle];
  Run["! cat " <> path <> " | ./convert_to_tex.pl | tee " <> filename];
  filehandle = OpenRead[filename];
  ReadString[filehandle]
]
