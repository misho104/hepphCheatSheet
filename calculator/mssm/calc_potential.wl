(* ::Package:: *)

If[$FrontEnd =!= Null, SetDirectory[NotebookDirectory[]]];
<<tools.wl

SuperPot = Total[{
  P[\[Mu]]                                       \[Epsilon][SU2->"a", SU2->"b"]           SF[Hu, SU2->"a"].SF[Hd, SU2->"b"],
  -P[yu, Gen->"i", Gen->"j"]                 \[Epsilon][SU2->"a", SU2->"b"]           SF[bU, SU3->"x", Gen->"i"].SF[Hu, SU2->"a"].SF[Q, SU3->"x", SU2->"b", Gen->"j"],
  P[yd, Gen->"i", Gen->"j"]                  \[Epsilon][SU2->"a", SU2->"b"]           SF[bD, SU3->"x", Gen->"i"].SF[Hd, SU2->"a"].SF[Q, SU3->"x", SU2->"b", Gen->"j"],
  P[ye, Gen->"i", Gen->"j"]                  \[Epsilon][SU2->"a", SU2->"b"]           SF[bE, Gen->"i"].SF[Hd, SU2->"a"].SF[L, SU2->"b", Gen->"j"],
  -P[\[Kappa], Gen->"i"]                            \[Epsilon][SU2->"a", SU2->"b"]           SF[L, SU2->"a", Gen->"i"].SF[Hu, SU2->"b"],
  (1/2) P[\[Lambda], Gen->"i", Gen->"j", Gen->"k"]   \[Epsilon][SU2->"a", SU2->"b"]           SF[L, SU2->"a", Gen->"i"].SF[L, SU2->"b", Gen->"j"].SF[bE, Gen->"k"],
        P[\[Lambda]p, Gen->"i", Gen->"j", Gen->"k"]  \[Epsilon][SU2->"a", SU2->"b"]           SF[L, SU2->"a", Gen->"i"].SF[Q, SU3->"x", SU2->"b", Gen->"j"].SF[bD, SU3->"x", Gen->"k"],
  (1/2) P[\[Lambda]pp, Gen->"i", Gen->"j", Gen->"k"]\[Epsilon]3[SU3->"x", SU3->"y", SU3->"z"] SF[bU, SU3->"x", Gen->"i"].SF[bD, SU3->"y", Gen->"j"].SF[bD, SU3->"z", Gen->"k"]
}];

Fields = {
  SF[Hu,            SU2->Null],
  SF[Hd,            SU2->Null],
  SF[Q,  SU3->Null, SU2->Null, Gen->Null],
  SF[bU, SU3->Null,            Gen->Null],
  SF[bD, SU3->Null,            Gen->Null],
  SF[L,             SU2->Null, Gen->Null],
  SF[bE,                       Gen->Null]
};

P  /: Conjugate[P[a__]] := PC[a]
PC /: Conjugate[PC[a__]] := P[a]
S  /: Conjugate[S[a__]] := SC[a]
SC /: Conjugate[SC[a__]] := S[a]
S /: S[name_, indices___] SC[name_, indices___] := S2[name]
P /: P[name_, indices___] PC[name_, indices___] := P2[name]
\[Epsilon] /: Conjugate[\[Epsilon][a__]] := \[Epsilon][a]
\[Epsilon]3 /: Conjugate[\[Epsilon]3[a__]] := \[Epsilon]3[a]
S2 /: S2[a__]^2 := S4[a]

P /: P[yu, Gen->i_, Gen->j_]*PC[yu, Gen->k_, Gen->j_] := P[yuyudag, Gen->i, Gen->k]
P /: P[yu, Gen->i_, Gen->j_]*PC[yu, Gen->i_, Gen->k_] := P[yudagyu, Gen->k, Gen->j]
P /: P[yd, Gen->i_, Gen->j_]*PC[yd, Gen->k_, Gen->j_] := P[ydyddag, Gen->i, Gen->k]
P /: P[yd, Gen->i_, Gen->j_]*PC[yd, Gen->i_, Gen->k_] := P[yddagyd, Gen->k, Gen->j]
P /: P[ye, Gen->i_, Gen->j_]*PC[ye, Gen->k_, Gen->j_] := P[yeyedag, Gen->i, Gen->k]
P /: P[ye, Gen->i_, Gen->j_]*PC[ye, Gen->i_, Gen->k_] := P[yedagye, Gen->k, Gen->j]

(*symmetry/antisymmetry*)
ToOrder[exp_] := exp //. {
  P[\[Lambda], Gen->a_, Gen->b_, Gen->c_]       /; Not[OrderedQ[{a, b}]] :> -P[\[Lambda], Gen->b, Gen->a, Gen->c],
  P[\[Lambda]pp, Gen->a_, Gen->b_, Gen->c_]     /; Not[OrderedQ[{b, c}]] :> -P[\[Lambda]pp, Gen->a, Gen->c, Gen->b],
  PC[\[Lambda], Gen->a_, Gen->b_, Gen->c_]      /; Not[OrderedQ[{a, b}]] :> -PC[\[Lambda], Gen->b, Gen->a, Gen->c],
  PC[\[Lambda]pp, Gen->a_, Gen->b_, Gen->c_]    /; Not[OrderedQ[{b, c}]] :> -PC[\[Lambda]pp, Gen->a, Gen->c, Gen->b],
  \[Epsilon][SU2->a_, SU2->b_]                   /; Not[OrderedQ[{a, b}]] :> -\[Epsilon][SU2->b, SU2->a],
  \[Epsilon]3[any1___, SU3->a_, SU3->b_, any2___] /; Not[OrderedQ[{a, b}]] :> -\[Epsilon]3[any1, SU3->b, SU3->a, any2]
};

U1 = {Hu->1/2, Hd->1/2, Q->1/6, bU->-2/3, bD->1/3, L->-1/2, bE->1};
SF[name_, any1___, a_->x_, any2___, b_->y_, any3___] /; Not[OrderedQ[{a, b}]] := SF[name, any1, b->y, any2, a->x, any3]
S[name_, any1___, a_->x_, any2___, b_->y_, any3___] /; Not[OrderedQ[{a, b}]] := S[name, any1, b->y, any2, a->x, any3]
F[name_, any1___, a_->x_, any2___, b_->y_, any3___] /; Not[OrderedQ[{a, b}]] := FC[name, any1, b->y, any2, a->x, any3]
SC[name_, any1___, a_->x_, any2___, b_->y_, any3___] /; Not[OrderedQ[{a, b}]] := SC[name, any1, b->y, any2, a->x, any3]
FC[name_, any1___, a_->x_, any2___, b_->y_, any3___] /; Not[OrderedQ[{a, b}]] := FC[name, any1, b->y, any2, a->x, any3]


D3\[Alpha] = -P[g3]*Total[{
  +SC[Q, SU3->"x", SU2->"a", Gen->"i"]*tau[\[Alpha], SU3->"x", SU3->"y"]*S[Q, SU3->"y", SU2->"a", Gen->"i"],
  -S[bU, SU3->"x",           Gen->"i"]*tau[\[Alpha], SU3->"x", SU3->"y"]*SC[bU, SU3->"y",          Gen->"i"],
  -S[bD, SU3->"x",           Gen->"i"]*tau[\[Alpha], SU3->"x", SU3->"y"]*SC[bD, SU3->"y",          Gen->"i"]
}];
D2\[Alpha] = -P[g2]*Total[{
  SC[Q, SU3->"x", SU2->"a", Gen->"i"]*T[\[Alpha], SU2->"a", SU2->"b"]*S[Q, SU3->"x", SU2->"b", Gen->"i"],
  SC[L,           SU2->"a", Gen->"i"]*T[\[Alpha], SU2->"a", SU2->"b"]*S[L,          SU2->"b", Gen->"i"],
  SC[Hu, SU2->"a"]*T[\[Alpha], SU2->"a", SU2->"b"]*S[Hu, SU2->"b"],
  SC[Hd, SU2->"a"]*T[\[Alpha], SU2->"a", SU2->"b"]*S[Hd, SU2->"b"]
}];
D1\[Alpha] = -P[gY] * Total[{
  (+1/2)SC[Hu, SU2->"a"] S[Hu, SU2->"a"], 
  (-1/2)SC[Hd, SU2->"a"] S[Hd, SU2->"a"], 
  (+1/6)SC[Q,  SU3->"x", SU2->"a", Gen->"i"] S[Q,  SU3->"x", SU2->"a", Gen->"i"], 
  (-2/3)SC[bU, SU3->"x", Gen->"i"] S[bU, SU3->"x", Gen->"i"], 
  (+1/3)SC[bD, SU3->"x", Gen->"i"] S[bD, SU3->"x", Gen->"i"], 
  (-1/2)SC[L, SU2->"a", Gen->"i"]  S[L, SU2->"a", Gen->"i"], 
  SC[bE, Gen->"i"] S[bE, Gen->"i"]
}];


(* ::Section:: *)
(*F-terms*)


Derivative[exp_, field:S[name_, indices__]] := Module[{\[Delta], result = exp, count, appearance, ind, rep},
  result = result /. {S[name, any___] :> S[name, any] + \[Delta] S[\[Delta], any]} // Coefficient[#, \[Delta], 1]& // SumToList;
  For[count = 1, count <= Length[result], count++,
    appearance = Cases[result[[count]], S[\[Delta], __], All
  ] // DeleteDuplicates;
  If[Not[Length[appearance] == 1], Abort["??"]];
  rep = (#[[1]] /. (List@@appearance[[1, 2;;]]))->(#[[1]] /. {indices})&/@{indices};
  result[[count]] = result[[count]] //. rep];
  result /. S[\[Delta], ___]:>1 // Total
];
Fterm[exp_, field_] := Module[{fieldtmp},
  fieldtmp = field /. {Null:>Unique[], SF->S};
  Derivative[exp //. {Dot->Times, SF->S}, fieldtmp]
];
result = Reap[
  Module[{tmp, scalar},
    tmp = SuperPot /. {(Gen->"i")->(Gen->"$i"), (SU2->"a")->(SU2->"$a"), (SU3->"x")->(SU3->"$x")};
    Do[
      scalar = (S@@field) /. {(Gen->Null)->(Gen->"i"), (SU2->Null)->(SU2->"a"), (SU3->Null)->(SU3->"x")};
      Sow["-F^*_{"<>ToTeXString[scalar]<>"}\n& = \n"];
      Sow[ToTeXString[JoinIndices[Fterm[tmp, scalar]]]];
      Sow["\n\\\\\n"];
    , {field, Fields}]
  ]
][[2]] // Flatten // StringJoin;

ToFile["Fterms.raw", result]


CombinationRules = {
    \[Epsilon][SU2->a_, SU2->b_]\[Epsilon][SU2->a_, SU2->c_] :> delta[b,c],
    \[Epsilon][SU2->a_, SU2->b_]\[Epsilon][SU2->c_, SU2->b_] :> delta[a,c],
    \[Epsilon][SU2->a_, SU2->b_]\[Epsilon][SU2->b_, SU2->c_] :> -delta[a,c],
    \[Epsilon][SU2->a_, SU2->b_]\[Epsilon][SU2->c_, SU2->a_] :> -delta[b,c],
    \[Epsilon]3[SU3->a_, SU3->b_, SU3->c_]\[Epsilon]3[SU3->a_, SU3->d_, SU3->e_] :> delta[b,d]delta[c,e] - delta[b,e]delta[c,d],
    \[Epsilon]3[any3___, SU3->a_, any4___]\[Epsilon]3[any1___, SU3->x_, SU3->a_, any2___] :> (-1)*\[Epsilon]3[any3, SU3->a, any4]\[Epsilon]3[any1, SU3->a, SU3->x, any2],
    any1_[any2___, any3_ -> x_, any4___] delta[x_, y_] :> any1[any2, any3->y, any4],
    any1_[any2___, any3_ -> x_, any4___] delta[y_, x_] :> any1[any2, any3->y, any4]
};
RenewIndices[exp_] := Module[{old, result=SumToList[exp]},
  old = Counts[Cases[exp, (_ -> a_) :> a, All]] /. Association -> List // Cases[#, (p_ -> 2) :> p] &;
  Do[result = result /. o -> Unique[o], {o, old}];
  Total[result]]
FtermSUSYPotential = Total[Module[{org, conj},
  org = Fterm[SuperPot, #];
  conj = RenewIndices /@ (org // Conjugate);
  org * conj // Expand]& /@ Fields] // Expand//. CombinationRules;


PickUpScalar[exp_] := Module[{s, sc, s2, s4},
  s = Cases[exp, S[a_, any___] :> a, All] // Sort;
  sc = Cases[exp, SC[a_, any___] :> a, All] // Sort;
  s2 = Cases[exp, S2[a_, any___] :> {a,a}, All] // Sort;
  s4 = Cases[exp, S4[a_, any___] :> {a,a,a,a}, All] // Sort;
  {s, sc, s2, s4} // Flatten // Sort]
result = SumToList[FtermSUSYPotential] // Total // SumToList // GroupBy[#, PickUpScalar[#]&]&;
result = FixedPoint[Expand[#] //. CombinationRules&, result /. Association->List];


result = (#[[1]]->(#[[2]] // ToOrder // Total)) &/@ result;
ToTeXString /@ result[[All,2]];
s = StringRiffle[%, "\n\\\\\n+ "];
s// ToFile["FtermPotential.raw", #]&


DtermSUSYPotential1 = (1/2)D1\[Alpha] D1\[Alpha];
DtermSUSYPotential2 = (1/2)D2\[Alpha](RenewIndices /@ SumToList[D2\[Alpha]] // Total) // Expand;
DtermSUSYPotential2 = Expand[DtermSUSYPotential2 //. {T[a_, SU2->i_, SU2->j_]T[a_, SU2->k_, SU2->l_] :> (1/2)(delta[i,l]delta[j,k]-delta[i,j]delta[k,l]/2)}] //. CombinationRules;
DtermSUSYPotential3 = (1/2)D3\[Alpha](RenewIndices /@ SumToList[D3\[Alpha]] // Total) // Expand;
DtermSUSYPotential3 = Expand[DtermSUSYPotential3 //. {tau[a_, SU3->i_, SU3->j_]tau[a_, SU3->k_, SU3->l_] :> (1/2)(delta[i,l]delta[j,k]-delta[i,j]delta[k,l]/3)}] //. CombinationRules;
DtermSUSYPotential = Expand[DtermSUSYPotential1 + DtermSUSYPotential2 + DtermSUSYPotential3] //. {
  P[g_:gY|g2|g3]^2 :> P2[g]
};

result = SumToList[FtermSUSYPotential+DtermSUSYPotential] // Total // SumToList // GroupBy[#, PickUpScalar[#]&]&;
result = FixedPoint[Expand[#] //. CombinationRules&, result /. Association->List];
result = (#[[1]]->(#[[2]] // ToOrder // Total)) &/@ result;
ToTeXString /@ result[[All,2]];
s = StringRiffle[%, "\n\\\\&\n+ "];
s // ToFile["SUSYPotential.raw", #]&


SuperPot //. {
  Dot[SF[x1__], SF[x2__], SF[x3__]] :> (-1)(Dot[S[x1], F[x2], F[x3]] + Dot[S[x3], F[x1], F[x2]] + Dot[S[x2], F[x3], F[x1]]),
  Dot[SF[x1__], SF[x2__]] :> (-1)Dot[F[x1], F[x2]]
} // ExpandAll
%//.Dot[a_,b_]/;Not[OrderedQ[OrderInTerm/@{a,b}]]&&FreeQ[{a,b},Dot]:>(Dot[b,a]) // RewriteIndices//ToOrder;
StringRiffle[ToTeXString /@ (List@@(Expand[%])), "\n\\\\&\n+ "];
ToFile["superfermion.raw", %]



