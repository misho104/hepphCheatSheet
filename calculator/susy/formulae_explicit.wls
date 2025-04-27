(* ::Package:: *)

(* :Time-Stamp: <2024-8-4 14:38:28> *)
(* :Author: Sho Iwamoto / Misho *)
(* :Copyright: 2022 Sho Iwamoto / Misho *)
(* This file is licensed under the Apache License, Version 2.0.
   You may not use this file except in compliance with it.
   See the LICENSE file attached or the following URL for the full license information.
   https://www.apache.org/licenses/LICENSE-2.0
*)


LorSymbol := Alternatives[0, 1, 2, 3, Blank[Symbol]];
Lor := Alternatives[0, 1, 2, 3];
Spi := Alternatives[1, 2];

Metric[\[Mu]:Lor] := {1, -1, -1, -1}[[\[Mu]+1]];
Pauli[\[Mu]:Lor] := PauliMatrix[\[Mu]]
PauliBar[\[Mu]:Lor] := PauliMatrix[\[Mu]] * Metric[\[Mu]]
EE = Pauli[0];
delta = KroneckerDelta;
Mat[i_, n_Integer] /; NumericQ[i] := IdentityMatrix[n]*i

\[Eta][{\[Mu]:Lor, \[Nu]:Lor}, Null] := If[\[Mu]==\[Nu], Metric[\[Mu]], 0]
\[Eta][Null, {\[Mu]:Lor, \[Nu]:Lor}] := If[\[Mu]==\[Nu], Metric[\[Mu]], 0]
\[Epsilon][{\[Mu]:Lor, \[Nu]:Lor, \[Rho]:Lor, \[Sigma]:Lor}, Null] := LeviCivitaTensor[4][[\[Mu]+1, \[Nu]+1, \[Rho]+1, \[Sigma]+1]]
\[Epsilon][Null, {\[Mu]:Lor, \[Nu]:Lor, \[Rho]:Lor, \[Sigma]:Lor}] := -\[Epsilon][{\[Mu], \[Nu], \[Rho], \[Sigma]}, None]
\[Epsilon]U[a:Spi, b:Spi] := LeviCivitaTensor[2][[a, b]]
\[Epsilon]D[a:Spi, b:Spi] := -\[Epsilon]U[a, b]
si[{\[Mu]:Lor}, Null] := Pauli[\[Mu]]
si[Null, {\[Mu]:Lor}] := PauliBar[\[Mu]]
sb[{\[Mu]:Lor}, Null] := PauliBar[\[Mu]]
sb[Null, {\[Mu]:Lor}] := Pauli[\[Mu]]
si[{\[Mu]:Lor, \[Nu]:Lor}, Null] := (I/4)(Pauli[\[Mu]] . PauliBar[\[Nu]] - Pauli[\[Nu]] . PauliBar[\[Mu]])
sb[{\[Mu]:Lor, \[Nu]:Lor}, Null] := (I/4)(PauliBar[\[Mu]] . Pauli[\[Nu]] - PauliBar[\[Nu]] . Pauli[\[Mu]])
si[{\[Mu]:Lor}, {\[Nu]:Lor}]     := si[{\[Mu], \[Nu]}, Null] * Metric[\[Nu]]
sb[{\[Mu]:Lor}, {\[Nu]:Lor}]     := sb[{\[Mu], \[Nu]}, Null] * Metric[\[Nu]]
si[Null, {\[Mu]:Lor, \[Nu]:Lor}] := si[{\[Mu], \[Nu]}, Null] * Metric[\[Mu]] * Metric[\[Nu]]
sb[Null, {\[Mu]:Lor, \[Nu]:Lor}] := sb[{\[Mu], \[Nu]}, Null] * Metric[\[Mu]] * Metric[\[Nu]]

si[{\[Mu]:Lor}, Null][a:Spi, b:Spi] := Pauli[\[Mu]][[a,b]]
si[Null, {\[Mu]:Lor}][a:Spi, b:Spi] := PauliBar[\[Mu]][[a,b]]
sb[{\[Mu]:Lor}, Null][a:Spi, b:Spi] := PauliBar[\[Mu]][[a,b]]
sb[Null, {\[Mu]:Lor}][a:Spi, b:Spi] := Pauli[\[Mu]][[a,b]]
si[{\[Mu]:Lor, \[Nu]:Lor}, Null][a:Spi, b:Spi] := (I/4)(Pauli[\[Mu]] . PauliBar[\[Nu]] - Pauli[\[Nu]] . PauliBar[\[Mu]])[[a,b]]
sb[{\[Mu]:Lor, \[Nu]:Lor}, Null][a:Spi, b:Spi] := (I/4)(PauliBar[\[Mu]] . Pauli[\[Nu]] - PauliBar[\[Nu]] . Pauli[\[Mu]])[[a,b]]
si[{\[Mu]:Lor}, {\[Nu]:Lor}][a:Spi, b:Spi]     := si[{\[Mu], \[Nu]}, Null][[a,b]] * Metric[\[Nu]]
sb[{\[Mu]:Lor}, {\[Nu]:Lor}][a:Spi, b:Spi]     := sb[{\[Mu], \[Nu]}, Null][[a,b]] * Metric[\[Nu]]
si[Null, {\[Mu]:Lor, \[Nu]:Lor}][a:Spi, b:Spi] := si[{\[Mu], \[Nu]}, Null][[a,b]] * Metric[\[Mu]] * Metric[\[Nu]]
sb[Null, {\[Mu]:Lor, \[Nu]:Lor}][a:Spi, b:Spi] := sb[{\[Mu], \[Nu]}, Null][[a,b]] * Metric[\[Mu]] * Metric[\[Nu]]


\[Eta][\[Mu]:LorSymbol, \[Nu]:LorSymbol] := \[Eta][{\[Mu], \[Nu]}, Null]
si[\[Mu]:LorSymbol] := si[{\[Mu]}, Null]
sb[\[Mu]:LorSymbol] := sb[{\[Mu]}, Null]
si[\[Mu]:LorSymbol, \[Nu]:LorSymbol] := si[{\[Mu], \[Nu]}, Null]
sb[\[Mu]:LorSymbol, \[Nu]:LorSymbol] := sb[{\[Mu], \[Nu]}, Null]

LorentzIndices = {\[Mu], \[Nu], \[Rho], \[Sigma], \[Alpha], \[Beta], \[Gamma]};
SpinorIndices = {a, b, c, d, da, db, dc, dd};
Protect /@ Join[LorentzIndices, SpinorIndices];


Exit[]


CheckEqual[exp1_, exp2_] := Module[{
   lInd1 = Select[LorentzIndices, Not[FreeQ[exp1, #]]&],
   sInd1 = Select[SpinorIndices,  Not[FreeQ[exp1, #]]&],
   lInd2 = Select[LorentzIndices, Not[FreeQ[exp2, #]]&],
   sInd2 = Select[SpinorIndices,  Not[FreeQ[exp2, #]]&],
   lIndSum1, sIndSum1, sumTable1, summed1,
   lIndSum2, sIndSum2, sumTable2, summed2,
   lIndShared, sIndShared, compareTable, result,
   rule
  },
  rule = {(m_List)[i:1|2, j:1|2] :> m[[i,j]]};
  lIndSum1 = Complement[lInd1, lInd2];
  lIndSum2 = Complement[lInd2, lInd1];
  lIndShared = Intersection[lInd1, lInd2];
  sIndSum1 = Complement[sInd1, sInd2];
  sIndSum2 = Complement[sInd2, sInd1];
  sIndShared = Intersection[sInd1, sInd2];
  sumTable1 = Join[Table[{i, 0, 3}, {i, lIndSum1}], Table[{i, 1, 2}, {i, sIndSum1}]];
  sumTable2 = Join[Table[{i, 0, 3}, {i, lIndSum2}], Table[{i, 1, 2}, {i, sIndSum2}]];
  compareTable = Join[Table[{i, 0, 3}, {i, lIndShared}], Table[{i, 1, 2}, {i, sIndShared}]];
  summed1 = If[Length[sumTable1]==0, exp1, Sum@@{exp1, Sequence@@sumTable1}];
  summed2 = If[Length[sumTable2]==0, exp2, Sum@@{exp2, Sequence@@sumTable2}];
  result  = If[Length[compareTable]==0, summed1 == summed2 , Table@@{summed1 == summed2, Sequence@@compareTable}];
  result = Flatten[result/.rule];
  If[And@@result, {True, Length[result]}, result]
]


CheckEqual[si[\[Mu]] . sb[\[Nu]], Mat[\[Eta][\[Mu],\[Nu]], 2]-2I si[\[Mu],\[Nu]]]
CheckEqual[si[\[Mu]] . sb[\[Nu]], Mat[\[Eta][\[Mu],\[Nu]], 2]-2I si[\[Mu],\[Nu]]]
CheckEqual[si[\[Mu]] . sb[\[Nu]] . si[\[Rho]] + si[\[Rho]] . sb[\[Nu]] . si[\[Mu]], 2(si[\[Mu]]*\[Eta][\[Rho], \[Nu]] - si[\[Nu]]*\[Eta][\[Mu], \[Rho]] + si[\[Rho]]*\[Eta][\[Mu], \[Nu]])]
CheckEqual[si[\[Mu]] . sb[\[Nu]] . si[\[Rho]] - si[\[Rho]] . sb[\[Nu]] . si[\[Mu]], 2I si[Null, {\[Sigma]}]*\[Epsilon][{\[Mu], \[Nu], \[Rho], \[Sigma]}, Null]]
CheckEqual[sb[\[Mu]] . si[\[Nu]] . sb[\[Rho]] + sb[\[Rho]] . si[\[Nu]] . sb[\[Mu]], 2(sb[\[Mu]]*\[Eta][\[Rho], \[Nu]] - sb[\[Nu]]*\[Eta][\[Mu], \[Rho]] + sb[\[Rho]]*\[Eta][\[Mu], \[Nu]])]
CheckEqual[sb[\[Mu]] . si[\[Nu]] . sb[\[Rho]] - sb[\[Rho]] . si[\[Nu]] . sb[\[Mu]], -2I sb[Null, {\[Sigma]}]*\[Epsilon][{\[Mu], \[Nu], \[Rho], \[Sigma]}, Null]]



CheckEqual[si[\[Mu]][a, da]*sb[Null, {\[Mu]}][db,b], 2delta[a, b]delta[da,db]]
CheckEqual[si[\[Mu]][a, da]*si[Null, {\[Mu]}][b, db], 2\[Epsilon]D[a, b]\[Epsilon]D[da,db]]
CheckEqual[sb[\[Mu]][da, a]*sb[Null, {\[Mu]}][db,b], 2\[Epsilon]U[a, b]\[Epsilon]U[da,db]]


CheckEqual[(-1/2)si[{\[Mu],\[Nu]}, Null][a, b]  *si[Null, {\[Mu],\[Nu]}][c, d],   -delta[a, d]  *delta[c, b]   + (1/2)delta[a, b]  *delta[c, d]]
CheckEqual[(-1/2)sb[{\[Mu],\[Nu]}, Null][da, db]*sb[Null, {\[Mu],\[Nu]}][dc, dd], -delta[da, dd]*delta[dc, db] + (1/2)delta[da, db]*delta[dc, dd]]


Sum[(-1/2)sb[{\[Mu],\[Nu]}, Null][da, db]sb[Null, {\[Mu],\[Nu]}][dc, dd], {\[Mu], 0, 3}, {\[Nu], 0, 3}] /. {da->1, db->1, dc->1, dd->1} /. {(m_List)[i:1|2, j:1|2] :> m[[i,j]]}
-delta[da, dd]delta[dc, db] + (1/2)delta[da, db]delta[dc, dd] /. {da->1, db->1, dc->1, dd->1} /. {(m_List)[i:1|2, j:1|2] :> m[[i,j]]}


ue da  dc 
st  db dd






Exit[]
