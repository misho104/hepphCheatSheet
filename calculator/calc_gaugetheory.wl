(* ::Package:: *)

T[1] = {{0,1}, {1,0}} / 2;
T[2] = {{0,-I}, {I,0}} / 2;
T[3] = {{1,0}, {0,-1}} / 2;
\[Epsilon][a_, b_, c_] := LeviCivitaTensor[3][[a,b,c]];
\[Epsilon]2 := LeviCivitaTensor[2]
\[Lambda][1] = {{0,1,0}, {1,0,0}, {0,0,0}};
\[Lambda][2] = {{0,-I,0}, {I,0,0}, {0,0,0}};
\[Lambda][3] = {{1,0,0}, {0,-1,0}, {0,0,0}};
\[Lambda][4] = {{0,0,1}, {0,0,0}, {1,0,0}};
\[Lambda][5] = {{0,0,-I}, {0,0,0}, {I,0,0}};
\[Lambda][6] = {{0,0,0}, {0,0,1}, {0,1,0}};
\[Lambda][7] = {{0,0,0}, {0,0,-I}, {0,I,0}};
\[Lambda][8] = {{1,0,0}, {0,1,0}, {0,0,-2}}/Sqrt[3];
\[Tau][a_] := \[Lambda][a]/2;
fmatrix = Table[Tr[(\[Tau][a].\[Tau][b]-\[Tau][b].\[Tau][a]).\[Tau][c]]*(2/I), {a,8}, {b,8}, {c,8}];
f[a_, b_, c_] := fmatrix[[a,b,c]]

\[Delta] = KroneckerDelta;


Table[Tr[T[a].T[b]] == \[Delta][a,b]/2,{a,3},{b,3}] // And@@Flatten[#]&
Table[T[a].T[b]-T[b].T[a] == I Sum[\[Epsilon][a,b,c] T[c], {c,3}], {a,3},{b,3}] // And@@Flatten[#]&
Table[
    Sum[\[Epsilon][a,d,e]\[Epsilon][b,c,d]+\[Epsilon][b,d,e]\[Epsilon][c,a,d]+\[Epsilon][c,d,e]\[Epsilon][a,b,d], {d,3}]==0,
    {a,3},{b,3},{c,3},{e,3}] // And@@Flatten[#]&
    
Sum[T[a].T[a], {a,3}]
Table[Sum[\[Epsilon][a,b,c]\[Epsilon][a,d,e],{a,3}]==\[Delta][b,d]\[Delta][c,e]-\[Delta][b,e]\[Delta][c,d], {b,3}, {c,3}, {d,3}, {e,3}] // And@@Flatten[#]&
Table[-Conjugate[T[a]][[i,j]]==Sum[\[Epsilon]2[[i,k]]\[Epsilon]2[[j,l]]T[a][[k,l]], {k, 2}, {l,2}], {i,2}, {j,2}, {a, 3}] // And@@Flatten[#]&
Table[-\[Epsilon]2.T[a].\[Epsilon]2 == Inverse[\[Epsilon]2].T[a].\[Epsilon]2 == Conjugate[-T[a]], {a,3}]
Table[-\[Epsilon]2.Conjugate[-T[a]].\[Epsilon]2 == Inverse[\[Epsilon]2].Conjugate[-T[a]].\[Epsilon]2 == T[a], {a,3}]


Table[Tr[\[Tau][a].\[Tau][b]] == \[Delta][a,b]/2,{a,8},{b,8}] // And@@Flatten[#]&
Table[\[Tau][a].\[Tau][b]-\[Tau][b].\[Tau][a] == I Sum[f[a,b,c] \[Tau][c], {c,8}], {a,8},{b,8}] // And@@Flatten[#]&
Table[
    Sum[f[a,d,e]f[b,c,d]+f[b,d,e]f[c,a,d]+f[c,d,e]f[a,b,d], {d,8}]==0,
    {a,8},{b,8},{c,8},{e,8}] // And@@Flatten[#]&
Do[If[f[a,b,c]!=0,Print[{a,b,c,f[a,b,c]}]], {a,8}, {b,a,8}, {c,b,8}]
Table[Sum[\[Tau][a][[i,j]]\[Tau][a][[k,l]],{a,8}] == (1/2)(\[Delta][i,l]\[Delta][j,k]-\[Delta][i,j]\[Delta][k,l]/3), {i,3}, {j,3}, {k,3}, {l,3}] // And@@Flatten[#]&






