#!/usr/bin/env wolframscript
(* ::Package:: *)

$Assumptions = {vsq > 0, \[Mu]sq > 0, tb > 0, mZsq > 0, gZ>0, b>0, POS>0};
potential = (\[Mu]sq + mHu2)HuZ^2 + (\[Mu]sq + mHd2)HdZ^2 - 2b HuZ HdZ + (gZ^2/8)(HuZ^2-HdZ^2)^2;


simplified = potential //. {HuZ -> Sqrt[vsq]Sin[\[Beta]], HdZ -> Sqrt[vsq]Cos[\[Beta]], \[Beta]->ArcTan[tb], vsq->2mZsq/gZ^2} // FullSimplify


eqs = {D[simplified, tb]==0, D[simplified, mZsq]==0}//FullSimplify
tanbetas = Eliminate[eqs, mZsq]//FullSimplify//Solve[#,tb]&//FullSimplify


mZsq1 = ((Solve[#, mZsq] //. tanbetas[[1]])&/@eqs) // Flatten // FullSimplify // DeleteDuplicates
mZsq2 = ((Solve[#, mZsq] //. tanbetas[[2]])&/@eqs) // Flatten // FullSimplify // DeleteDuplicates


sol1 = Flatten[{tanbetas[[1]], mZsq1}] // FullSimplify
sol2 = Flatten[{tanbetas[[2]], mZsq2}] // FullSimplify
eqs //. sol1 // FullSimplify
eqs //. sol2 // FullSimplify
sol1 /. \[Mu]sq->(B-mHu2-mHd2)/2 // FullSimplify // Together
sol2 /. \[Mu]sq->(B-mHu2-mHd2)/2 // FullSimplify // Together


Sin[2\[Beta]]/.\[Beta]->ArcTan[tb]/.{sol1, sol2} // FullSimplify
TrigExpand[Cos[2\[Beta]]/.\[Beta]->ArcTan[tb]]/.{sol1, sol2} // FullSimplify


(mZsq/.sol1[[2]]) == -mHd2-mHu2-2 \[Mu]sq+(-mHd2+mHu2)/Cos2\[Beta] /.Cos2\[Beta]->(Cos[2\[Beta]]/.\[Beta]->ArcTan[tb]/.sol1[[1]])//FullSimplify
(mZsq/.sol2[[2]]) == -mHd2-mHu2-2 \[Mu]sq+(-mHd2+mHu2)/Cos2\[Beta] /.Cos2\[Beta]->(Cos[2\[Beta]]/.\[Beta]->ArcTan[tb]/.sol2[[1]])//FullSimplify



