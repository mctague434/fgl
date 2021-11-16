(* ::Package:: *)

p=2; gen=Araki; gen=Hazewinkel;


BPl[0,_.,_.,_.] = 1;
BPl[n_Integer,k:(_Integer|Infinity):Infinity] := BPl[n,k,p,gen];
BPl[n_Integer,k:(_Integer|Infinity),p_Integer,gen_Symbol] := BPl[n,k,p,gen] =
  Simplify[1/(p-If[gen===Araki,p^p^n,0])
    Sum[BPl[i,k,p,gen] Subscript[v,n-i]^p^i, {i,Max[n-k,0],n-1}] /. Subscript[v,0]->p ];
logBP[ord_Integer,k:(_Integer|Infinity):Infinity] := logBP[ord,k,p,gen];
logBP[ord_Integer,k_,p_Integer,gen_Symbol] := logBP[ord,k,p,gen] =
  Function[d,Evaluate[Sum[BPl[n,k,p,gen] d^p^n, {n, 0, Log[p, ord]}] + O[d]^ord]];
expBP[ord_Integer,k:(_Integer|Infinity):Infinity] := expBP[ord,k,p,gen];
expBP[ord_Integer,k_,p_Integer,gen_Symbol] := expBP[ord,k,p,gen] =
  Function[d,Evaluate[Map[Simplify,InverseSeries[logBP[ord,k,p,gen][d]],{2}]]];
fglBP[ord_Integer,k:(_Integer|Infinity):Infinity,d_Symbol:d] := fglBP[ord,k,d,p,gen];
fglBP[ord_Integer,k_,d_Symbol,p_Integer,gen_Symbol] :=
  fglBP[ord,k,d,p,gen]=Function[{x,y},Evaluate[Module[{z}, Map[Expand, 
     ComposeSeries[expBP[ord,k,p,gen][d],
       ComposeSeries[logBP[ord,k,p,gen][z],x d+O[d]^ord] +
       ComposeSeries[logBP[ord,k,p,gen][z],y d+O[d]^ord]], {2}]]]];
pSerBP[ord_Integer,k:(_Integer|Infinity):Infinity,d_Symbol:d]:=pSerBP[ord,k,d,p,gen];
pSerBP[ord_Integer,k_,d_Symbol,p_Integer,gen_Symbol][x_] :=
  Module[{z}, With[{xPlus=(Normal[fglBP[ord,k,d,p,gen][x,z]]/.d->1)+O[z]^ord},
    Map[Expand,Nest[ComposeSeries[xPlus,#]&,x+O[x]^ord,p-1],{2}]]];


vI[I_List] := vI[I,p]; vI[{},_] = 1;
vI[I_List,p_Integer] := vI[I,p] =
  Subscript[v, First[I]] vI[Rest[I]]^p^First[I] /. Subscript[v,0]->p;
II[I_List] := II[I,p]; II[n_Integer,p_Integer] := II[n,p]=p-p^p^n;
II[{},_]=1; II[I_List,p_Integer] := II[I,p]=II[Plus@@I,p]II[Most[I],p];


w[K_List,nvars_Integer] := w[K,nvars,p,gen];
w[{},_,_,_][vars__] := Plus[vars];
w[K_List,nvars_Integer,p_Integer,gen_Symbol] :=
  With[{slotvars = Slot/@Range[1,nvars]},
  With[{formula  = 1/If[gen===Hazewinkel, p^Length[K], II[K]]
    (Plus@@(#^p^(Plus@@K) & /@ slotvars)
     - Plus@@(Function[j,With[{I=Drop[K,-j],J=Take[K,-j]},
               If[gen===Hazewinkel, p^Length[J], II[K]/II[I]]
               w[J,nvars,p,gen][Sequence@@slotvars]^p^(Plus@@I)]]
	         /@ Range[0,Length[K]-1]))},
      w[K,nvars,p,gen]=formula&; formula& ]];


BPSumSimplify[ord_Integer,k:(_Integer|Infinity):Infinity,d_Symbol:d] :=
  BPSumSimplify[ord,k,d,p,gen];
BPSumSimplify[ord_Integer,k:(_Integer|Infinity),
	      d_Symbol,p_Integer,gen_Symbol][terms_List] :=
  With[{mintermvord = Min[Exponent[#,d,Min]& /@ terms]},
    Cases[
     Map[Simplify, vI[#] d^(2(p^(Plus@@#)-1))
                   (w[#,Length[terms],p,gen]@@terms) + O[d]^ord, {2}]& /@
           Flatten[Permutations/@IntegerPartitions[#,All,Range[1,Min[k,#]]]&/@
                                     Range[0,Log[p,(1+ord)/(2+mintermvord)]],2],
     Except[O[d]^ord]]];


BPSumToOrder[ord_Integer,k:(_Integer|Infinity):Infinity,d_Symbol:d] :=
       BPSumToOrder[ord,k,d,p,gen];
BPSumToOrder[ord_Integer,k:(_Integer|Infinity),
	     d_Symbol,p_Integer,gen_Symbol][terms__] :=
  Map[Expand,First[NestWhile[BPSumSimplify[ord,k,d,p,gen], {terms},
			     Length[#]>1&],{2}]];


pSeriesBP[ord_Integer,k:(_Integer|Infinity):Infinity,d_Symbol:d] :=
  pSeriesBP[ord,k,d,p,gen];
pSeriesBP[ord_Integer,k:(_Integer|Infinity),
	  d_Symbol,p_Integer,gen_Symbol][x_] :=
  BPSumToOrder[ord,k,d,p,gen]@@Table[x, p];
