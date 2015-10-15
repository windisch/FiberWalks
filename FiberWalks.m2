newPackage("FiberWalks",
	Version => "0.1",
	Date => "May 2015",
	Authors => {
     {Name => "Tobias Windisch",
      Email => "windisch@ovgu.de",
      HomePage => "http://www.uni-magdeburg.de/windisch/"}},
   Headline => "Package for analysing fiber graphs",
	Configuration => {},
   PackageImports => {"Graphs","Polyhedra"},
	Reload=>true
	)

export {
    --Datatypes
    "Fiber",
    "FiberGraph",

    --fiber graphs
    "fiber",
    "fiberGraph",
    "fiberDegree",
    "fiberConstant",
    "fiberDegrees",
    "fiberMoves",
    "fiberNeighborhoods",
    "getHemmeckeMatrix",
--    "minDegAtVertex",
    "adaptedMoves",
    "convertMoves",
    "hypergeometric",
    "moveGraph",
    "findConnectingPath",
    "countEdgeDisjointPaths",
    "enumerateNeighborlyTrees",

    --properties
    "edgeCon",
    "phi",
    "vectorSupport",

    --transistion matrices
    "simpleFiberWalk",
    "scaledSimpleFiberWalk",
    "simpleWalk",
    "metropolisHastingsWalk",
    "slem",
    "mixingTime",

    --options
    "Directed",
    "fiberNeighborhood",
    "ReturnSet",
    "Stationary",
    "Size",
    "TermOrder",
    "Verbose",
    "Distribution"
}

--variable for polynomial ring
xx:=vars(23);

--TODOs: 
--make final distribution an argument in metropolisHastingsWalk
--datatypes are not working

Fiber = new Type of List
FiberGraph = new Type of Graph

adaptedMoves = method()
adaptedMoves (Matrix,ZZ) := List => (M,r) -> (adaptedMoves(convertMoves(M),r));
adaptedMoves (List,ZZ) := List => (M,r) -> (
if #M===0 then return false;
M=transpose matrix for m in M list flatten entries m;
d:=numColumns(M);
P:=latticePoints crossPolytope(d,r);
return unique for p in P list M*p;
);

fiber = method ()
fiber (Matrix,ZZ) := Fiber => (A,b) -> (fiber(A,toList{b}));
fiber (Matrix,List) := Fiber => (A,b) -> (fiber(A,vector b));
fiber (Matrix,Vector) := Fiber => (A,b) -> (fiber(A,matrix b));
fiber (Matrix,Matrix) := Fiber => (A,b) -> (
d:=numColumns A;
if numRows(A)!=numRows(b) or numColumns(b)>1 then return false;
--check whether fiber finite
--if (matrix(toList{d:{1}})**QQ) % image(transpose(A)**QQ)!=0 then (
--   << "Fiber not finite" << endl;
--   return false;
--   );
--identity matrix
I:=-map(ZZ^d); 
o:=matrix toList(d:{0});
P:=intersection(I,o,A,b);
LP:=latticePoints P;
return LP;
);

fiberGraph = method (Options => {Directed => false,TermOrder=>Lex})
fiberGraph (Matrix,Matrix,Matrix) := FiberGraph => opts -> (A,b,M) -> (fiberGraph(A,b,convertMoves(M),opts));
fiberGraph (Matrix,Matrix,List) := FiberGraph => opts -> (A,b,M) -> (fiberGraph(fiber(A,b),M,opts));
fiberGraph (List,Matrix) := FiberGraph => opts -> (F,M) ->(fiberGraph(F,convertMoves(M),opts));
fiberGraph (List,List) := FiberGraph => opts -> (F,M) -> (
n:=#F;
ee:={};
if opts.Directed then (
--directed fiber graphs
   if n==0 then return digraph({});
   d:=numRows(F_0);
   R:=QQ[for i in 0..(d-1) list xx_(i),MonomialOrder=>opts.TermOrder];
   for e in subsets(F,2) do (
      if member(e_0-e_1,M) or member (e_1-e_0,M) then (
         v1:=flatten entries e_0;
         v2:=flatten entries e_1;
         m1:=product(for i in 0..(d-1) list ((R_i)^(v1_i))_R);
         m2:=product(for i in 0..(d-1) list ((R_i)^(v2_i))_R);
         if (m1)_R>(m2)_R then ee=ee|{{e_0,e_1}} else ee=ee|{{e_1,e_0}};
         ); 
      );
      return digraph(ee);
   ) else (
--undirected fiber graphs
   for e in subsets(F,2) do (
      if member(e_0-e_1,M) or member (e_1-e_0,M) then (
         ee=ee|{e}; 
         );
      ); 
      return graph(ee);
   );
);

phi = method(Options => {Verbose => false})
phi (Matrix,Matrix,List,ZZ) := ZZ => opts -> (A,M,N,d) -> (phi(A,convertMoves(M),N,d,opts));
phi (Matrix,List,List,ZZ) := ZZ => opts -> (A,M,N,d) -> (
--computes phi_M(d)
--return min for G in N list if #G>= d then edgeCon(A,M,G) else continue;
k:={};
nN:=for G in N list if #G>=d then G else continue;
if opts.Verbose then (
   num:=nN;
   i:=1;
   );
for G in nN do (
    k=k|{edgeCon(A,M,G)}; 
    if opts.Verbose then (
       << i << "/" << num <<endl; 
       i=i+1;
        );
    );
return min k;
);

--TODO: remove dependence from A
edgeCon = method(Options => {Verbose => false})
edgeCon (Matrix,Matrix,Matrix) := ZZ => opts -> (A,M,G) -> (edgeCon(A,convertMoves(M),convertMoves(G),opts));
edgeCon (Matrix,Matrix,List) := ZZ => opts -> (A,M,G) -> (edgeCon(A,convertMoves(M),G,opts));
edgeCon (Matrix,List,Matrix) := ZZ => opts -> (A,M,G) -> (edgeCon(A,M,convertMoves(G),opts));
edgeCon (Matrix,List,List) := ZZ => opts -> (A,M,G) -> (
--computes kappa_M(G)
if opts.Verbose then (<< "Compute move graph";);
F:=moveGraph(A,M,G);
if opts.Verbose then (<< "...done" <<endl;);
k:={};
if opts.Verbose then (
    n:=#G;
    i:=1;
    );
Z:=matrix toList(numColumns(A):{0});
--return max for g in G list countEdgeDisjointPaths(F,Z,g);
if opts.Verbose then (<< "Count edge-disjoint paths" << endl;);
for g in G do (
    if opts.Verbose then (
        << i << "/" << n << endl;
        i=i+1;
        );
    k=k|{countEdgeDisjointPaths(F,Z,g)}; 
    );
return min k;
);


fiberDegree = method ()
fiberDegree (Matrix,Matrix) := ZZ => (M,G) -> (fiberDegree(convertMoves(M),convertMoves(G)));
fiberDegree (Matrix,List) := ZZ => (M,G) -> (fiberDegree(convertMoves(M),G));
fiberDegree (List,Matrix) := ZZ => (M,G) -> (fiberDegree(M,convertMoves(G)));
fiberDegree (List,List) := ZZ => (M,G) -> (
d:=numRows first M;
--make M symmetric
M=unique(-M|M);
--construct N(G)
N:=mutableMatrix(ZZ,d,1);
for i in 0..(d-1) do (
   N_(i,0)=- max for g in G list if(g_(i,0)<0) then -g_(i,0) else 0;
	);
N=matrix N;
--compute fiber degree
fD:=0;
for m in M do (
--check whether m>= N
    if any(apply(flatten entries (m-N),i -> i <0),j->j===true)===false then fD=fD+1;
    );
return fD;
);

fiberConstant = method()
fiberConstant (Matrix) := Matrix => (G) -> (fiberConstant(convertMoves(G)));
fiberConstant (List) := Matrix => (G) -> (
d:=numRows first G;
N:=mutableMatrix(ZZ,d,1);
for i in 0..(d-1) do (
   N_(i,0)=- max for g in G list if(g_(i,0)<0) then -g_(i,0) else 0;
	);
return matrix N;
);

fiberDegrees = method (Options => {fiberNeighborhood => {}})
fiberDegrees (Matrix) := ZZ => opts -> (M) -> (fiberDegrees(convertMoves(M),opts));
fiberDegrees (List) := ZZ => opts -> (M) -> (
--returns all possible fiber degrees
fN:=opts.fiberNeighborhood;
--compute fiberNeighborhood if not provided in the arguments
if #fN==0 then (
   fN=fiberNeighborhoods(M);   
    );
return sort unique for G in fN list #G;
);

--minDegAtVertex = method();
--minDegAtVertex (Matrix,Matrix,List) := Boolean => (A,b,M) -> (
--F:=fiber(A,b);
--V:=for v in entries transpose vertices convexHull F list transpose lift(matrix({v}),ZZ);
--G:=fiberGraph(F,M);
--
--return minimalDegree G===min for v in V list degree(G,v)
----);

fiberMoves = method();
fiberMoves (Matrix,Matrix) := List => (M,N) -> (fiberMoves(convertMoves(M),N))
fiberMoves (List,Matrix) := List => (M,N) -> (
--make M symmetric
M=unique(-M|M);
return for g in M list if all(flatten entries(g+N),i-> i>=0) then g else continue;    
);

fiberNeighborhoods = method (Options => {Verbose =>false,Size=>-1})
fiberNeighborhoods (Matrix) := List => opts -> (M) -> (fiberNeighborhoods(convertMoves(M),opts));
fiberNeighborhoods (List) := List => opts -> (M) -> (
--make M symmetric
M=unique(-M|M);
fN:={{}};
--counter
--subsets to consider
P:={};
if opts.Size == -1 then (
    P=subsets(M);
    ) else (
--restrict computation on fixed i and delete P from memory afterwards
    P=subsets(M,opts.Size);
    );

if opts.Verbose then (
    num:=#P;
    i:=0;
    );

for MM in P do (
   if opts.Verbose then (
       if opts.Size !=-1 then (
           << opts.Size << ":" << "\t";
           );
      << i << "/" << num << endl; 
      i=i+1;
      );
   if #MM>0 then (
      if fiberDegree(M,MM) == #MM then fN=fN|{MM};       
       ); 
    );
return fN;
);

vectorSupport = method()
vectorSupport (Matrix) := List => (A) -> (
d:=numColumns(A);
r:=numRows(A);
return flatten for i in 0..(r-1) list for j in 0..(d-1) list if A_(i,j)!=0 then (i,j) else continue;
);

getHemmeckeMatrix = method ()
getHemmeckeMatrix (ZZ) := Matrix => (k) -> (
if k==0 then return matrix({{0}});
I:=map(ZZ^k);
O:=reshape(ZZ^k,ZZ^k,matrix 0_(ZZ^(k*k)));
i:=matrix toList(k:{-1});
o:=matrix toList(k:{0});
ll:=matrix({toList((4*k):0)|{1,1}});
A:=(I|I|O|O|i|o)||(O|O|I|I|o|i)||ll;
return A;
);

moveGraph = method ()
moveGraph (Matrix,Matrix) := FiberGraph => (M,G) -> (moveGraph(convertMoves(M),convertMoves(G)));
moveGraph (List,List) := FiberGraph => (M,G) -> (

o:=matrix toList(numRows(first G):{0});
fC:=fiberConstant(G);

--enumerate vertices
V:={};
tC:={o};

while(#tC>0) do (
    v:=first tC;
    tC=delete(v,tC);
    for g in M do (
       vnew:=v+g;
       if all(flatten entries(vnew-fC),i-> i>=0) === true then (
            if member(vnew,V) === false then (
               V=V|{vnew}; 
               tC=unique(tC|{vnew});
               );
            );
        );
    );
return fiberGraph(V,M); 
);

----TODO: remove dependence of A
--moveGraph = method()
--moveGraph (Matrix,Matrix,Matrix) := FiberGraph => (A,M,G) -> (moveGraph(A,convertMoves(M),convertMoves(G)));
--moveGraph (Matrix,List,List) := FiberGraph => (A,M,G)-> (
--d:=numColumns A;
--I:=-map(ZZ^d); 
--o:=matrix toList(numRows(A):{0});
--Z:=matrix toList(numColumns(A):{0});
--
----construct N(G)
--N:=mutableMatrix(ZZ,d,1);
--for i in 0..(d-1) do (
--   N_(i,0)=max for g in G list if(g_(i,0)<0) then -g_(i,0) else 0;
--	);
--
----construct F_M(G)
--P:=intersection(I,matrix N,A,o);
--LP:=latticePoints P;
--F:=fiberGraph(LP,M);
----A priori, F is not connected (right?). Hence, return this connected
----component of F which contains 0
--cc:=connectedComponents(F);
--for c in cc do (
--   if member(Z,set c) then return inducedSubgraph(F,c);
--   );
--);

convertMoves = method()
convertMoves (Matrix) := List => (M) -> (
return for m in entries M list matrix vector m;
);

--TODO: Move this method to Graphs
--enumerateNeighborlyTrees = method()
--enumerateNeighborlyTrees (ZZ) := List => (n) -> (
--computes (up to symmetry) all neighborly trees
--on n edges
--tree on n edges has n+1 vertices
--V:=toList(0..n);
--T:={};
--for E in subsets(subsets(V,2),n) do (
--    G:=graph(E);
--    if isTree(G) then (
--       if isNeighborly(G) then (
--          T=T|{G};           
--           );
--        );  
--    );
--return T;
--);

--TODO: Move this method to Graphs (implement Dijkstra maybe)
findConnectingPath = method()
findConnectingPath (Graph,Thing,Thing) := List => (G,v,w) -> (
--return path (=list of vertices) where no vertex is used twice
FW:=floydWarshall(G);
--length of shortest path (no vertex is used twice)
d:=FW#(v,w);
if d == infinity then return {};
P:=findPaths(G,v,d);
for p in P do if last p === w then return p;
return false;
);

--TODO: Move this method to Graphs (implement dijkstra maybe)
countEdgeDisjointPaths = method()
countEdgeDisjointPaths (Graph,Thing,Thing) := ZZ => (G,v,w) -> (
P:=findConnectingPath(G,v,w);
n:=0;
while #P > 0 do (
    n=n+1;
--remove edges from G
    PE:=for i in 1..(#P-1) list {P_(i-1),P_(i)};
    G=deleteEdges(G,PE);
    P=findConnectingPath(G,v,w);
    );
return n;
);

----------------------------------
---- TRANSITION MATRICES  --------
----------------------------------

simpleFiberWalk = method ()
simpleFiberWalk (Matrix,Matrix,Matrix) := Matrix => (A,b,M) -> (simpleFiberWalk(A,b,convertMoves(M)));
simpleFiberWalk (Matrix,Matrix,List) := Matrix => (A,b,M) -> (
P:=mutableMatrix(adjacencyMatrix(fiberGraph(A,b,M))**QQ);
D:=#(set(M)+set(-M));
for i in 0..numRows(P)-1 do (
   deg:=sum flatten entries P^{i};
   P_(i,i)=(D-deg)/D;
   for j in 0..numColumns(P)-1 do if j!=i then P_(i,j)=P_(i,j)*1/D;
    );
return matrix P;
);

scaledSimpleFiberWalk = method ()
scaledSimpleFiberWalk (Matrix,Matrix,Matrix) := Matrix => (A,b,M) ->(scaledSimpleFiberWalk(A,b,convertMoves(M)));
scaledSimpleFiberWalk (Matrix,Matrix,List) := Matrix => (A,b,M) -> (

--TODO: remove multiples from Markov basis
F:=fiber(A,b);
d:=numColumns A;
n:=#F;
mm:=#M;
P:=mutableMatrix(QQ,n,n);
for i in 0..(n-1) do (
    v:=F_i;
    print v;
        for m in M do (
            print m;
            l:=floor max for j in 0..(d-1) list if m_(j,0)>0 then v_(j,0)/m_(j,0) else 0;
            u:=floor max for j in 0..(d-1) list if m_(j,0)<0 then -v_(j,0)/m_(j,0) else 0;

            for j in -l..u do (
                if j!=0 then (
                  k:=position(F,w->w==v+j*m);
                  P_(i,k)=1/mm*1/(l+u+1);
                     );
                );
        );
       P_(i,i)=1-sum flatten entries P^{i};
);
return matrix P;
);

hypergeometric = method()
hypergeometric (Matrix) := RR => (v) -> (
return  numeric(sum flatten entries v)!/(product for vv in flatten entries v list vv!)
);
hypergeometric (List) := HashTable => (F) -> (
--This returns the conditional hypergeometric distribution (which
--does not depend on parameters)
--all elements in F must have the same norm
p:=apply(F,f->{f,hypergeometric(f)});
c:=sum for f in p list f_1;
return apply(p, f-> {f_0,f_1/c});
);

simpleWalk = method()
--simpleWalk (Matrix,Matrix,Matrix) := Matrix => (A,b,M) -> (simpleWalk(fiberGraph(A,b,M)));
simpleWalk (Graph) := Matrix => (G) -> (
n:=#(vertexSet G);
P:=mutableMatrix(adjacencyMatrix(G)**QQ);
for i in 0..n-1 do (
   deg:=sum flatten entries P^{i};
   for j in 0..n-1 do if j!=i then P_(i,j)=P_(i,j)*1/deg;
    );
return matrix P;
);

metropolisHastingsWalk = method(Options => {Stationary =>
false,Distribution => false})
--metropolisHastingsWalk (Matrix,Matrix,Matrix) := Matrix => (A,b,M) ->(metropolisHastingsWalk(fiberGraph(A,b,M)));
metropolisHastingsWalk (Graph) := Matrix => opts -> (G) -> (
n:=#(vertexSet G);
A:=adjacencyMatrix(G);
p:=toList();
if opts.Stationary then (
    if sum(p)!=1 then (
        return false; 
        );
    p=opts.Distribution;
    
    );

P:=mutableMatrix(A**QQ);
	for i in 0..(n-1) do (
		for j in 0..(n-1) do (
			if i==j then (
				P_(i,i)=sum for k in 0..n-1 list A_(i,k)*max(0,(1/(sum flatten entries A_i))-(1/(sum flatten entries A_k)));

			) else (
				if A_(i,j)==1 then (
					P_(i,j)=min(1/(sum flatten entries A_i),1/(sum flatten entries A_j));	
				);
			);	
		);	
	);
return matrix P;
);

slem = method()
slem (Matrix) := RR => (P) -> ( 
return (rsort unique for v in eigenvalues P list abs v)_1;
);

mixingTime = method()
mixingTime (Matrix) := RR => (P) -> (return -1/log(slem(P)););

beginDocumentation()


document {
        Key => FiberWalks,
        Headline => "a package for random walks on fiber graphs",

        EM "FiberWalks", " is a package for random walks on fiber
        graphs",
	
	BR{},BR{},
	BOLD "Literature \n",
	UL {
	  LI {"[DS1998] ", EM "Algebraic algorithms for sampling from
     conditional distributions ", "(P. Diaconis, B. Sturmfels,
     1998).\n"}}}

document {
     Key => {fiber,
     (fiber,Matrix,ZZ),(fiber,Matrix,List),(fiber, Matrix,
     Vector),(fiber,Matrix,Matrix)},
     Headline => "Fiber of a matrix",
     Usage => "fiber(A,b)",
     Inputs => {
          "A" => { "a Matrix"},
          "b" => { "an element in ZZ, a List, a Vector or a Matrix"}},
     Outputs => {
          {"a List containing all elements of the fiber of A for the right-hand side b"} },
     EXAMPLE {
          "A=matrix({{1,0,-2},{1,1,1}})",
          "b=matrix({{2},{10}})",
          "fiber(A,b)"
          },
     SeeAlso => fiberGraph}

document {
     Key => {fiberGraph,
     (fiberGraph,Matrix,Matrix,Matrix),(fiberGraph,Matrix,Matrix,List),(fiberGraph,List,Matrix),(fiberGraph,List,List)},
     Headline => "Fiber graph of a matrix",
     Usage => "fiberGraph(A,b,M)",
     Inputs => {
          "A" => { "a Matrix"},
          "b" => { "a Matrix"},
          "M" => { "a Matrix or a List"}},
     Outputs => {
          {"the (directed) fiber graph of A with right-hand side b and allowed
          moves M"} },
     EXAMPLE {
          "needsPackage(\"FourTiTwo\")",
          "A=matrix({{1,0,-2},{1,1,1}})",
          "b=matrix({{2},{10}})",
          "M=toricMarkov(A)",
          "fiberGraph(A,b,M);",
          "fiberGraph(A,b,M,Directed=>true,TermOrder=>Lex)",
          "F=fiber(A,b)",
          "fiberGraph(F,M);"
          },
     SeeAlso => fiber}


document {
     Key => {convertMoves,
     (convertMoves,Matrix)},
     Headline => "Conversion of matrices containing Markov moves",
     Usage => "convertMoves(M)",
     Inputs => {
          "M" => { "a Matrix"}},
     Outputs => {
          {"A List consisting of the rows of M written as matrices"}},
     EXAMPLE {
          "needsPackage(\"FourTiTwo\")",
          "A=matrix({{1,1,1}})",
          "M=toricMarkov(A)",
          "convertMoves(M)"
          }}

document {
     Key => {simpleWalk,
     (simpleWalk,Graph)},
     Headline => "The simple walk",
     Usage => "simpleWalk(G)",
     Inputs => {
          "G" => { "a Graph"}},
     Outputs => {
          {"the transition matrix of the simple walk on G"} },
     EXAMPLE {
          "needsPackage(\"Graphs\")",
          "G=graph({{1,2},{2,3},{3,1}})",
          "simpleWalk(G)"
          },
     SeeAlso => {simpleFiberWalk,metropolisHastingsWalk}}

document {
     Key => {metropolisHastingsWalk,
     (metropolisHastingsWalk,Graph)},
     Headline => "The Metropolis-Hastings walk",
     Usage => "metropolisHastingsWalk(G)",
     Inputs => {
          "G" => { "a Graph"}},
     Outputs => {
          {"the transition matrix of the Metropolis-Hastings walk on G
          with uniform as stationary distribution"} },
     EXAMPLE {
          "needsPackage(\"Graphs\")",
          "G=graph({{1,2},{2,3},{3,1},{3,4}})",
          "metropolisHastingsWalk(G)"
          },
     SeeAlso => {simpleFiberWalk,simpleWalk}}

document {
     Key => {simpleFiberWalk,
     (simpleFiberWalk,Matrix,Matrix,Matrix),(simpleFiberWalk,Matrix,Matrix,List)},
     Headline => "The simple walk",
     Usage => "simpleFiberWalk(A,b,M)",
     Inputs => {
          "A" => { "a Matrix"},
          "b" => { "a Matrix"},
          "M" => { "a Matrix or a List"}},
     Outputs => {
          {"the transition matrix of the simple fiber walk on the
          fiber graph of A with right-hand side b and allowed moves M"} },
     EXAMPLE {
          "A=matrix({{1,1,1,1}})",
          "b=matrix({{2}})",
          "M=toricMarkov(A)",
          "simpleFiberWalk(A,b,M)"
          },
     SeeAlso => {simpleWalk,metropolisHastingsWalk}}

document {
     Key => {slem,
     (slem,Matrix)},
     Headline => "Second largest eigenvalue modulus",
     Usage => "slem(T)",
     Inputs => {
          "T" => { "a Matrix"}},
     Outputs => {
          {"the second largest eigenvalue modulus of the random walk
          corresponding to the transition matrix T"} },
     EXAMPLE {
          "needsPackage(\"Graphs\")",
          "G=graph({{1,2},{2,3},{3,1},{3,4}})",
          "T=simpleWalk(G);",
          "slem(T)"
          }}

document {
     Key => {mixingTime,
     (mixingTime,Matrix)},
     Headline => "Mixing time",
     Usage => "mixingTime(T)",
     Inputs => {
          "T" => { "a Matrix"}},
     Outputs => {
          {"the mixing time of the random walk
          corresponding to the transition matrix T"} },
     EXAMPLE {
          "needsPackage(\"Graphs\")",
          "G=graph({{1,2},{2,3},{3,1},{3,4}})",
          "T=simpleWalk(G);",
          "mixingTime(T)"
          }}

-- Tests --

TEST ///
--check creation of adapted moves
M=matrix({{1,-1,0},{1,0,-1}});
AM={
matrix({{-2},{2},{0}}),matrix({{-2},{1},{1}}),matrix({{-1},{1},{0}}),
matrix({{0},{1},{-1}}),matrix({{-2},{0},{2}}),matrix({{-1},{0},{1}}),
matrix({{0},{0},{0}}),matrix({{1},{0},{-1}}),matrix({{2},{0},{-2}}),
matrix({{0},{-1},{1}}),matrix({{1},{-1},{0}}),matrix({{2},{-1},{-1}}),
matrix({{2},{-2},{0}})}
assert(adaptedMoves(M,2)===AM);
///

TEST ///
--check fiber 
A=matrix({{1,1,1}});
F={
matrix {{3},{0},{0}},matrix({{2},{0},{1}}), 
matrix({{1},{0},{2}}),matrix({{0},{0},{3}}), 
matrix({{2},{1},{0}}),matrix({{1},{1},{1}}), 
matrix({{0},{1},{2}}),matrix({{1},{2},{0}}), 
matrix({{0},{2},{1}}),matrix({{0},{3},{0}})}
L={};
L=L|{fiber(A,3)};
L=L|{fiber(A,{3})};
L=L|{fiber(A,matrix({{3}}))};
L=L|{fiber(A,vector({3}))};
assert(all(L,S->S==F));
///

TEST ///
--check infinite fibers 
A=matrix({{1,-1}});
assert(fiber(A,1)===false);
///

TEST ///
--check conversion of moves
M=matrix({{1,-1,0},{1,0,-1}});
MM={matrix({{1},{-1},{0}}),matrix({{1},{0},{-1}})};
assert(convertMoves(M)===MM);
///

TEST /// 
G=graph({{1,2},{2,3},{1,3},{3,4},{3,5},{4,6},{5,6}});
assert(countEdgeDisjointPaths(G)===2);
///


end
