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
    "getHemmeckeMatrix",
    "adaptedMoves",
    "convertMoves",

    --properties
    "isEdgeClosed",

    --transistion matrices
    "simpleFiberWalk",
    "simpleWalk",
    "metropolisHastingsWalk",
    "slem",
    "mixingTime",

    --options
    "ReturnSet",
    "Directed",
    "TermOrder",
    "Stationary",
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
if (matrix(toList{d:{1}})**QQ) % image(transpose(A)**QQ)!=0 then (
   << "Fiber not finite" << endl;
   return false;
   );
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

isEdgeClosed = method()
isEdgeClosed (Matrix,Matrix) := Boolean => (A,M) -> (
return true;
);

convertMoves = method()
convertMoves (Matrix) := List => (M) -> (
return for m in entries M list matrix vector m;
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



end
