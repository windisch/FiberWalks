newPackage("FiberWalks",
	Version => "0.2",
	Date => "Februar 2016",
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
    "compressedFiberGraph",
    "adaptedMoves",
    "convertMoves",
    "areIsomorphic",
    "findConnectingPath",
    "countEdgeDisjointPaths",
    "characteristicPolynomial",
    "hammingDistance",
    "getHemmeckeMatrix",
    "listDegSequences",

    --properties
    "conductance",
    "fiberDimensionOne",
    "isSetOfDirections",

    --transistion matrices
    "simpleFiberWalk",
    "simpleWalk",
    "metropolisHastingsWalk",
    "heatBath",
    "slem",
    "mixingTime",
    "approxFiberMixing",

    --miscellaneous
    "linearSpan",
    "isMultiple",

    --options
    "Directed",
    "ReturnSet",
    "Distribution",
    "Stationary",
    "Size",
    "TermOrder",
    "Verbose"
}

--variable for polynomial ring
xx:=vars(23);

--TODOs: 
--make final distribution an argument in metropolisHastingsWalk
--datatypes are not working

Fiber = new Type of List
FiberGraph = new Type of Graph

--TODO: Move to graphs package?
conductance = method()
conductance (Matrix) := QQ => (P) ->(
--computes conductance if stationary distribution is uniform
n:=numRows(P);
c:=n;
N:=toList(0..n-1);
M:={};
for i in 1..floor(n/2) do (
    << i << endl;
    for S in subsets(n,i) do (
        T:=1/i*sum flatten for s in S list for t in toList(set(N)-set(S)) list P_(s,t);
        c=min(T,c);
        if T==c then M=S;
        );       
    );
return (c,M);
);

isSetOfDirections = method()
isSetOfDirections (List) := Boolean => (M) -> (
--checks whether a set of moves is a set of directions
for a in subsets(M,2) do(
    if isMultiple(a_0,a_1) then return false
    );
return true;
);

isMultiple = method()
isMultiple (ZZ,ZZ) := Boolean => (u,v) -> (isMultiple(matrix({{u}}),matrix({{v}})))
isMultiple (Matrix,Matrix) := Boolean => (u,v) -> (
--checks whether there is an integer k such that u=kv or v=ku
A:=u|v;
if dim(kernel A)==1 then (
   s:=(syz(u|v))_0;
   i:=abs(s_0);
   j:=abs(s_1);
   if gcd(i,j)==min(i,j) then return true;
   );
return false;

);

fiberDimensionOne = method()
fiberDimensionOne (Graph) := Boolean => (G) -> (
n:=#(vertexSet(G));
F:=toList(1..n);
S:=toList(1..n-1);
for M in subsets S do(
      div:=0;
      for a in subsets(M,2) do(
       i:=max(a);
	    j:=min(a);
	    if gcd(i,j)==j then div=1;
      );
      if div==0 then(
      	 if areIsomorphic(G,fiberGraph(F,M)) then return true;
	 );
);
return false;
);
fiberDimensionOne (List) := Boolean => (degs) -> (
--n:=#(vertexSet(G));
n:=#degs;
F:=toList(1..n);
S:=toList(1..n-1);
for M in subsets S do (
      if isSetOfDirections(M) then (
      H:=fiberGraph(F,M);
      if isConnected(H) then (
            D:=sort for v in vertexSet(H) list degree(H,v);
            if D==degs then (
               print D;
               );
       );

	 );
);
return false;
);

listDegSequences = method()
listDegSequences (ZZ) := List => (n) -> (
S:=toList(1..n-1);
F:=toList(1..n);
D:={};
for M in subsets S do (
    if isSetOfDirections(M) then (
      H:=fiberGraph(F,M);
      D=D|{sort for v in vertexSet(H) list degree(H,v)};
      );
    );
return unique D;
);


--TODO: Move this method to a suitable package
characteristicPolynomial = method()
characteristicPolynomial (Matrix) := RingElement => (A) -> (
if numRows(A)!=numColumns(A) then return false;
R:=QQ[vars(0)];
n:=numRows(A);
A=substitute(A,R);
I:=id_(R^n);
return det(R_0*I-A);
);

hammingDistance = method()
hammingDistance (Matrix,Matrix) := ZZ => (A,B) -> (
return sum for a in flatten entries(A-B) list if a!= 0 then 1 else 0;
);

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

areIsomorphic = method()
areIsomorphic (Graph,Graph) := Boolean => (G,H) -> (
AG:=adjacencyMatrix(G);
AH:=adjacencyMatrix(H);
n:=#(vertexSet(G));
for P in permutations toList(0..(n-1)) do (
--relabeling G
   if (AG_P)^P==AH then return true
    );
return false;
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
      return graph(F,ee);
   );
);

compressedFiberGraph = method()
compressedFiberGraph (Matrix,Matrix,List) := FiberGraph => (A,b,M) -> (
G:=fiberGraph(A,b,M);
V:=vertexSet G;
for v in V do (
    for m in M do (
         l:=deepestDecent(v,-m);
         u:=deepestDecent(v,m);
         for i in 1..l do G=addEdge(G,set{v,v-i*m});
         for i in 1..u do G=addEdge(G,set{v,v+i*m});
       );
    );
return G;
);



deepestDecent = method()
deepestDecent (Matrix,Matrix) := ZZ => (v,m) -> (
d:=numRows(v);
return floor min for j in 0..(d-1) list if m_(j,0)<0 then -v_(j,0)/m_(j,0) else continue;
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

convertMoves = method()
convertMoves (Matrix) := List => (M) -> (
return for m in entries M list matrix vector m;
);

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

linearSpan = method ()
linearSpan (List) := Module => (L) -> (
return image transpose matrix apply(L,l->flatten entries l);
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

heatBath = method()
heatBath (Polyhedron,List) := Matrix => (P,M) -> (heatBath(latticePoints P,M))
heatBath (List,List) := Matrix => (F,M) -> (
-- F: sample space
-- M: Markov basis
--TODO: remove multiples from Markov basis
--TODO: allow density functions on M
n:=#F;
k:=#M;
P:=mutableMatrix(QQ,n,n);

for i in 0..(n-1) do (
    for m in M do (
      J:=for j in 0..(n-1) list if (F_i-F_j) % image(m) == 0 then j else continue;
      for j in J do if i!=j then P_(i,j)=(1/k)*1/(#J) else continue;
--find vertices that are adjacent to i along m
       );
      );
--write rejection probabilities
for i in 0..(n-1) do P_(i,i)=1-sum(for j in 0..(n-1) list P_(i,j));
return matrix(P);
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

approxFiberMixing = method()
approxFiberMixing (Matrix,Matrix,List) := ZZ => (A,u,M) -> (
--count the fiber
n:=#fiber(A,A*u);
--make moves symmetric
M=toList(set(M)+set(-M));
nM:=#M;
--observed tables
T:=new MutableHashTable;
--set counter
i:=1;

while true do (
--keep track of tables
    if T#?u then T#u=T#u+1 else T#u=1; 
--compute distance to uniform distribution
e:=1/2*(sum for v in values(T) list abs(v/i-1/n))+1/2*(n-#values(T))/n;
if e<1/4 then return i;

--get proposal
    m:=M_(random(1,nM)-1);     
    if all(flatten entries(u+m),k -> k>=0) then (
        u=u+m;
        );

    i=i+1;
    );
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
     Key => {approxFiberMixing,
     (approxFiberMixing,Matrix,Matrix,List)},
     Headline => "Mixing time of fiber walks",
     Usage => "approxFiberMixing(A,u,M)",
     Inputs => {
          "A" => { "a Matrix"},
          "u" => { "a Matrix"},
          "M" => { "a List"}},
     Outputs => {
          {"the number of steps needed to get a sample from the fiber with
          respect to a probability density function that has total variance
          distance to the uniform distribution at most 1/4"} },
     EXAMPLE {
          "A=matrix({{1,1,1,1}})",
          "b=matrix({{2}})",
          "M=toricMarkov(A)",
          "simpleFiberWalk(A,b,M)"
          },
     SeeAlso => {mixingTime}}

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
