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
    --fiber graphs
    expansion,
    getFiber,
    getFiberGraph,
    getHemmeckeMatrix,
    adaptedMoves,

    --transistion matrices
    simpleFiberWalk,
    simpleWalk,
    metropolisHastingsWalk,
    slem,

    --options
    ReturnSet
}

--variable for polynomial ring
xx:=vars(23);

--TODOs: 
--Move method expansion to Graphs.m2
--Write documentation
--Implement checks

expansion = method (Options => {ReturnSet => false,Verbose=>false})
expansion Graph := ZZ => opts -> G -> (
V:=set(vertexSet(G));
E:=edges(G);
--return 0 if graph is empty graph
if #E==0 then return 0;

n:=floor((#V)/2);
--CS:={};
RS:={};
qq:=0;
ee:=degree(G,(toList(V))_0);

for i in 1..n do (
    if opts.Verbose then << i << "/" << n << endl;
    for S in subsets(V,i) do (
        CS:=V-S;
        qq:=sum for e in edges(G) list if #(e*S)>0 and #(e*CS)>0 then 1 else 0;
        ee=min(ee,qq/#S);
        if(ee == qq) then RS=S;
        );
    );
if opts.ReturnSet then return (ee,RS) else return ee;
);

adaptedMoves = method()
adaptedMoves (Matrix,ZZ) := List => (M,r) -> (adaptedMoves(for m in entries M list matrix vector m,r));
adaptedMoves (List,ZZ) := List => (M,r) -> (
if #M===0 then return false;
M=transpose matrix for m in M list flatten entries m;
d:=numColumns(M);
P:=latticePoints crossPolytope(d,r);
return unique for p in P list M*p;
);

getFiber = method ()
getFiber (Matrix,ZZ) := List => (A,b) -> (getFiber(A,toList{b}));
getFiber (Matrix,List) := List => (A,b) -> (getFiber(A,vector b));
getFiber (Matrix,Vector) := List => (A,b) -> (getFiber(A,matrix b));
getFiber (Matrix,Matrix) := List => (A,b) -> (
d:=numColumns A;
if numRows(A)!=numRows(b) or numColumns(b)>1 then return false;
--identity matrix
I:=-map(ZZ^d); 
o:=matrix toList(d:{0});
P:=intersection(I,o,A,b);
LP:=latticePoints P;
return LP;
);

getFiberGraph = method ()
getFiberGraph (Matrix,Matrix,Matrix) := List => (A,b,M) -> (getFiberGraph(A,b,for m in entries M list matrix vector m));
getFiberGraph (Matrix,Matrix,List) := Graph => (A,b,M) -> (
fiber:=getFiber(A,b);
n:=#fiber;
AA:=mutableMatrix(ZZ,n,n);
for i in 0..n-1 do (
    for j in 0..n-1 do(
        if i == j then AA_(i,j)=0 else (
            if member(fiber_i-fiber_j,M) or
               member(fiber_j-fiber_i,M) then 
               AA_(i,j)=1 else
               AA_(i,j)=0;
            );
        );
    );
return graph(matrix AA);
);

getHemmeckeMatrix = method ()
getHemmeckeMatrix (ZZ) := Matrix => (k) -> (
I:=map(ZZ^k);
O:=reshape(ZZ^k,ZZ^k,matrix 0_(ZZ^(k*k)));
i:=matrix toList(k:{-1});
o:=matrix toList(k:{0});
ll:=matrix({toList((4*k):0)|{1,1}});
A:=(I|I|O|O|i|o)||(O|O|I|I|o|i)||ll;
return A;

);

----------------------------------
---- TRANSITION MATRICES  --------
----------------------------------

simpleFiberWalk = method ()
simpleFiberWalk (Matrix,Matrix,Matrix) := Matrix => (A,b,M) -> (simpleFiberWalk(A,b,for m in entries M list matrix vector m));
simpleFiberWalk (Matrix,Matrix,List) := Matrix => (A,b,M) -> (
P:=mutableMatrix(adjacencyMatrix(getFiberGraph(A,b,M))**QQ);
D:=#(set(M)+set(-M));
for i in 0..numRows(P)-1 do (
   deg:=sum flatten entries P^{i};
   P_(i,i)=(D-deg)/D;
   for j in 0..numColumns(P)-1 do if j!=i then P_(i,j)=P_(i,j)*1/D;
    );
return matrix P;
);

simpleWalk = method()
simpleWalk (Matrix,Matrix,Matrix) := Matrix => (A,b,M) -> (simpleWalk(getFiberGraph(A,b,M)));
simpleWalk (Graph) := Matrix => (G) -> (
n:=#(vertexSet G);
P:=mutableMatrix(adjacencyMatrix(G)**QQ);
for i in 0..n-1 do (
   deg:=sum flatten entries P^{i};
   for j in 0..n-1 do if j!=i then P_(i,j)=P_(i,j)*1/deg;
    );
return matrix P;
);

metropolisHastingsWalk = method()
metropolisHastingsWalk (Matrix,Matrix,Matrix) := Matrix => (A,b,M) ->(metropolisHastingsWalk(getFiberGraph(A,b,M)));
metropolisHastingsWalk (Graph) := Matrix => (G) -> (
n:=#(vertexSet G);
A:=adjacencyMatrix(G);
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



-- Tests --

TEST ///
--test expansion of graphs
G=graph({{1,2},{2,3},{3,1}});
assert(expansion(G)===2);
///

end
