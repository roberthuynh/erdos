# For each T1 instance (Y, ab, cd): Z = Y - ab - cd, X = Z + v with N(v) = {a,b,c,d}; print "g6(X) v".
import sys
import networkx as nx
for line in open(sys.argv[1]):
    f = line.split()
    Y = nx.from_graph6_bytes(f[0].encode())
    a, b, c, d = map(int, f[1:5])
    Z = Y.copy(); Z.remove_edge(a, b); Z.remove_edge(c, d)
    X = Z.copy(); v = Y.number_of_nodes(); X.add_edges_from([(v, a), (v, b), (v, c), (v, d)])
    degs = [X.degree(u) for u in X]
    print(nx.to_graph6_bytes(X, header=False).decode().strip(), v,
          file=sys.stdout)
    print("n=%d e=%d 3n-4=%d maxdeg=%d" % (X.number_of_nodes(), X.number_of_edges(), 3*X.number_of_nodes()-4, max(degs)), file=sys.stderr)
