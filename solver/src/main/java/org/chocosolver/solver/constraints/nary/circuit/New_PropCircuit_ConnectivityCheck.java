package org.chocosolver.solver.constraints.nary.circuit;

import org.chocosolver.solver.constraints.Propagator;
import org.chocosolver.solver.constraints.PropagatorPriority;
import org.chocosolver.solver.exception.ContradictionException;
import org.chocosolver.solver.variables.IntVar;
import org.chocosolver.util.ESat;

import java.util.Arrays;

import static org.chocosolver.util.tools.ArrayUtils.append;


/**
 * Propagator for circuit constraint checking that the directed graph is strongly connected
 * and that the undirected graph is 2-vertex-connected (2-vertex-connectivity implies 2-edge-connectivity).
 *
 * Graphs are implicitly derived from domains.
 *
 * This propagator runs in O(n + m) time per call.
 *
 * @author Sulian Le Bozec-Chiffoleau
 */
public final class New_PropCircuit_ConnectivityCheck extends Propagator<IntVar> {

    private final IntVar[] succ;
    private final IntVar[] pred;

    private final int n;
    private final int offsetSucc;
    private final int offsetPred;
    private final int[] index;
    private final int[] lowlink;
    private final boolean[] visited;
    private int time;
    private final int[] parent;

    public New_PropCircuit_ConnectivityCheck(IntVar[] succ, int offsetSucc, IntVar[] pred, int offsetPred) {
        super(append(succ, pred), PropagatorPriority.LINEAR, false);
        this.succ = succ;
        this.pred = pred;
        this.n = succ.length;
        this.offsetSucc = offsetSucc;
        this.offsetPred = offsetPred;
        this.index = new int[n];
        this.lowlink = new int[n];
        this.parent = new int[n];
        this.visited = new boolean[n];
    }

    @Override
    public ESat isEntailed() {
        return ESat.TRUE;
    }

    @Override
    public void propagate(int evtmask) throws ContradictionException {
        checkStrongConnectivity();
        check2VertexConnectivity();
    }

    //=========================================================================
    // Strong Connectivity
    //=========================================================================

    private void checkStrongConnectivity() throws ContradictionException {
        Arrays.fill(visited, false);
        time = 0;
        // Run a single DFS from the root 0
        directedDFS(0);
        if (time < n) {fails();} // All vertices could not be reached by a single DFS
    }

    private void directedDFS(int u) throws ContradictionException {
        visited[u] = true;
        index[u] = time;
        lowlink[u] = time;
        time++;
        IntVar var = succ[u];
        int ub = var.getUB();
        for (int val = var.getLB(); val <= ub; val = var.nextValue(val)) {
            int v = val - offsetSucc;
            if (!visited[v]) {
                directedDFS(v);
                lowlink[u] = Math.min(lowlink[u], lowlink[v]);
            } else {
                lowlink[u] = Math.min(lowlink[u], index[v]);
            }
        }
        if (u != 0 && lowlink[u] == index[u]) {fails();} // An intermediary SCC has been discovered
    }

    //=========================================================================
    // 2-Vertex Connectivity
    //=========================================================================

    private void check2VertexConnectivity() throws ContradictionException {
        Arrays.fill(visited, false);
        time = 0;
        // Run a single DFS from the first child of the root 0
        visited[0] = true;
        index[0] = time;
        lowlink[0] = time;
        time++;
        int firstChild = succ[0].getLB() - offsetSucc;
        parent[firstChild] = 0;
        undirectedDFS(firstChild);
        if (time < n) {fails();} // The root 0 is an articulation point
    }

    private void undirectedDFS(int u) throws ContradictionException {
        visited[u] = true;
        index[u] = time;
        lowlink[u] = time;
        time++;
        // neighbours = successors U predecessors
        explore(u, succ, offsetSucc);
        explore(u, pred, offsetPred);
    }

    private void explore(int u, IntVar[] neighbours, int offset) throws ContradictionException {
        int ub = neighbours[u].getUB();
        for (int val = neighbours[u].getLB(); val <= ub; val = neighbours[u].nextValue(val)) {
            int v = val - offset;
            if (!visited[v]) {
                parent[v] = u;
                undirectedDFS(v);
                if (u != 0 && lowlink[v] >= index[u]) {fails();} // u is an articulation point
                lowlink[u] = Math.min(lowlink[u], lowlink[v]);
            } else if (v != parent[u]) {
                lowlink[u] = Math.min(lowlink[u], index[v]);
            }
        }
    }
}