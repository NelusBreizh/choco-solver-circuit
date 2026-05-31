package org.chocosolver.solver.constraints.nary.circuit;

import org.chocosolver.solver.constraints.Propagator;
import org.chocosolver.solver.constraints.PropagatorPriority;
import org.chocosolver.solver.exception.ContradictionException;
import org.chocosolver.solver.variables.IntVar;

import java.util.Arrays;

public class New_PropCircuit_ReducedPath extends Propagator<IntVar> {
    private final int n;
    private final IntVar[] succ;
    private final IntVar[] pred;
    private final int offsetSucc;
    private final int offsetPred;
    // Split graph
    private int source;
    private int sink;
    // Tarjan's algorithm
    private final int[] pre;
    private final int[] low;
    private final int[] stack;
    private final boolean[] inStack;
    private final boolean[] visited;
    private int dfsTime;
    private int stackTop;
    // SCC storage
    private final int[] sccPartition;
    private final int[] sccIndices;
    private final int[] sccBelonging;
    private final int[] upToDateSCC;
    private int updateKey;
    private int numberOfSCCs;
    // Reduced path pruning
    private final int NOT_FOUND_YET = -1;
    private final int NOT_UNIQUE = -2;
    private final int[] entryNode;
    private final int[] exitNode;


    public New_PropCircuit_ReducedPath(IntVar[] succ, int offsetSucc, IntVar[] pred, int offsetPred) {
        super(succ, PropagatorPriority.QUADRATIC, false);
        this.succ = succ;
        this.pred = pred;
        this.offsetSucc = offsetSucc;
        this.offsetPred = offsetPred;
        this.n = succ.length;
        this.source = 0;
        this.sink = n;
        // Structures for Tarjan's algorithm
        this.pre = new int[n + 1];
        this.low = new int[n + 1];
        this.stack = new int[n + 1];
        this.inStack = new boolean[n + 1];
        this.visited = new boolean[n + 1];
        // Structures for SCC storage
        this.sccPartition = new int[n + 1];
        this.sccIndices = new int[n + 1];
        this.sccBelonging = new int[n + 1];
        this.upToDateSCC = new int[n + 1];
        this.updateKey = 0;
        this.numberOfSCCs = 0;
        // Structures for reduced path filtering
        this.entryNode = new int[n + 1];
        this.exitNode = new int[n + 1];
    }

    @Override
    public void propagate(int evtmask) throws ContradictionException {
        // ============= Reset the structures =============
        Arrays.fill(inStack, false);
        Arrays.fill(visited, false);
        dfsTime = 0;
        stackTop = 0;
        resetSCCs();
        // ============= Run DFS =============
        source = 0; // TODO replace later by heuristic or external choice
        dfs(source);
        // ============= Ad-hoc intra-SCC filtering rules =============
        IntVar varSucc;
        IntVar varPred;
        int valueSucc;
        int valuePred;
        int node;
        int ub;
        // The first and last SCCs are singletons so we can ignore them
        for (int scc = 1; scc < numberOfSCCs - 1; scc++) {
            // Prune the unique entry node's incoming arcs within the SCC
            if (hasUniqueEntryNode(scc) && getSizeSCC(scc) > 1) {
                varPred = getPredecessorsVarFromSplitGraphIndex(entryNode[scc]);
                valueSucc = getSuccessorsValueFromSplitGraphIndex(entryNode[scc]);
                ub = varPred.getUB();
                for (valuePred = varPred.getLB(); valuePred <= ub; valuePred = varPred.nextValue(valuePred)) {
                    node = getSplitGraphIndexFromPredecessorsValue(valuePred);
                    if (isInSCC(node, scc)) {
                        varPred.removeValue(valuePred, this);
                        varSucc = getSuccessorsVarFromSplitGraphIndex(node);
                        varSucc.removeValue(valueSucc, this);
                    }
                }
            }
            // Prune the unique exit node's outgoing arcs within the SCC
            if (hasUniqueExitNode(scc) && getSizeSCC(scc) > 1) {
                varSucc = getSuccessorsVarFromSplitGraphIndex(exitNode[scc]);
                valuePred = getPredecessorsValueFromSplitGraphIndex(exitNode[scc]);
                ub = varSucc.getUB();
                for (valueSucc = varSucc.getLB(); valueSucc <= ub; valueSucc = varSucc.nextValue(valueSucc)) {
                    node = getSplitGraphIndexFromSuccessorsValue(valueSucc);
                    if (isInSCC(node, scc)) {
                        varSucc.removeValue(valueSucc, this);
                        varPred = getPredecessorsVarFromSplitGraphIndex(node);
                        varPred.removeValue(valuePred, this);
                    }
                }
            }
            // Prune the arc from the unique entry to the unique exit if the SCC contains at least 3 nodes
            if (hasUniqueEntryNode(scc) && hasUniqueExitNode(scc) && getSizeSCC(scc) > 2) {
                getSuccessorsVarFromSplitGraphIndex(entryNode[scc]).removeValue(getSuccessorsValueFromSplitGraphIndex(exitNode[scc]), this);
                getPredecessorsVarFromSplitGraphIndex(exitNode[scc]).removeValue(getPredecessorsValueFromSplitGraphIndex(entryNode[scc]), this);
            }
        }
    }

    // =========================================================
    // TARJAN'S ALGORITHM IN THE SPLIT GRAPH
    // =========================================================

    private void dfs(int u) throws ContradictionException {
        pre[u] = dfsTime;
        low[u] = dfsTime;
        dfsTime++;
        stack[stackTop++] = u;
        inStack[u] = true;
        visited[u] = true;
        IntVar var = getSuccessorsVarFromSplitGraphIndex(u);
        if (var != null) {
            int ub = var.getUB();
            for (int val = var.getLB(); val <= ub; val = var.nextValue(val)) {
                int v = getSplitGraphIndexFromSuccessorsValue(val);
                if (!visited[v]) {
                    dfs(v);
                    low[u] = Math.min(low[u], low[v]);
                } else if (inStack[v]){
                    low[u] = Math.min(low[u], pre[v]);
                }
            }
        }
        if (pre[u] == low[u]) {
            processNewSCC(u);
        }
    }

    private void processNewSCC(int root) throws ContradictionException {
        int scc = newSCC();
        int node;
        exitNode[scc] = NOT_FOUND_YET;
        if (scc > 0) {entryNode[scc - 1] = NOT_FOUND_YET;}
        do {
            stackTop--;
            node = stack[stackTop];
            inStack[node] = false;
            addToSCC(node, scc);
            processNode(node, scc);
        } while (node != root && stackTop > 0);
        if (scc > 0 && entryNode[scc - 1] == NOT_FOUND_YET) {fails();} // There is no Hamiltonian path in the reduced graph
    }

    private void processNode(int node, int scc) throws ContradictionException {
        if (scc == 0) {return;}
        IntVar var = getSuccessorsVarFromSplitGraphIndex(node);
        int ub = var.getUB();
        for (int val = var.getLB(); val <= ub; val = var.nextValue(val)) {
            int v = getSplitGraphIndexFromSuccessorsValue(val);
            if (isInPreviousSCC(v, scc)) {
                exitNode[scc] = exitNode[scc] == NOT_FOUND_YET || exitNode[scc] == node  ? node : NOT_UNIQUE;
                entryNode[scc - 1] = entryNode[scc - 1] == NOT_FOUND_YET || entryNode[scc - 1] == v ? v : NOT_UNIQUE;
            }
            else if (isInEarlierSCC(v, scc)) {
                pruneSplitGraphArc(node, v);
            }
        }
    }

    private void pruneSplitGraphArc(int a, int b) throws ContradictionException {
        int i = getIndexFromSplitGraphIndex(a);
        int j = getIndexFromSplitGraphIndex(b);
        succ[i].removeValue(j + offsetSucc, this);
        pred[j].removeValue(i + offsetPred, this);
    }

    // =========================================================
    // GETTERS FOR INDICES, VARIABLES AND VALUES
    // =========================================================

    // TODO: check everything when enabling compression

    public int getIndexFromSplitGraphIndex(int indSG) {
        return indSG == sink ? source : indSG;
    }

    public int getSplitGraphIndexFromSuccessorsValue(int value) {
        return value - offsetSucc == source ? sink : value - offsetSucc;
    }

    public int getSplitGraphIndexFromPredecessorsValue(int value) {
        return value - offsetPred == source ? sink : value - offsetPred;
    }

    public int getSuccessorsValueFromSplitGraphIndex(int indSG) {
        return indSG == sink ? source + offsetSucc : indSG + offsetSucc;
    }

    public int getPredecessorsValueFromSplitGraphIndex(int indSG) {
        return indSG == sink ? source + offsetPred : indSG + offsetPred;
    }

    public IntVar getSuccessorsVarFromSplitGraphIndex(int index) {
        return index == sink ? null : succ[index];
    }

    public IntVar getPredecessorsVarFromSplitGraphIndex(int index) {
        return index == sink ? null : pred[index];
    }

    // =========================================================
    // SCC STORAGE
    // =========================================================

    private void resetSCCs() {
        numberOfSCCs = 0;
        updateKey++;
    }

    private int newSCC() {
        int id = numberOfSCCs++;
        if (id == 0) {
            sccIndices[id] = 0;
        } else {
            sccIndices[id] = sccIndices[id - 1];
        }
        return id;
    }

    private void addToSCC(int node, int scc) {
        sccPartition[sccIndices[scc]++] = node;
        sccBelonging[node] = scc;
        upToDateSCC[node] = updateKey;
    }

    // =========================================================
    // SCC QUERY
    // =========================================================

    private boolean isInSCC(int node, int scc) {
        return upToDateSCC[node] == updateKey && sccBelonging[node] == scc;
    }

    private boolean isInPreviousSCC(int node, int scc) {
        return upToDateSCC[node] == updateKey && sccBelonging[node] == scc - 1;
    }

    private boolean isInEarlierSCC(int node, int scc) {
        return upToDateSCC[node] == updateKey && sccBelonging[node] < scc - 1;
    }

    private int getStartPositionSCC(int scc) {
        return scc == 0 ? 0 : sccIndices[scc - 1];
    }

    private int getEndPositionSCC(int scc) {
        return sccIndices[scc];
    }

    private int getSizeSCC(int scc) {
        return getEndPositionSCC(scc) - getStartPositionSCC(scc);
    }

    private boolean hasUniqueEntryNode(int scc) {
        return entryNode[scc] >= 0;
    }

    private boolean hasUniqueExitNode(int scc) {
        return exitNode[scc] >= 0;
    }

    // =========================================================
    // ENTAILMENT (not used yet)
    // =========================================================

    @Override
    public org.chocosolver.util.ESat isEntailed() {
        return org.chocosolver.util.ESat.TRUE;
    }
}