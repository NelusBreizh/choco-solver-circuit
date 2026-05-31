package org.chocosolver.solver.constraints.nary.circuit;

import org.chocosolver.solver.constraints.Propagator;
import org.chocosolver.solver.constraints.PropagatorPriority;
import org.chocosolver.solver.exception.ContradictionException;
import org.chocosolver.solver.variables.IntVar;
import org.chocosolver.solver.variables.delta.IIntDeltaMonitor;
import org.chocosolver.solver.variables.events.IntEventType;
import org.chocosolver.solver.variables.events.PropagatorEventType;
import org.chocosolver.util.ESat;
import org.chocosolver.util.procedure.IntProcedure;

import static org.chocosolver.util.tools.ArrayUtils.append;

/**
 * This propagator, Assignment and AllDifferent together enforce generalised arc consistency (or domain consistency) on the following constraint:
 *
 *      succ[i] = j  <=>  pred[j] = i.
 *
 * In particular, this propagator ensures the graph derived from pred is the reverse graph of the graph derived from succ.
 * With Assignment, they enforce the degree constraint for circuit.
 *
 * It reacts only to value removals and runs in O(1) time per value removal, and thus in O(n^2) time over a whole branch of the search tree.
 *
 * @Disclaimer The code can be messy because of potential offsets.
 *
 * @author Sulian Le Bozec-Chiffoleau
 */
public class New_PropCircuit_ReverseGraph extends Propagator<IntVar> {

    private final IntVar[] succ;
    private final IntVar[] pred;
    private final int n;
    private final int offsetSucc;
    private final int offsetPred;

    private final IIntDeltaMonitor[] idmSucc;
    private final IIntDeltaMonitor[] idmPred;
    private final IntProcedure procSucc;
    private final IntProcedure procPred;
    private int varIdx;


    public New_PropCircuit_ReverseGraph(IntVar[] succ, int offsetSucc, IntVar[] pred, int offsetPred) {
        super(append(succ, pred), PropagatorPriority.UNARY, true);
        this.succ = succ;
        this.pred = pred;
        this.n = succ.length;
        this.offsetSucc = offsetSucc;
        this.offsetPred = offsetPred;
        this.idmSucc = new IIntDeltaMonitor[n];
        this.idmPred = new IIntDeltaMonitor[n];
        for (int i = 0; i < n; i++) {
            idmSucc[i] = succ[i].monitorDelta(this);
            idmPred[i] = pred[i].monitorDelta(this);
        }
        this.procSucc = val -> {
            pred[val - offsetSucc].removeValue(varIdx + offsetPred, this);
        };
        this.procPred = val -> {
            succ[val - offsetPred].removeValue(varIdx + offsetSucc, this);
        };
    }

    @Override
    public void propagate(int evtmask) throws ContradictionException {
        if (PropagatorEventType.isFullPropagation(evtmask)) {
            for (int i = 0; i < n; i++) {
                succ[i].updateLowerBound(offsetSucc, this);
                succ[i].updateUpperBound(n - 1 + offsetSucc, this);
                pred[i].updateLowerBound(offsetPred, this);
                pred[i].updateUpperBound(n - 1 + offsetPred, this);
            }
            // i -> j can remain in the original graph only if j -> i exists in the reverse graph
            removeFromLeftAllUnsymmetricalValues(succ, offsetSucc, pred, offsetPred);
            // i -> j can remain in the reverse graph only if j -> i exists in the original graph
            removeFromLeftAllUnsymmetricalValues(pred, offsetPred, succ, offsetSucc);
        }
        for (int i = 0; i < n; i++) {
            idmSucc[i].startMonitoring();
            idmPred[i].startMonitoring();
        }
    }

    private void removeFromLeftAllUnsymmetricalValues(IntVar[] left, int offsetLeft, IntVar[] right, int offsetRight) throws ContradictionException {
        int i; // The index of a variable from left
        int j; // The index of a variable from right
        for (i = 0; i < n; i++) {
            IntVar var_left  = left[i]; // The actual variable from left
            int val_left_right; // A value from left that represent a variable from right
            int ub = var_left.getUB();
            for (val_left_right = var_left.getLB(); val_left_right <= ub; val_left_right = var_left.nextValue(val_left_right)) {
                j = val_left_right - offsetLeft; // The index of the variable from right
                IntVar var_right = right[j]; // The actual variable from right
                int val_right_left = i + offsetRight; // A value from right that represent a variable from left
                if (!var_right.contains(val_right_left)) {
                    var_left.removeValue(val_left_right, this);
                }
            }
        }
    }

    @Override
    public void propagate(int idxVarInProp, int mask) throws ContradictionException {
        if (idxVarInProp < n) {
            varIdx = idxVarInProp;
            idmSucc[varIdx].forEachRemVal(procSucc);
        } else {
            varIdx = idxVarInProp - n;
            idmPred[varIdx].forEachRemVal(procPred);
        }
    }

    @Override
    public int getPropagationConditions(int vIdx) {
        return IntEventType.all();
    }

    @Override
    public ESat isEntailed() {
        for (int i = 0; i < n; i++) {
            if (!succ[i].isInstantiated() || !pred[i].isInstantiated()) {
                return ESat.UNDEFINED;
            }
        }
        for (int i = 0; i < n; i++) {
            if (pred[succ[i].getValue() - offsetSucc].getValue() - offsetPred != i) {
                return ESat.FALSE;
            }
        }
        return ESat.TRUE;
    }
}