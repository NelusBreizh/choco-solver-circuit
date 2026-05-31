package org.chocosolver.solver.constraints.nary.circuit;

import org.chocosolver.memory.IEnvironment;
import org.chocosolver.sat.Reason;
import org.chocosolver.solver.constraints.Propagator;
import org.chocosolver.solver.constraints.PropagatorPriority;
import org.chocosolver.solver.exception.ContradictionException;
import org.chocosolver.solver.variables.IntVar;
import org.chocosolver.solver.variables.events.IntEventType;
import org.chocosolver.solver.variables.events.PropagatorEventType;
import org.chocosolver.util.ESat;
import org.chocosolver.util.objects.CompressedPaths;

import static org.chocosolver.util.tools.ArrayUtils.append;

/**
 *
 * This propagator enforces the no sub-tour constraint.
 * If there is an instantiated directed path from i to j that do not contain all vertices, then the arc (j,i) is removed.
 *
 * This propagator uses CompressedPaths to get a compressed representation of instantiated directed path into single nodes.
 *
 * It reacts to instantiations and runs in O(1) time per instantiation, and thus in O(n) time over a whole branch of the search tree.
 *
 * @author Sulian Le Bozec-Chiffoleau
 */
public class New_PropCircuit_NoSubtour_CompressedPaths extends Propagator<IntVar> {

    private final IntVar[] succ;
    private final int n;
    private final int offsetSucc;
    private final CompressedPaths compressedPaths;


    public New_PropCircuit_NoSubtour_CompressedPaths(IntVar[] succ, int offsetSucc) {
        super(succ, PropagatorPriority.UNARY, true);
        this.succ = succ;
        this.n = succ.length;
        this.offsetSucc = offsetSucc;
        this.compressedPaths = new CompressedPaths(n);
    }

    public void procedureInstantiation(int i, int j) throws ContradictionException {
        IEnvironment env = model.getEnvironment();
        compressedPaths.mergePaths(i,j, env);
        // Eliminate the sub-tour arc or enforce it if all vertices are on the same path
        if (compressedPaths.getNumberPaths() > 1) {
            succ[compressedPaths.getTail(j)].removeValue(compressedPaths.getHead(i) + offsetSucc, this);
        } else {
            succ[compressedPaths.getTail(j)].instantiateTo(compressedPaths.getHead(i) + offsetSucc, this);
        }
    }

    @Override
    public void propagate(int evtmask) throws ContradictionException {
        if (PropagatorEventType.isFullPropagation(evtmask)) {
            for (int i = 0; i < n; i++) {
                succ[i].updateLowerBound(offsetSucc, this);
                succ[i].updateUpperBound(n - 1 + offsetSucc, this);
                // Remove loops
                if (n > 1) {succ[i].removeValue(i + offsetSucc, this);}
            }
            for (int i = 0; i < n; i++) {
                if (succ[i].isInstantiated()) {
                    procedureInstantiation(i, succ[i].getValue() - offsetSucc);
                }
            }
        }
    }

    @Override
    public void propagate(int idxVarInProp, int mask) throws ContradictionException {
        procedureInstantiation(idxVarInProp, succ[idxVarInProp].getValue() - offsetSucc);
    }

    @Override
    public int getPropagationConditions(int vIdx) {
        return IntEventType.instantiation();
    }

    @Override
    public ESat isEntailed() {
        if (compressedPaths.getNumberPaths() > 1) {
            return ESat.UNDEFINED;
        }
        else {
            return ESat.TRUE;
        }
    }
}