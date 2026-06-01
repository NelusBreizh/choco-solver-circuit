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

    public int procedureInstantiation(int i, int j) throws ContradictionException {
        // Subtour detection
        if (!compressedPaths.isTail(i) || !compressedPaths.isHead(j) || compressedPaths.getTail(j) == i) {fails();}
        IEnvironment env = model.getEnvironment();
//        System.out.printf("NoSubtour react on instantiation (%d, %d) \n", i, j);
        compressedPaths.mergePaths(i,j, env);
        // Eliminate the sub-tour arc or enforce it if all vertices are on the same path
        if (compressedPaths.getNumberPaths() > 1) {
//            System.out.printf("NoSubtour filter (%d, %d) \n", compressedPaths.getTail(j), compressedPaths.getHead(i));
            succ[compressedPaths.getTail(j)].removeValue(compressedPaths.getHead(i) + offsetSucc, this);
            // If the new tail is now instantiated we self propagate
            if (succ[compressedPaths.getTail(j)].isInstantiated()) {return compressedPaths.getTail(j);}
        } else {
//            System.out.printf("NoSubtour enforce (%d, %d) \n", compressedPaths.getTail(j), compressedPaths.getHead(i));
            succ[compressedPaths.getTail(j)].instantiateTo(compressedPaths.getHead(i) + offsetSucc, this);
        }
        return -1;
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
                    selfPropagate(i);
                }
            }
        }
    }

    @Override
    public void propagate(int idxVarInProp, int mask) throws ContradictionException {
        if (compressedPaths.isTail(idxVarInProp)) { // If not, this instantiation has already been processed by self propagation
            selfPropagate(idxVarInProp);
        }
    }

    public void selfPropagate(int idxVarInProp) throws ContradictionException {
        if (compressedPaths.getNumberPaths() == 1) {return;} // The cycle has been completed by this propagator OR this instantiation has already been processed internally by self propagation
        int index = idxVarInProp;
        assert succ[index].isInstantiated();
        // Removing the subtour arc may instantiate the tail of the newly formed path, so we may need to self propagate
        while (index != -1) {
            index = procedureInstantiation(index, succ[index].getValue() - offsetSucc);
        }
    }

    @Override
    public int getPropagationConditions(int vIdx) {
        return IntEventType.instantiation();
    }

    @Override
    public ESat isEntailed() {
        for (int i = 0; i < n; i++) {
            if (!succ[i].isInstantiated()) {
                return ESat.UNDEFINED;
            }
        }
        return compressedPaths.getNumberPaths() == 1 ? ESat.TRUE : ESat.FALSE;
    }
}