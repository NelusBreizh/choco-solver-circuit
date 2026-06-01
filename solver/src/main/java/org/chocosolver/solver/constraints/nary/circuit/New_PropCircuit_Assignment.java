package org.chocosolver.solver.constraints.nary.circuit;

import org.chocosolver.solver.constraints.Propagator;
import org.chocosolver.solver.constraints.PropagatorPriority;
import org.chocosolver.solver.exception.ContradictionException;
import org.chocosolver.solver.variables.IntVar;
import org.chocosolver.solver.variables.events.IntEventType;
import org.chocosolver.solver.variables.events.PropagatorEventType;
import org.chocosolver.util.ESat;

import static org.chocosolver.util.tools.ArrayUtils.append;

/**
 *
 * This propagator, ReverseGraph and AllDifferent together enforce generalised arc consistency (or domain consistency) on the following constraint:
 *
 *      succ[i] = j  <=>  pred[j] = i.
 *
 * In particular, this propagator ensures that once a variable is instantiated, its matched variable is also instantiated.
 * With ReverseGraph, they enforce the degree constraint for circuit.
 *
 * It reacts only to instantiations and runs in O(1) time per instantiation, and thus in O(n) time over a whole branch of the search tree.
 *
 * @author Sulian Le Bozec-Chiffoleau
 */
public class New_PropCircuit_Assignment extends Propagator<IntVar> {

    private final IntVar[] succ;
    private final IntVar[] pred;
    private final int n;
    private final int offsetSucc;
    private final int offsetPred;


    public New_PropCircuit_Assignment(IntVar[] succ, int offsetSucc, IntVar[] pred, int offsetPred) {
        super(append(succ, pred), PropagatorPriority.UNARY, true);
        this.succ = succ;
        this.pred = pred;
        this.n = succ.length;
        this.offsetSucc = offsetSucc;
        this.offsetPred = offsetPred;
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
            for (int i = 0; i < n; i++) {
                if (succ[i].isInstantiated()) {
                    pred[succ[i].getValue() - offsetSucc].instantiateTo(i + offsetPred, this);
                }
                if (pred[i].isInstantiated()) {
                    succ[pred[i].getValue() - offsetPred].instantiateTo(i + offsetSucc, this);
                }
            }
        }
    }



    @Override
    public void propagate(int idxVarInProp, int mask) throws ContradictionException {
        assert vars[idxVarInProp].isInstantiated();
        if (idxVarInProp < n) {
//            System.out.printf("Assignment reacts on successor instantiation %d --> %d \n", idxVarInProp, succ[idxVarInProp].getValue() - offsetSucc);
//            System.out.printf("enforces %d <-- %d \n", succ[idxVarInProp].getValue() - offsetSucc, idxVarInProp + offsetPred);
            pred[succ[idxVarInProp].getValue() - offsetSucc].instantiateTo(idxVarInProp + offsetPred, this);
        } else {
//            System.out.printf("Assignment reacts on predecessor instantiation %d <-- %d \n", idxVarInProp - n, pred[idxVarInProp - n].getValue());
//            System.out.printf("enforces %d --> %d \n", pred[idxVarInProp - n].getValue(), idxVarInProp - n);
            succ[pred[idxVarInProp - n].getValue() - offsetPred].instantiateTo(idxVarInProp - n + offsetSucc, this);
        }
    }

    @Override
    public int getPropagationConditions(int vIdx) {
        return IntEventType.instantiation();
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