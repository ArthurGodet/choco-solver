/*
 * This file is part of choco-solver, http://choco-solver.org/
 *
 * Copyright (c) 2019, IMT Atlantique. All rights reserved.
 *
 * Licensed under the BSD 4-clause license.
 *
 * See LICENSE file in the project root for full license information.
 */
package org.chocosolver.solver.constraints.nary;

import gnu.trove.list.array.TIntArrayList;
import java.util.Comparator;
import java.util.LinkedList;
import java.util.Random;
import org.chocosolver.memory.IStateInt;
import org.chocosolver.solver.constraints.Propagator;
import org.chocosolver.solver.constraints.PropagatorPriority;
import org.chocosolver.solver.exception.ContradictionException;
import org.chocosolver.solver.exception.SolverException;
import org.chocosolver.solver.variables.IntVar;
import org.chocosolver.solver.variables.events.IntEventType;
import org.chocosolver.util.ESat;
import org.chocosolver.util.tools.ArrayUtils;

/**
 @author Arthur Godet <arth.godet@gmail.com>
 @since 14/10/2019
 */
public class PropSweepDiffN extends Propagator<IntVar> {

    //***********************************************************************************
    // VARIABLES
    //***********************************************************************************

    private int n;
    private IntVar[] x;
    private IntVar[] y;
    private IntVar[] dx;
    private IntVar[] dy;

    private boolean fast;

    private IStateInt[] witnessesLB; // TODO : may not be necessary to be trailed
    private IStateInt[] witnessesUB; // TODO : may not be necessary to be trailed
    private boolean find;
    private int xFind;
    private int xWit;
    private Random rand;
    private LinkedList<Event> Qevent;
    private int[] Pstatus;
    private TIntArrayList list;

    //***********************************************************************************
    // CONSTRUCTOR
    //***********************************************************************************

    public PropSweepDiffN(IntVar[] x, IntVar[] y, IntVar[] dx, IntVar[] dy, boolean fast) {
        super(ArrayUtils.append(x, y, dx, dy), PropagatorPriority.LINEAR, false);
        this.fast = fast;
        n = x.length;
        this.x = x;
        this.y = y;
        this.dx = dx;
        this.dy = dy;
        if (!(n == y.length && n == dx.length && n == dy.length)) {
            throw new SolverException("PropDiffN variable arrays do not have same size");
        }
        for(int i = 0; i<n; i++) { // TODO : temporary
            if(!dx[i].isInstantiated() || !dy[i].isInstantiated()) {
                throw new SolverException("PropagDiffN only accepts instantiated width and height");
            }
        }

        this.witnessesLB = new IStateInt[n];
        this.witnessesUB = new IStateInt[n];
        for(int i = 0; i<n; i++) {
            witnessesLB[i] = this.getModel().getEnvironment().makeInt(y[i].getLB());
            witnessesUB[i] = this.getModel().getEnvironment().makeInt(y[i].getLB());
        }

        this.rand = new Random(0);
        Qevent = new LinkedList<>();
        list = new TIntArrayList();
    }

    //***********************************************************************************
    // PROPAGATE METHODS
    //***********************************************************************************

    @Override
    public int getPropagationConditions(int idx) {
        if(idx < n) {
            if (fast) {
                return IntEventType.instantiation();
            }
            return IntEventType.combine(IntEventType.INCLOW, IntEventType.INSTANTIATE);
        }
        return IntEventType.VOID.getMask();
    }

    private void prop(int i, boolean lb) throws ContradictionException {
        boolean checkIfInForbiddenRegions = false;
        int value = (lb ? x[i].getLB() : x[i].getUB());
        int witness = (lb ? witnessesLB[i].get() : witnessesUB[i].get());
        for(int j = 0; j<n && !checkIfInForbiddenRegions; j++) {
            checkIfInForbiddenRegions = checkIfInForbiddenRegions(i, j, value, witness);
        }
        if(checkIfInForbiddenRegions) {
            if(lb) {
                findMinimum(i);
            } else {
                findMaximum(i);
            }
            if(!find) {
                fails();
            } else {
                if(lb) {
                    witnessesLB[i].set(xWit);
                    x[i].updateLowerBound(xFind, this);
                } else {
                    witnessesUB[i].set(xWit);
                    x[i].updateUpperBound(xFind, this);
                }
            }
        }
    }

    @Override
    public void propagate(int evtmask) throws ContradictionException {
        for(int i = 0; i<n; i++) {
            if(!x[i].isInstantiated()) {
                prop(i, true);
                prop(i, false);
            }
        }
        if(isCompletelyInstantiated()) { // TODO : should not be useful ! We need to understand why is it not ok --> because of the if on x[i].isInstantiated()
            if(isEntailed().equals(ESat.FALSE)) {
                fails();
            }
        }
    }

    private boolean getForbiddenRegion(int i, int j, int xPrime, boolean down) {
        int rx_m = x[j].getUB()-dx[i].getLB()+1;
        int rx_p = x[j].getLB()+dx[j].getLB()-1;
        int ry_m = y[j].getUB()-dy[i].getLB()+1;
        int ry_p = y[j].getLB()+dy[j].getLB()-1;
        boolean test = (down ? xPrime < x[i].getLB() : xPrime > x[i].getUB());

        return test && rx_m <= rx_p && ry_m <= ry_p;
    }

    private boolean checkIfInForbiddenRegions(int i, int j, int vx, int vy) {
        int rx_m = x[j].getUB()-dx[i].getLB()+1;
        int rx_p = x[j].getLB()+dx[j].getLB()-1;
        int ry_m = y[j].getUB()-dy[i].getLB()+1;
        int ry_p = y[j].getLB()+dy[j].getLB()-1;

        return rx_m <= vx && vx <= rx_p && ry_m <= vy && vy <= ry_p;
    }

    // TODO : et finir de débugger ce propagateur pour que tout fonctionne correctement
    // TODO : COMPRENDRE POURQUOI LE SWEEP FILTRE MOINS BIEN QUE L'EXISTANT ALORS QUE JACOP LAISSE SUPPOSER LE CONTRAIRE

    private int getRandValue(IntVar y) {
        int idx = rand.nextInt(y.getDomainSize());
        int value = y.getLB();
        int i = 0;
        while(i<idx) {
            value = y.nextValue(value);
            i++;
        }
        return value;
    }

    private void buildPStatus(int i) {
        Pstatus = new int[y[i].getUB()-y[i].getLB()+1];
        for(int k = 0; k<Pstatus.length; k++) {
            if(!y[i].contains(y[i].getLB()+k)) {
                Pstatus[k]++;
            }
        }
    }

    private void findMinimum(int i) {
        Qevent.clear();
        for(int j = 0; j<n; j++) {
            if(j != i) {
                if(getForbiddenRegion(i, j, x[i].getLB()-1, true)) {
                    Qevent.add(new Event(true, Math.max(x[j].getUB() - dx[i].getLB() + 1, x[i].getLB()), i, j));
                    if(x[j].getLB()+dx[j].getLB() <= x[i].getUB()) {
                        Qevent.add(new Event(false, x[j].getLB() + dx[j].getLB(), i, j));
                    }
                }
            }
        }
        Qevent.sort(Comparator.comparingInt(e -> e.pos));
        if(Qevent.isEmpty() || Qevent.getFirst().pos > x[i].getLB()) {
            xFind = x[i].getLB();
            xWit = getRandValue(y[i]);
            find = true;
        } else {
            buildPStatus(i);
            while(!Qevent.isEmpty()) {
                int delta = Qevent.getFirst().pos;
                while(!Qevent.isEmpty() && Qevent.getFirst().pos == delta) {
                    handleEvent(Qevent.removeFirst());
                }
                list.clear();
                for(int k = 0; k<Pstatus.length; k++) {
                    if(Pstatus[k] == 0) {
                        list.add(y[i].getLB()+k);
                    }
                }
                if(!list.isEmpty()) {
                    find = true;
                    xFind = delta;
                    xWit = list.getQuick(rand.nextInt(list.size()));
                    return;
                }
            }

            find = false;
            xFind = 0;
            xWit = 0;
        }
    }

    private void findMaximum(int i) {
        Qevent.clear();
        for(int j = 0; j<n; j++) {
            if(j != i) {
                if(getForbiddenRegion(i, j, x[i].getUB()+1, false)) {
                    Qevent.add(new Event(true, Math.min(x[j].getLB() + dx[j].getLB() - 1, x[i].getUB()), i, j));
                    if(x[j].getUB()-dx[i].getLB() >= x[i].getLB()) {
                        Qevent.add(new Event(false, x[j].getUB()-dx[i].getLB(), i, j));
                    }
                }
            }
        }
        Qevent.sort(Comparator.comparingInt(e -> e.pos));
        if(Qevent.isEmpty() || Qevent.getLast().pos < x[i].getUB()) {
            xFind = x[i].getUB();
            xWit = getRandValue(y[i]);
            find = true;
        } else {
            buildPStatus(i);
            while(!Qevent.isEmpty()) {
                int delta = Qevent.getLast().pos;
                while(!Qevent.isEmpty() && Qevent.getLast().pos == delta) {
                    handleEvent(Qevent.removeLast());
                }
                list.clear();
                for(int k = 0; k<Pstatus.length; k++) {
                    if(Pstatus[k] == 0) {
                        list.add(y[i].getLB()+k);
                    }
                }
                if(!list.isEmpty()) {
                    find = true;
                    xFind = delta;
                    xWit = list.getQuick(rand.nextInt(list.size()));
                    return;
                }
            }

            find = false;
            xFind = 0;
            xWit = 0;
        }
    }

    private void handleEvent(Event event) {
        int i = event.i;
        int j = event.j;
        int l = Math.max(y[j].getUB()-dy[i].getLB()+1, y[i].getLB());
        int u = Math.min(y[j].getLB()+dy[j].getLB()-1, y[i].getUB());
        if(event.start) {
            for(int k = l; k<=u; k++) {
                Pstatus[k-y[i].getLB()]++;
            }
        } else {
            for(int k = l; k<=u; k++) {
                Pstatus[k-y[i].getLB()]--;
            }
        }
    }

    //***********************************************************************************
    // EVENT
    //***********************************************************************************

    private static class Event {
        public final boolean start;
        public final int pos;
        public final int i;
        public final int j;

        Event(boolean start, int pos, int i, int j) {
            this.start = start;
            this.pos = pos;
            this.i = i;
            this.j = j;
        }

        @Override
        public String toString() {
            return "Event("+start+","+pos+","+i+","+j+")";
        }
    }

    //***********************************************************************************
    // EXISTENT METHODS
    //***********************************************************************************

    private boolean boxInstantiated(int i) {
        return x[i].isInstantiated() && y[i].isInstantiated()
            && dx[i].isInstantiated() && dy[i].isInstantiated();
    }

    private boolean mayOverlap(int i, int j) {
        return isNotDisjoint(i, j, true) && isNotDisjoint(i, j, false);
    }

    private boolean isNotDisjoint(int i, int j, boolean horizontal) {
        if(horizontal) {
            return (x[i].getLB() < x[j].getUB() + dx[j].getUB()) && (x[j].getLB() < x[i].getUB() + dx[i].getUB());
        } else {
            return (y[i].getLB() < y[j].getUB() + dy[j].getUB()) && (y[j].getLB() < y[i].getUB() + dy[i].getUB());
        }
    }

    @Override
    public ESat isEntailed() {
        for (int i = 0; i < n; i++) {
            if (boxInstantiated(i))
                for (int j = i + 1; j < n; j++) {
                    if (boxInstantiated(j)) {
                        if (mayOverlap(i, j)) {
                            return ESat.FALSE;
                        }
                    }
                }
        }
        if (isCompletelyInstantiated()) {
            return ESat.TRUE;
        }
        return ESat.UNDEFINED;
    }

    //***********************************************************************************
    // TO STRING
    //***********************************************************************************

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder("DIFFN(");
        for (int i = 0; i < n; i++) {
            if (i > 0) {
                sb.append(",");
            }
            sb.append("[").append(vars[i].toString());
            sb.append(",").append(vars[i + n].toString());
            sb.append(",").append(vars[i + 2 * n].toString());
            sb.append(",").append(vars[i + 3 * n].toString()).append("]");
        }
        sb.append(")");
        return sb.toString();
    }
}
