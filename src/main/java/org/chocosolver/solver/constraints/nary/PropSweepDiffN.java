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
import java.util.Arrays;
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
    private IStateInt[] targetSourceStatus; // 2 = target & source, 1 = source, 0 = neither
    private boolean find;
    private int xFind;
    private int xWit;
    private Random rand;
    private Event[] Qevent;
    private int QeventSize;
    private int[] Pstatus;
    private int size;
    private TIntArrayList list;

    //***********************************************************************************
    // CONSTRUCTOR
    //***********************************************************************************

    public PropSweepDiffN(IntVar[] x, IntVar[] y, IntVar[] dx, IntVar[] dy, boolean fast) {
        super(ArrayUtils.append(x, y, dx, dy), PropagatorPriority.QUADRATIC, false);
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
                throw new SolverException("PropSweepDiffN only accepts instantiated width and height");
            }
        }

        this.witnessesLB = new IStateInt[n];
        this.witnessesUB = new IStateInt[n];
        this.targetSourceStatus = new IStateInt[n];
        for(int i = 0; i<n; i++) {
            witnessesLB[i] = this.getModel().getEnvironment().makeInt(y[i].getLB());
            witnessesUB[i] = this.getModel().getEnvironment().makeInt(y[i].getLB());
            targetSourceStatus[i] = this.getModel().getEnvironment().makeInt(2);
        }

        this.rand = new Random(0);
        Qevent = new Event[2*(n-1)];
        for(int i = 0; i<Qevent.length; i++) {
            Qevent[i] = new Event(true, 0, 0, 0);
        }
        QeventSize = 0;
        list = new TIntArrayList();

        size = Arrays.stream(y).mapToInt(IntVar::getDomainSize).max().getAsInt();
        Pstatus = new int[size];
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
            return IntEventType.boundAndInst();
        }
        return IntEventType.VOID.getMask();
    }

    private boolean prop(int i, boolean lb) throws ContradictionException {
        if(lb) {
            findMinimum(i);
        } else {
            findMaximum(i);
        }

        if(!find) {
            fails();
        }

        if(lb) {
            witnessesLB[i].set(xWit);
            return x[i].updateLowerBound(xFind, this);
        } else {
            witnessesUB[i].set(xWit);
            return x[i].updateUpperBound(xFind, this);
        }
    }

    private boolean doOverlap(int i, int j, boolean hori) {
        int offSet = hori ? 0 : n;
        int S_i = vars[i + offSet].getUB();
        int e_i = vars[i + offSet].getLB() + vars[i + 2 * n + offSet].getLB();
        int S_j = vars[j + offSet].getUB();
        int e_j = vars[j + offSet].getLB() + vars[j + 2 * n + offSet].getLB();
        return (S_i < e_i && e_j > S_i && S_j < e_i)
            || (S_j < e_j && e_i > S_j && S_i < e_j);
    }

    @Override
    public void propagate(int evtmask) throws ContradictionException {
        boolean hasFiltered = true;
        while(hasFiltered) {
            hasFiltered = false;
            for(int i = 0; i<n; i++) {
                if(targetSourceStatus[i].get() == 2) {
                    boolean checkIfInForbiddenRegionsLB = false;
                    boolean checkIfInForbiddenRegionsUB = false;
                    for(int j = 0; j<n && !(checkIfInForbiddenRegionsLB && checkIfInForbiddenRegionsUB); j++) {
                        if(i == j) {
                            continue;
                        }
//                        int rx_m = x[j].getUB()-dx[i].getLB()+1;
//                        int rx_p = x[j].getLB()+dx[j].getLB()-1;
//                        int ry_m = y[j].getUB()-dy[i].getLB()+1;
//                        int ry_p = y[j].getLB()+dy[j].getLB()-1;
//                        System.out.println((x[i].getName().contains("x") ? "X" : "Y")+"-check : R["+i+":"+j+"] = ("+rx_m+".."+rx_p+","+ry_m+".."+ry_p+")");
                        checkIfInForbiddenRegionsLB |= checkIfInForbiddenRegions(i, j, x[i].getLB(), witnessesLB[i].get());
                        checkIfInForbiddenRegionsUB |= checkIfInForbiddenRegions(i, j, x[i].getUB(), witnessesUB[i].get());
                    }
                    if(checkIfInForbiddenRegionsLB) {
//                        System.out.println(x[i]+":LB");
                        hasFiltered |= prop(i, true);
                    }
                    if(checkIfInForbiddenRegionsUB) {
//                        System.out.println(x[i]+":UB");
                        hasFiltered |= prop(i, false);
                    }
                }
                if(boxInstantiated(i)) {
                    for(int j = i+1; j<n; j++) {
                        if(j != i && boxInstantiated(j) && doOverlap(i, j, true) && doOverlap(i, j, false)) {
                            fails();
                        }
                    }
                    this.targetSourceStatus[i].set(1);
                }
            }
            updateSourceStatus();
        }
    }

    private boolean disjoint(int i, int B_x_m, int B_x_p, int B_y_m, int B_y_p) {
        int x_m = x[i].getLB();
        int x_p = x[i].getUB() + dx[i].getLB() - 1;
        int y_m = y[i].getLB();
        int y_p = y[i].getUB() + dy[i].getLB() -1;

        return B_x_m > x_p || B_x_p < x_m || B_y_m > y_p || B_y_p < y_m;
    }

    private void updateSourceStatus() {
        int B_x_m = Integer.MAX_VALUE;
        int B_x_p = -Integer.MAX_VALUE;
        int B_y_m = Integer.MAX_VALUE;
        int B_y_p = -Integer.MAX_VALUE;
        for(int i = 0; i<n; i++) {
            if(targetSourceStatus[i].get() == 2) {
                B_x_m = Math.min(B_x_m, x[i].getLB());
                B_x_p = Math.max(B_x_p, x[i].getUB() + dx[i].getLB() - 1);
                B_y_m = Math.min(B_y_m, y[i].getLB());
                B_y_p = Math.max(B_y_p, y[i].getUB() + dy[i].getLB() - 1);
            }
        }
        for(int i = 0; i<n; i++) {
            if(targetSourceStatus[i].get() == 1 && disjoint(i, B_x_m, B_x_p, B_y_m, B_y_p)) {
                targetSourceStatus[i].set(0);
            }
        }
    }

    private boolean isValidForbiddenRegion(int i, int j) {
        int rx_m = x[j].getUB()-dx[i].getLB()+1;
        int rx_p = x[j].getLB()+dx[j].getLB()-1;
        int ry_m = y[j].getUB()-dy[i].getLB()+1;
        int ry_p = y[j].getLB()+dy[j].getLB()-1;
//        System.out.println("R["+i+":"+j+"] = ("+rx_m+".."+rx_p+","+ry_m+".."+ry_p+")");

        return rx_m <= rx_p && ry_m <= ry_p;
    }

    private boolean checkIfInForbiddenRegions(int i, int j, int vx, int vy) {
        int rx_m = x[j].getUB()-dx[i].getLB()+1;
        int rx_p = x[j].getLB()+dx[j].getLB()-1;
        int ry_m = y[j].getUB()-dy[i].getLB()+1;
        int ry_p = y[j].getLB()+dy[j].getLB()-1;

        return rx_m <= vx && vx <= rx_p && ry_m <= vy && vy <= ry_p;
    }

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
        size = y[i].getUB()-y[i].getLB()+1;
        for(int k = 0; k<size; k++) {
            if(!y[i].contains(y[i].getLB()+k)) {
                Pstatus[k] = 1;
            } else {
                Pstatus[k] = 0;
            }
        }
    }

    private static void updateEvent(Event event, boolean start, int pos, int i, int j) {
        event.start = start;
        event.pos = pos;
        event.i = i;
        event.j = j;
    }

    private void findMinimum(int i) {
        QeventSize = 0;
        for(int j = 0; j<n; j++) {
            if(j != i && targetSourceStatus[j].get() >= 1) {
                if(isValidForbiddenRegion(i, j)) {
                    updateEvent(Qevent[QeventSize++], true, Math.max(x[j].getUB() - dx[i].getLB() + 1, x[i].getLB()), i, j);
                    if(x[j].getLB()+dx[j].getLB() <= x[i].getUB()) {
                        updateEvent(Qevent[QeventSize++], false, x[j].getLB() + dx[j].getLB(), i, j);
                    }
                }
            }
        }
        Arrays.sort(Qevent, 0, QeventSize);
        if(QeventSize == 0 || Qevent[0].pos > x[i].getLB()) {
            xFind = x[i].getLB();
            xWit = getRandValue(y[i]);
            find = true;
        } else {
            buildPStatus(i);
            int idx = 0;
            while(idx < QeventSize) {
                int delta = Qevent[idx].pos;
                while(idx < QeventSize && Qevent[idx].pos == delta) {
                    handleEvent(Qevent[idx++]);
                }
                list.clear();
                for(int k = 0; k<size; k++) {
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
        QeventSize = 0;
        for(int j = 0; j<n; j++) {
            if(j != i && targetSourceStatus[j].get() >= 1) {
                if(isValidForbiddenRegion(i, j)) {
                    updateEvent(Qevent[QeventSize++], true, Math.min(x[j].getLB() + dx[j].getLB() - 1, x[i].getUB()), i, j);
                    if(x[j].getUB()-dx[i].getLB() >= x[i].getLB()) {
                        updateEvent(Qevent[QeventSize++], false, x[j].getUB()-dx[i].getLB(), i, j);
                    }
                }
            }
        }
        Arrays.sort(Qevent, 0, QeventSize);
        if(QeventSize == 0 || Qevent[QeventSize-1].pos < x[i].getUB()) {
            xFind = x[i].getUB();
            xWit = getRandValue(y[i]);
            find = true;
        } else {
            buildPStatus(i);
            int idx = QeventSize-1;
            while(idx >= 0) {
                int delta = Qevent[idx].pos;
                while(idx >= 0 && Qevent[idx].pos == delta) {
                    handleEvent(Qevent[idx--]);
                }
                list.clear();
                for(int k = 0; k<size; k++) {
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
        for(int k = l; k<=u; k++) {
            Pstatus[k-y[i].getLB()] += (event.start ? 1 : -1);
        }
    }

    //***********************************************************************************
    // EVENT
    //***********************************************************************************

    private static class Event implements Comparable<Event> {
        public boolean start;
        public int pos;
        public int i;
        public int j;

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

        @Override
        public int compareTo(Event o) {
            return Integer.compare(this.pos, o.pos);
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
